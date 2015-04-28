package cuckoo

import (
	"bytes"
	"encoding/binary"
	"encoding/gob"
	"errors"
	"hash"
	"hash/fnv"
	"io"
	"io/ioutil"
	"math"
	"math/rand"
	"os"
)

type Filter struct {
	Bbuckets []bucket
	M        uint // number of buckets
	B        uint // number of entries per bucket
	F        uint // length of fingerprints (in bytes)
	Ccount   uint // number of items in the filter
	N        uint // filter capacity
}

// maxNumKicks is the maximum number of relocations to attempt when inserting
// an element before considering the filter full.
const maxNumKicks = 500

// bucket consists of a set of []byte entries.
type bucket [][]byte

// contains indicates if the given fingerprint is contained in one of the
// bucket's entries.
func (b bucket) contains(f []byte) bool {
	return b.indexOf(f) != -1
}

// indexOf returns the entry index of the given fingerprint or -1 if it's not
// in the bucket.
func (b bucket) indexOf(f []byte) int {
	for i, fingerprint := range b {
		if bytes.Equal(f, fingerprint) {
			return i
		}
	}
	return -1
}

// getEmptyEntry returns the index of the next available entry in the bucket or
// an error if it's full.
func (b bucket) getEmptyEntry() (int, error) {
	for i, fingerprint := range b {
		if fingerprint == nil {
			return i, nil
		}
	}
	return -1, errors.New("full")
}

func LoadCuckooFilter(p string) (*CuckooFilter, error) {
	var data = new(bytes.Buffer)

	f, err := os.Open(p)

	if err != nil {
		return nil, err
	}

	if _, err := io.Copy(data, f); err != nil {
		return nil, err
	}

	f.Close()

	dec := gob.NewDecoder(data)

	var v Filter

	err = dec.Decode(&v)

	if err != nil {
		return nil, err
	}

	return &CuckooFilter{
		Bbuckets: v.Bbuckets,
		Hash:     fnv.New32(),
		M:        v.M,
		B:        v.B,
		F:        v.F,
		N:        v.N,
	}, nil
}

func (c *CuckooFilter) Write(p string) error {
	bf := Filter{
		Bbuckets: c.Bbuckets,
		M:        c.M,
		B:        c.B,
		F:        c.F,
		Ccount:   c.Ccount,
		N:        c.N,
	}

	var data = new(bytes.Buffer)

	enc := gob.NewEncoder(data)

	if err := enc.Encode(bf); err != nil {
		return err
	}

	if err := ioutil.WriteFile(p, data.Bytes(), 0644); err != nil {
		return err
	}

	return nil
}

// CuckooFilter implements a Cuckoo Bloom filter as described by Andersen,
// Kaminsky, and Mitzenmacher in Cuckoo Filter: Practically Better Than Bloom:
//
// http://www.pdl.cmu.edu/PDL-FTP/FS/cuckoo-conext2014.pdf
//
// A Cuckoo Filter is a Bloom filter variation which provides support for
// removing elements without significantly degrading space and performance. It
// works by using a cuckoo hashing scheme for inserting items. Instead of
// storing the elements themselves, it stores their fingerprints which also
// allows for item removal without false negatives (if you don't attempt to
// remove an item not contained in the filter).
//
// For applications that store many items and target moderately low
// false-positive rates, cuckoo filters have lower space overhead than
// space-optimized Bloom filters.
type CuckooFilter struct {
	Bbuckets []bucket
	M        uint        // number of buckets
	B        uint        // number of entries per bucket
	F        uint        // length of fingerprints (in bytes)
	Ccount   uint        // number of items in the filter
	N        uint        // filter capacity
	Hash     hash.Hash32 // hash function (used for fingerprint and hash)
}

// NewCuckooFilter creates a new Cuckoo Bloom filter optimized to store n items
// with a specified target false-positive rate.
func NewCuckooFilter(n uint, fpRate float64) *CuckooFilter {
	var (
		b       = uint(4)
		f       = calculateF(b, fpRate)
		m       = power2(n / uint(f) * 8)
		buckets = make([]bucket, m)
	)

	for i := uint(0); i < m; i++ {
		buckets[i] = make(bucket, b)
	}

	return &CuckooFilter{
		Bbuckets: buckets,
		Hash:     fnv.New32(),
		M:        m,
		B:        b,
		F:        uint(f),
		N:        n,
	}
}

// Buckets returns the number of buckets.
func (c *CuckooFilter) Buckets() uint {
	return c.M
}

// Capacity returns the number of items the filter can store.
func (c *CuckooFilter) Capacity() uint {
	return c.N
}

// Count returns the number of items in the filter.
func (c *CuckooFilter) Count() uint {
	return c.Ccount
}

// Test will test for membership of the data and returns true if it is a
// member, false if not. This is a probabilistic test, meaning there is a
// non-zero probability of false positives.
func (c *CuckooFilter) Test(data []byte) bool {
	i1, i2, f := c.components(data)

	// If either bucket contains f, it's a member.
	return c.Bbuckets[i1%c.M].contains(f) || c.Bbuckets[i2%c.M].contains(f)
}

// Add will add the data to the Cuckoo Filter. It returns an error if the
// filter is full. If the filter is full, an item is removed to make room for
// the new item. This introduces a possibility for false negatives. To avoid
// this, use Count and Capacity to check if the filter is full before adding an
// item.
func (c *CuckooFilter) Add(data []byte) error {
	return c.add(c.components(data))
}

// TestAndAdd is equivalent to calling Test followed by Add. It returns true if
// the data is a member, false if not. An error is returned if the filter is
// full. If the filter is full, an item is removed to make room for the new
// item. This introduces a possibility for false negatives. To avoid this, use
// Count and Capacity to check if the filter is full before adding an item.
func (c *CuckooFilter) TestAndAdd(data []byte) (bool, error) {
	i1, i2, f := c.components(data)

	// If either bucket contains f, it's a member.
	if c.Bbuckets[i1%c.M].contains(f) || c.Bbuckets[i2%c.M].contains(f) {
		return true, nil
	}

	return false, c.add(i1, i2, f)
}

// TestAndRemove will test for membership of the data and remove it from the
// filter if it exists. Returns true if the data was a member, false if not.
func (c *CuckooFilter) TestAndRemove(data []byte) bool {
	i1, i2, f := c.components(data)

	// Try to remove from bucket[i1].
	b1 := c.Bbuckets[i1%c.M]
	if idx := b1.indexOf(f); idx != -1 {
		b1[idx] = nil
		c.Ccount--
		return true
	}

	// Try to remove from bucket[i2].
	b2 := c.Bbuckets[i2%c.M]
	if idx := b2.indexOf(f); idx != -1 {
		b2[idx] = nil
		c.Ccount--
		return true
	}

	return false
}

// Reset restores the Bloom filter to its original state. It returns the filter
// to allow for chaining.
func (c *CuckooFilter) Reset() *CuckooFilter {
	buckets := make([]bucket, c.M)
	for i := uint(0); i < c.M; i++ {
		buckets[i] = make(bucket, c.B)
	}
	c.Bbuckets = buckets
	c.Ccount = 0
	return c
}

// add will insert the fingerprint into the filter returning an error if the
// filter is full.
func (c *CuckooFilter) add(i1, i2 uint, f []byte) error {
	// Try to insert into bucket[i1].
	b1 := c.Bbuckets[i1%c.M]
	if idx, err := b1.getEmptyEntry(); err == nil {
		b1[idx] = f
		c.Ccount++
		return nil
	}

	// Try to insert into bucket[i2].
	b2 := c.Bbuckets[i2%c.M]
	if idx, err := b2.getEmptyEntry(); err == nil {
		b2[idx] = f
		c.Ccount++
		return nil
	}

	// Must relocate existing items.
	i := i1
	for n := 0; n < maxNumKicks; n++ {
		bucketIdx := i % c.M
		entryIdx := rand.Intn(int(c.B))
		f, c.Bbuckets[bucketIdx][entryIdx] = c.Bbuckets[bucketIdx][entryIdx], f
		i = i ^ uint(binary.BigEndian.Uint32(c.computeHash(f)))
		b := c.Bbuckets[i%c.M]
		if idx, err := b.getEmptyEntry(); err == nil {
			b[idx] = f
			c.Ccount++
			return nil
		}
	}

	return errors.New("full")
}

// components returns the two hash values used to index into the buckets and
// the fingerprint for the given element.
func (c *CuckooFilter) components(data []byte) (uint, uint, []byte) {
	var (
		hash = c.computeHash(data)
		f    = hash[0:c.F]
		i1   = uint(binary.BigEndian.Uint32(hash))
		i2   = i1 ^ uint(binary.BigEndian.Uint32(c.computeHash(f)))
	)

	return i1, i2, f
}

// computeHash returns a 32-bit hash value for the given data.
func (c *CuckooFilter) computeHash(data []byte) []byte {
	c.Hash.Write(data)
	hash := c.Hash.Sum(nil)
	c.Hash.Reset()
	return hash
}

// SetHash sets the hashing function used in the filter.
// For the effect on false positive rates see: https://github.com/tylertreat/BoomFilters/pull/1
func (c *CuckooFilter) SetHash(h hash.Hash32) {
	c.Hash = h
}

// calculateF returns the optimal fingerprint length in bytes for the given
// bucket size and false-positive rate epsilon.
func calculateF(b uint, epsilon float64) uint {
	f := uint(math.Ceil(math.Log(2 * float64(b) / epsilon)))
	f = f / 8
	if f <= 0 {
		f = 1
	}
	return f
}

// power2 calculates the next power of two for the given value.
func power2(x uint) uint {
	x--
	x |= x >> 1
	x |= x >> 2
	x |= x >> 4
	x |= x >> 8
	x |= x >> 16
	x |= x >> 32
	x++
	return x
}
