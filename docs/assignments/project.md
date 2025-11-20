---
order: -1
icon: code
date: 2025-11-19 08:00:00 -5
---

# Final project

Instead of doing [Assignment 4](./hw4), you can pick something open-ended to work on. You need to talk to me ahead of time to do this.

The idea here is for you to explore something you're interested in and complete a more substantial proof. Whatever you work on you need to write a short, 1-2 page proposal explaining what you're planning to do, and/or present the idea to me, so I can give feedback (mainly so I can confirm the scope is reasonable and that you have some intermediate goals).

The project will include a (short) written report on what you did. If you don't finish the proofs, that's okay - it's still important that you communicate what you did and what challenges you ran into. The report should be about 2--5 pages explaining what problem you tackled and what progress you made. You will submit your code, but the report is what I will start with to make sense of what you did so spend some time making that clear.

## "Easy" projects

These are projects that I believe are doable, except that I haven't done them myself.

### Verify pdqsort

The standard library's basic sorting algorithm is "pdqsort" - pattern-defeating quicksort. Verify it.

### Make Memoize more useful

Memoization is mostly useful when memoizing a recursive function and caching its recursive subcalls. The interface of the example in the [Persistence lecture](/notes/persistently.md) does not allow this - there is a circularity where the function is required to create a `Memoize`, but we want to call the `Memoize` in recursive calls.

Re-implement memoization to solve this problem. See these [lecture notes](https://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec22-memoization/memo.htm) (specifically the last section, "Automatic Memoization Using Higher Order Functions") for how this works. Implement a memoized fibonacci function and verify it using the new specification.

## "Medium" projects

These are projects that you might not finish, and which require you to figure out the scope.

### Verify a range map data structure

Verify a data structure that can efficiently map a (potentially large) range of keys to a single value. Example use cases include processing a firewall configuration, where the keys would be IP addresses and rules apply to whole IP address ranges, or for efficiently filtering based on `.gitignore` rules.

You can simplify the implementation by only supporting integer keys. A more sophisticated implementation would support strings; Goose does not (currently) support string comparison with `s1 < s2`, so you would need to implement this yourself.

This requires some data structure design. A starting point would be to maintain a list of sorted ranges that you search with binary search.

### Verify a buddy allocator

Verify a memory allocator, using the [buddy allocator algorithm](https://www.geeksforgeeks.org/buddy-system-memory-allocation-technique/). The Go implementation should keep a large byte slice as the backing storage, and return a struct on allocation with both the data and any metadata required by the algorithm (this is a simplification since working with the pointers alone is difficult in Go).

### Verify the Cloudflare trie-hard data structure

Port [trie-hard](https://github.com/cloudflare/trie-hard) to Go and verify it. Specialize that implementation to u64.

This is a trie (an efficient prefix-search data structure, especially for a fixed set of search strings), but with the twist of encoding the pointers into the bits of an integer for space efficiency (without this Cloudflare found it wasn't faster than a Rust `HashMap`).

## Open-ended projects

These projects are more open ended.

### Make Goose easier to use

Did you find something difficult while doing the previous assignments? It's an open project option to fix a pain point you experienced. This could involve primarily writing documentation, but it would need to be substantial and involve code examples.

This is open-ended but need not require any challenging proofs.

### Verify the Go sync.Map

The Go standard library has [sync.Map](https://pkg.go.dev/sync#Map), a concurrent hash map.

Adapt the [implementation](https://cs.opensource.google/go/go/+/refs/tags/go1.23.0:src/sync/map.go;l=38) to develop a version that works with Goose (I can help you with this part) and verify it. You don't need to deal with the `any` type; feel free to specialize to a map from integers to integers. Focus on a few key operations, such as Load, Store, and CompareAndSwap; they'll capture the essential difficulty.

### Verify a UTF-8 library

Verify a library for UTF-8; a minimum implementation would be [Valid](https://pkg.go.dev/unicode/utf8@go1.23.1#Valid) (which checks if a byte sequence has only valid UTF-8-encoded runes) and [DecodeRune](https://pkg.go.dev/unicode/utf8@go1.23.1#DecodeRune) (which find the end of the first rune in a byte sequence).

Many programs rely on a such a library for manipulating text encoded as UTF-8. This code is a bit tricky to write, and needs to be high performance.

A principle task for you in this project is to understand and encode the UTF-8 spec using pure Coq functions; this would be of independent interest and you'll learn something valuable.

Note that implementing Unicode on top of UTF-8 is a massive task. I haven't looked into what this would entail and if there's a useful and small-enough starting point, but you're welcome to do that study and report back.
