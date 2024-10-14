---
order: -1
icon: code
---

# Final project

For the final project, you'll pick something to verify. The details are still to be finalized, but here are the rough parameters.

The idea here is for you to explore something you're interested in and complete a more substantial proof. I'll give 1-2 straightforward options and 1-2 more difficult ideas. Whatever you work on I suggest you write a short, 1-2 page proposal explaining what you're planning to do, and/or schedule a meeting with me, so I can give feedback (mainly so I can confirm the scope is reasonable and that you have some intermediate goals).

## Make Goose easier to use

Did you find something difficult while doing the previous assignments? It's an open project option to fix a pain point you experienced. This could involve writing documentation, but it would need to be substantial and involve code examples.

## Verify the Go sync.Map

The Go standard library has [sync.Map](https://pkg.go.dev/sync#Map), a concurrent hash map.

Adapt the [implementation](https://cs.opensource.google/go/go/+/refs/tags/go1.23.0:src/sync/map.go;l=38) to develop a version that works with Goose (I can help you with this part) and verify it. You don't need to deal with the `any` type; feel free to specialize to a map from integers to integers. Focus on a few key operations, such as Load, Store, and CompareAndSwap; they'll capture the essential difficulty.

## Verify a UTF-8 library

Verify a library for UTF-8; a minimum implementation would be [Valid](https://pkg.go.dev/unicode/utf8@go1.23.1#Valid) (which checks if a byte sequence has only valid UTF-8-encoded runes) and [DecodeRune](https://pkg.go.dev/unicode/utf8@go1.23.1#DecodeRune) (which find the end of the first rune in a byte sequence).

Many programs rely on a such a library for manipulating text encoded as UTF-8. This code is a bit tricky to write, and needs to be high performance.

A principle task for you in this project is to understand and encode the UTF-8 spec using pure Coq functions; this would be of independent interest and you'll learn something valuable.

Note that implementing Unicode on top of UTF-8 is a massive task. I haven't looked into what this would entail and if there's a useful and small-enough starting point, but you're welcome to do that study and report back.

## Verify a range map data structure

Verify a data structure that can efficiently map a (potentially large) range of keys to a single value. Example use cases include processing a firewall configuration, where the keys would be IP addresses and rules apply to whole IP address ranges, or for efficiently filtering based on `.gitignore` rules.

You can simplify the implementation by only supporting integer keys. A more sophisticated implementation would support strings; Goose does not (currently) support string comparison with `s1 < s2`, so you would need to implement this yourself.

This requires some data structure design. A starting point would be to maintain a list of sorted ranges that you search with binary search.

## Verify the Cloudflare trie-hard data structure

Port [trie-hard](https://github.com/cloudflare/trie-hard) to Go and verify it. Specialize that implementation to u64.

This is a trie (an efficient prefix-search data structure, especially for a fixed set of search strings), but with the twist of encoding the pointers into the bits of an integer for space efficiency (without this Cloudflare found it wasn't faster than a Rust `HashMap`).

## Verify Go's sort.Find

We saw a simplified binary search implementation in the notes. Specify and verify the Go binary search implementation, [sort.Find](https://pkg.go.dev/sort#Find) from the standard library.

(I think this project is a bit more straightforward than many of the others.)
