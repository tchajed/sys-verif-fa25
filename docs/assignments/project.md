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
