---
order: -1
category: lecture
tags: [draft]
---

# Draft: Verifying Go code

::: warning
This note is a draft.
:::

Recall the FastExp example:

```go
// FastExp returns b to the power of n
func FastExp(b uint64, n uint64) uint64
```

We wanted to show that this function computes $b^n$, but we didn't have a way to express that, especially one that would work for more complicated functions that modified their inputs or used pointers.

What we're building up to is a spec that looks like this:

```coq
Lemma wp_FastExp (b n0: w64) :
  {{{ ⌜(uint.Z b)^(uint.Z n0) < 2^64⌝  }}}
    FastExp #b #n0
  {{{ (e: w64), RET #e; ⌜uint.Z e = (uint.Z b)^(uint.Z n0)⌝ }}}.
```

There are three broad steps before we can get to that spec, though:

1. Use Goose to model the Go code's behavior in Coq.
2. Understand how to write a specification for a function using pre- and post-conditions.
3. Understand how to prove such specifications.

We'll start by going through this process for _pure_ functions, translating what we've seen for Coq functions to similar implementations written in Go (but for example with loops rather than recursion and the ability to modify local variables). Then, we'll extend the modeling, specification, and proof approaches to handle pointers.
