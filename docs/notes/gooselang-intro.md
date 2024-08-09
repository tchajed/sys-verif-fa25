---
order: -1
---

# Verifying Go code

Recall the FastExp example:

```go
// FastExp returns b to the power of n
func FastExp(b uint64, n uint64) uint64
```

We wanted to show that this function computes $b^n$, but we didn't have a way to express that, especially one that would work for more complicated functions that dealt with pointers or interacted with the outside world.

Here's what the spec we'll write looks like:

```coq
Lemma wp_FastExp (b n0: w64) :
  {{{ ⌜(uint.Z b)^(uint.Z n0) < 2^64⌝  }}}
    FastExp #b #n0
  {{{ (e: w64), RET #e; ⌜uint.Z e = (uint.Z b)^(uint.Z n0)⌝ }}}.
```
