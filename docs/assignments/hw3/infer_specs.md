---
# Auto-generated from literate source. DO NOT EDIT.
category: assignment
tags: literate
order: 2
shortTitle: "Assignment 3: infer specs"
---

# Assignment 3: Inferring specifications

For each `Example` function in [go/heap/exercises.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/heap/exercises.go), come up with a general specification of the snippet's behavior, state it in Coq, and prove it correct. A specification for `ExampleA` is provided below as an example.

```rocq
From sys_verif Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init.

Section goose.
Context `{!heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

(* worked example of a general specification *)
Lemma wp_ExampleA (x_l y_l: loc) (z: w64) (x: bool) (y: w64) q :
  {{{ is_pkg_init heap.heap ∗
      "x" :: x_l ↦{q} x ∗ "y" :: y_l ↦ y }}}
    @! heap.heap.ExampleA #x_l #y_l #z
  {{{ RET #(); x_l ↦{q} x ∗
               y_l ↦ (if x then z else 0) }}}.
Proof.
  wp_start as "H". iNamed "H".
Admitted.

Lemma wp_ExampleB :
  {{{ True }}}
    @! heap.heap.ExampleB #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma wp_ExampleC :
  {{{ True }}}
    @! heap.heap.ExampleC #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.

```

**Warning**: this one is a bit harder than the rest in both specification and proof.

```rocq
Lemma wp_ExampleD :
  {{{ True }}}
    @! heap.heap.ExampleD #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma wp_ExampleE :
  {{{ True }}}
    @! heap.heap.ExampleE #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.
End goose.
```
