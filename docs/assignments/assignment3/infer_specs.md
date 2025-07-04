---
# Auto-generated from literate source. DO NOT EDIT.
category: assignment
tags: literate
order: 2
shortTitle: "Assignment 3: infer specs"
---

# Assignment 3: Inferring specifications

For each `Example` function in [go/heap/exercises.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/heap/exercises.go), come up with a general specification of the snippet's behavior, state it in Coq, and prove it correct. A specification for `ExampleA` is provided below as an example.

```coq
From sys_verif Require Import prelude empty_ffi.
From Goose.sys_verif_code Require Import heap.

Section goose.
Context `{!heapGS Σ}.

(* worked example of a general specification *)
Lemma wp_ExampleA (x_l y_l: loc) (z: w64) (x: bool) (y: w64) q :
  {{{ "x" :: x_l ↦[boolT]{q} #x ∗ "y" :: y_l ↦[uint64T] #y }}}
    ExampleA #x_l #y_l #z
  {{{ RET #(); x_l ↦[boolT]{q} #x ∗
               y_l ↦[uint64T] (if x then #z else #0) }}}.
Proof.
  wp_start as "H". iNamed "H".
Admitted.

Lemma wp_ExampleB :
  {{{ True }}}
    ExampleB #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.

Lemma wp_ExampleC :
  {{{ True }}}
    ExampleC #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.

```

**Warning**: this one is a bit harder than the rest in both specification and proof.

```coq
Lemma wp_ExampleD :
  {{{ True }}}
    ExampleD #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.

(* you will not need to directly use this, it will be used automatically *)
Lemma slice_nil_ty ty : val_ty slice.nil (slice.T ty).
Proof.
  change slice.nil with (slice_val Slice.nil).
  apply slice_val_ty.
Qed.

Hint Resolve slice_nil_ty : core.

Lemma wp_ExampleE :
  {{{ True }}}
    ExampleE #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.

```

**Hint:** you can check `exercises_test.go` file to figure out what this function does.

```coq
Lemma wp_ExampleG :
  {{{ True }}}
    ExampleG #()
  {{{ RET #(); True }}}.
Proof.
  (* FILL IN HERE *)
Admitted.
End goose.
```
