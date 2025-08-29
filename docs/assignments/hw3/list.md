---
# Auto-generated from literate source. DO NOT EDIT.
category: assignment
tags: literate
order: 4
shortTitle: "Assignment 3: linked lists"
---

# Assignment 3: Linked lists as lists

This proof develops a specification for the linked-list implementation at [go/heap/list/linked_list.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/heap/list/linked_list.go).

You should start by reading the Go code.

The idea of this proof is similar to what you saw in Assignment 2's exercise 5, but with the code written in Go (and thus using nil pointers rather than an inductive data type) and with the proof written in Coq (so you have the Iris Proof Mode rather than writing a proof outline).

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From New.generatedproof.sys_verif_code Require Import linked_list.


Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit linked_list := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf linked_list := build_get_is_pkg_init_wf.

(* We abbreviate "linked list" to "ll" in some of these definitions to keep
specs and other theorem statements concise. *)

```

After reading the code, read the definition of `ll_rep` and understand how it relates a list pointer (which will be a `n *Node`) to a list of values `xs: list w64`.

```rocq
Fixpoint ll_rep (l: loc) (xs: list w64) : iProp Σ :=
  match xs with
  | nil => "%Heq" :: ⌜l = null⌝
  | cons x xs' => (∃ (next_l: loc),
      "elem" :: l ↦s[linked_list.Node :: "elem"] x ∗
      "next" :: l ↦s[linked_list.Node :: "next"] next_l ∗
      "Hnext_l" :: ll_rep next_l xs')%I
  end.

```

The proofs will work by analysis on `xs`, but the code checks if `l` is `nil` or not. We relate the two with the following two lemmas (note that the Gallina `null` is the model of the Go `nil` pointer).

```rocq
Lemma ll_rep_null l :
  ll_rep l [] -∗ ⌜l = null⌝.
Proof.
  simpl. auto.
Qed.

Lemma ll_rep_non_null l x xs :
  ll_rep l (x::xs) -∗ ⌜l ≠ null⌝.
Proof.
  simpl. iIntros "H". iNamed "H".
  iDestruct (field_pointsto_not_null with "elem") as %Hnot_null; done.
Qed.

```

Prove this specification.

```rocq
Lemma wp_New :
  {{{ is_pkg_init linked_list }}}
    @! linked_list.New #()
  {{{ (l: loc), RET #l; ll_rep l [] }}}.
Proof.
Admitted.


```

Fill in a postcondition here and prove this specification.

```rocq
Lemma wp_Node__Insert (l: loc) (xs: list w64) (elem: w64) :
  {{{ is_pkg_init linked_list ∗ ll_rep l xs }}}
    l @ (ptrT.id linked_list.Node.id) @ "Insert" #elem
  {{{ (l': loc), RET #l';
      False  }}}.
Proof.
Admitted.

```

Prove this specification.

```rocq
Lemma wp_Node__Pop (l: loc) (xs: list w64) :
  {{{ is_pkg_init linked_list ∗ ll_rep l xs }}}
    l @ (ptrT.id linked_list.Node.id) @ "Pop" #()
  {{{ (x: w64) (l': loc) (ok: bool), RET (#x, #l', #ok);
      if ok then ∃ xs', ⌜xs = cons x xs'⌝ ∗
                        ll_rep l' xs'
      else ⌜xs = []⌝
  }}}.
Proof.
Admitted.


```

Fill in this specification. (You should read the code to see what it does and how it manages the memory of the two lists.)

A general structure is provided for the proof (which you are allowed to change if you find it helpful); fill in the rest of the proof.

```rocq
Lemma wp_Node__Append l1 xs1 l2 xs2 :
  {{{ is_pkg_init linked_list ∗
      ll_rep l1 xs1 ∗ ll_rep l2 xs2 }}}
    l1 @ (ptrT.id linked_list.Node.id) @ "Append" #l2
  {{{ (l2': loc), RET #l2';
      False  }}}.
Proof.
  generalize dependent xs2.
  generalize dependent l2.
  generalize dependent l1.
  induction xs1 as [|x1 xs1 IH_wp_Append].
  - intros l1 l2 xs2. wp_start as "[Hl1 Hl2]".
    wp_auto.
    iDestruct (ll_rep_null with "Hl1") as %Hnull.
    admit.
  - intros l1 l2 xs2. wp_start as "[Hl1 Hl2]".
    wp_auto.
    (* Notice the hypothesis `IH_wp_Append`, which is available due to the use
    of `induction`. You'll need it to reason about the recursive call. *)
    iDestruct (ll_rep_non_null with "Hl1") as %Hnull.
    admit.
Admitted.

End proof.
```
