---
# Auto-generated from literate source. DO NOT EDIT.
category: assignment
tags: literate
order: 4
shortTitle: "Assignment 3: linked lists"
---

# Assignment 3: Linked lists as lists

This proof develops a specification for the linked-list implementation at [go/heap/linked_list.go](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/go/heap/linked_list.go).

You should start by reading the Go code.

The idea of this proof is similar to what you saw in Assignment 2's exercise 5, but with the code written in Go (and thus using nil pointers rather than an inductive data type) and with the proof written in Coq (so you have the Iris Proof Mode rather than writing a proof outline).

```coq
From sys_verif.program_proof Require Import prelude.
From Goose.sys_verif_code Require Import heap.


Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

(* We abbreviate "linked list" to "ll" in some of these definitions to keep
specs and other theorem statements concise. *)

```

After reading the code, read the definition of `ll_rep` and understand how it relates a list pointer (which will be a `n *Node`) to a list of values `xs: list w64`.

```coq
Fixpoint ll_rep (l: loc) (xs: list w64) : iProp Σ :=
  match xs with
  | nil => "%Heq" :: ⌜l = null⌝
  | cons x xs' => (∃ (next_l: loc),
      "elem" :: l ↦[Node :: "elem"] #x ∗
      "next" :: l ↦[Node :: "next"] #next_l ∗
      "Hnext_l" :: ll_rep next_l xs')%I
  end.

```

The proofs will work by analysis on `xs`, but the code checks if `l` is `nil` or not. We relate the two with the following two lemmas (note that the Gallina `null` is the model of the Go `nil` pointer).

```coq
Definition ll_rep_null l :
  ll_rep l [] -∗ ⌜l = null⌝.
Proof.
  simpl. auto.
Qed.

Definition ll_rep_non_null l x xs :
  ll_rep l (x::xs) -∗ ⌜l ≠ null⌝.
Proof.
  simpl. iIntros "H". iNamed "H".
  iDestruct (struct_field_pointsto_not_null with "elem") as %Hnot_null.
  { reflexivity. }
  { simpl. lia. }
  auto.
Qed.

```

Prove this specification.

```coq
Lemma wp_NewList :
  {{{ True }}}
    NewList #()
  {{{ (l: loc), RET #l; ll_rep l [] }}}.
Proof.
Admitted.


```

Fill in a postcondition here and prove this specification.

```coq
Lemma wp_Node__Insert (l: loc) (xs: list w64) (elem: w64) :
  {{{ ll_rep l xs }}}
    Node__Insert #l #elem
  {{{ (l': loc), RET #l';
      False  }}}.
Proof.
Admitted.

```

Prove this specification.

```coq
Lemma wp_Node__Pop (l: loc) (xs: list w64) :
  {{{ ll_rep l xs }}}
    Node__Pop #l
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

```coq
Lemma wp_Node__Append l1 xs1 l2 xs2 :
  {{{ ll_rep l1 xs1 ∗ ll_rep l2 xs2 }}}
    Node__Append #l1 #l2
  {{{ (l2': loc), RET #l2';
      False  }}}.
Proof.
  generalize dependent xs2.
  generalize dependent l2.
  generalize dependent l1.
  induction xs1 as [|x1 xs1 IH_wp_Append].
  - intros l1 l2 xs2. wp_start as "[Hl1 Hl2]".
    iDestruct (ll_rep_null with "Hl1") as %Hnull.
    admit.
  - intros l1 l2 xs2. wp_start as "[Hl1 Hl2]".
    (* Notice the hypothesis `IH_wp_Append`, which is available due to the use
    of `induction`. You'll need it to reason about the recursive call. *)
    iDestruct (ll_rep_non_null with "Hl1") as %Hnull.
    admit.
Admitted.

End proof.
```
