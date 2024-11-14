---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
order: 1
shortTitle: "Assignment 3: intro"
---

# Introduction to program proofs

These exercises should help you get started with doing program proofs with Goose. They're split into two parts: using the Iris Proof Mode for proving $P ⊢ Q$ with separation logic assertions (without any proofs about programs), and proving specifications using the weakest precondition tactics and lemmas.

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Goose.sys_verif_code Require Import functional heap.

Section proof.
Context `{!heapGS Σ}.

```

## IPM exercises

Here is a detailed proof of a simple separation logic entailment in the IPM, one small step at a time.

```coq
Lemma example_sep_comm_v1 (P Q: iProp Σ) :
  P ∗ Q -∗ Q ∗ P.
Proof.
  iIntros "H". iDestruct "H" as "[HP HQ]".
  iSplitL "HQ".
  - iExact "HQ".
  - iExact "HP".
Qed.

```

Now let's see the same proof more concisely.

```coq
Lemma example_sep_comm_v2 (P Q: iProp Σ) :
  P ∗ Q -∗ Q ∗ P.
Proof.

```

We can use a destruct pattern right away when doing an `iIntros`, without naming the intermediate result.

```coq
  iIntros "[HP HQ]".
  iSplitL "HQ".
  - iFrame.
  - iFrame.
Qed.

```

:::: info Exercise: typing special symbols

You should make sure you know how to type the special symbols in these specifications.

Delete each specification in this file and type it out again.

Refer to the [input guide](/notes/program-proofs/input.md) for guidance on how to type each symbol.

One easy thing to miss is that `P ∗ Q` (separating conjunction) requires you to type \sep. It's not the same as `x * y` (multiplication of integers).

::::

```coq
Lemma example_sep_comm_v3 (P Q: iProp Σ) :
  P ∗ Q -∗ Q ∗ P.
Proof.
  iIntros "[HP HQ]".

```

Using `iFrame` here is more than just more concise: `iFrame` automatically decides the split so we don't have to.

```coq
  iFrame.
Qed.

```

**Exercise:** complete the proof

```coq
Lemma ex_rearrange_1 (P Q R: iProp Σ) :
  R -∗ Q ∗ P -∗ P ∗ Q ∗ R.
Proof.
Admitted.

```

In this example we use a Coq-level implication. In this case, it comes from a premise in the lemma, but it will often be a previously proven lemma; using such a lemma looks the same as this use of a hypothesis in the lemma.

```coq
Lemma example_pure_impl_v1 (P Q R: iProp Σ) :
  (P -∗ Q) →
  P ∗ R -∗ Q ∗ R.
Proof.
  iIntros (HPQ) "[HP HR]".
  iDestruct (HPQ with "[$HP]") as "HQ".
  iFrame.
Qed.

```

Make sure you understand the following alternatives to the `iDestruct` above (try them out and see what happens);

- `iDestruct (HPQ with "[]") as "HQ"`
- `iDestruct (HPQ with "[HP]") as "HQ"`
- `iDestruct (HPQ with "[$HP]") as "HQ"`

There is also `iDestruct (HPQ with "HP")`. This is similar to `iDestruct (HPQ with "[$HP]")` but requires `"HP"` to _exactly_ match the premise of `HPQ`. It is primarily useful when the premise is very simple, but it is reasonable for you to forget about it and always use the framing version, rather than remembering one more variant of specialization patterns.

The previous proof was in _forward_ style (working from the hypotheses). We can also do a backward proof.

```coq
Lemma example_pure_impl_v2 (P Q R: iProp Σ) :
  (P -∗ Q) →
  P ∗ R -∗ Q ∗ R.
Proof.
  iIntros (HPQ) "[HP HR]".

```

In this proof, the `R` part of the proof can be handled separately; we don't need `R` any more.

```coq
  iFrame.
  iApply HPQ. iFrame.
Qed.

```

**Exercise:** complete the proof

You'll need to find the right lemma to use here.

```coq
Lemma ex_pure_impl s q (bs: list w8) :
  length bs = 3%nat →
  own_slice_small s byteT q bs -∗
  ⌜Slice.sz s = 3%Z⌝ ∗ own_slice_small s byteT q bs.
Proof.
Admitted.

```

**Exercise:** complete the proof

Read about [structs](../../notes/ownership.md#proofs-using-structs) (in particular `wp_ExamplePersonRef`) to see how to do this.

```coq
Lemma ex_split_struct l s :
  l ↦[struct.t S1] (#(W64 3), (s, #())) -∗
  l ↦[S1 :: "a"] #(W64 3) ∗
  l ↦[S1 :: "b"] s.
Proof.
Admitted.

```

You will need `iModIntro` to "introduce" the `▷P` (later) and `|==> P` (update) modalities. The update modality in particular is often needed at the end of a program proof, before proving the postcondition.

```coq
Lemma example_update_modality (P: iProp Σ) :
  P -∗ |==> P.
Proof.
  iIntros "HP".
  iModIntro.
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  heapGS0 : heapGS Σ
  P : iProp Σ
  ============================
  "HP" : P
  --------------------------------------∗
  |==> P // [!code --]
  P // [!code ++]
```

::::

```coq
  iApply "HP".
Qed.

```

These modalities both _weaken_ a proposition: `P ⊢ ▷P` and `P ⊢ |==> P`. Of course there will be situations where you can prove `▷P` but not `P` (otherwise there would be no point in having the modality), but we won't actually see those for later, and the update modality won't come up for a while.

Nonetheless you will want to be able to switch from proving `▷P` to `P`, using the `P ⊢ ▷P` rule (do you see why that makes sense as a backward step?). This is done with `iModIntro`.

**Exercise:** complete the proof

```coq
Lemma ex_later_modality (P Q: iProp Σ) :
  P ∗ (P -∗ Q) -∗ ▷ Q.
Proof.
Admitted.

```

## Program proofs

Here is a worked example. It demonstrates a number of tactics:

- `wp_bind`
- `iApply` with a `wp_*` theorem
- `wp_apply`
- `wp_load` and `wp_store`

```coq
Lemma wp_Swap (l1 l2: loc) (x y: w64) :
  {{{ l1 ↦[uint64T] #x ∗ l2 ↦[uint64T] #y }}}
    Swap #l1 #l2
  {{{ RET #(); l1 ↦[uint64T] #y ∗ l2 ↦[uint64T] #x }}}.
Proof.
  wp_start as "[Hx Hy]".
  wp_pures.

  (* The next instruction to run is a load from [l2]. *)
  wp_bind (![_] #l2)%E.
  iApply (wp_LoadAt with "[Hy]").
  { iFrame. }
  iModIntro. (* remove the ▷ ("later") modality from the goal - you can ignore
  this *)
  (* Notice that the load spec requires ownership over the address [l1] for the
  duration of the call, then returns it in the postcondition. It does this in
  the form of an implication, so we have to use [iIntros] to put the hypothesis
  back in the context. *)
  iIntros "Hy".

  (* [wp_apply] automates the process of finding where to apply the spec, so we
  don't have to use [wp_bind]. It also automatically removes the ▷ from the
  resulting goal. *)
  wp_apply (wp_LoadAt with "[$Hx]"). iIntros "Hx".

  (* Loading and storing variables is common enough that there's a tactic
  [wp_load] which automates the work of [wp_bind], finding the right hypothesis
  with a points-to fact (that is, something like [l2 ↦[uint64T] #y]), and also
  re-introducing the hypothesis after using the [wp_LoadAt] or [wp_StoreAt]
  lemma. *)

  wp_store.
  wp_store.

  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

```

**Exercise:** complete the proof.

Re-do above proof, but with the automation tactics.

```coq
Lemma wp_Swap_ex (l1 l2: loc) (x y: w64) :
  {{{ l1 ↦[uint64T] #x ∗ l2 ↦[uint64T] #y }}}
    Swap #l1 #l2
  {{{ RET #(); l1 ↦[uint64T] #y ∗ l2 ↦[uint64T] #x }}}.
Proof.
Admitted.

```

**Exercise:** complete the proof.

Compare this specification to the one we saw in the separation logic notes.

Prove it using the IPM. You may need to find the specification for `Assert` using `Search` (or you can guess what it's called).

```coq
Lemma wp_IgnoreOneLocF (x_l y_l: loc) :
  {{{ x_l ↦[uint64T] #(W64 0) }}}
    IgnoreOneLocF #x_l #y_l
  {{{ RET #(); x_l ↦[uint64T] #(W64 42) }}}.
Proof.
Admitted.

Lemma wp_UseIgnoreOneLocOwnership :
  {{{ True }}}
    UseIgnoreOneLocOwnership #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

```

**Exercise:** read this function and compare it to the specification.

The `(x_l: loc)` in the postcondition should be read as "there exists (x_l: loc), ..." where the ... is the rest of the postcondition. Special syntax is used so that `x_l` can be used in the `RET` clause itself.

```coq
Lemma example_stack_escape :
  {{{ True }}}
    StackEscape #()
  {{{ (x_l: loc), RET #x_l; x_l ↦[uint64T] #(W64 42) }}}.
Proof.
  wp_start as "_".

```

`wp_alloc` is a helper for using the allocation specifications, much like `wp_load` and `wp_store`.

```coq
  wp_alloc x_l as "Hx".
  wp_pures.
  iModIntro. iApply "HΦ". iFrame.
Qed.

End proof.
```
