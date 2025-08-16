---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
order: 1
shortTitle: "Assignment 3: intro"
---

# Introduction to program proofs

These exercises should help you get started with doing program proofs with Goose. They're split into two parts: using the Iris Proof Mode for proving $P ⊢ Q$ with separation logic assertions (without any proofs about programs), and proving specifications using the weakest precondition tactics and lemmas.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import functional_init heap_init.

Section proof.
Context `{!heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

```

## IPM exercises

Here is a detailed proof of a simple separation logic entailment in the IPM, one small step at a time.

```rocq
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

```rocq
Lemma example_sep_comm_v2 (P Q: iProp Σ) :
  P ∗ Q -∗ Q ∗ P.
Proof.

```

We can use a destruct pattern right away when doing an `iIntros`, without naming the intermediate result.

```rocq
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

```rocq
Lemma example_sep_comm_v3 (P Q: iProp Σ) :
  P ∗ Q -∗ Q ∗ P.
Proof.
  iIntros "[HP HQ]".

```

Using `iFrame` here is more than just more concise: `iFrame` automatically decides the split so we don't have to.

```rocq
  iFrame.
Qed.

```

**Exercise:** complete the proof

```rocq
Lemma ex_rearrange_1 (P Q R: iProp Σ) :
  R -∗ Q ∗ P -∗ P ∗ Q ∗ R.
Proof.
Admitted.

```

In this example we use a Coq-level implication. In this case, it comes from a premise in the lemma, but it will often be a previously proven lemma; using such a lemma looks the same as this use of a hypothesis in the lemma.

```rocq
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

```rocq
Lemma example_pure_impl_v2 (P Q R: iProp Σ) :
  (P -∗ Q) →
  P ∗ R -∗ Q ∗ R.
Proof.
  iIntros (HPQ) "[HP HR]".

```

In this proof, the `R` part of the proof can be handled separately; we don't need `R` any more.

```rocq
  iFrame.
  iApply HPQ. iFrame.
Qed.

```

**Exercise:** complete the proof

You'll need to find the right lemma to use here.

```rocq
Lemma ex_pure_impl s q (bs: list w8) :
  length bs = 3%nat →
  s ↦*{q} bs -∗
  ⌜slice.len_f s = 3%Z⌝ ∗ s ↦*{q} bs.
Proof.
Admitted.

```

**Exercise:** complete the proof

Read about [structs](../../notes/ownership.md#proofs-using-structs) (in particular `wp_ExamplePersonRef`) to see how to do this.

```rocq
Lemma ex_split_struct l s :
  l ↦ heap.S1.mk (W64 3) s -∗
  l ↦s[heap.S1 :: "a"] W64 3 ∗
  l ↦s[heap.S1 :: "b"] s.
Proof.
Admitted.

```

You will need `iModIntro` to "introduce" the `▷P` (later) and `|==> P` (update) modalities. The update modality in particular is often needed at the end of a program proof, before proving the postcondition.

```rocq
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
  globalsGS0 : globalsGS Σ
  go_ctx : GoContext
  P : iProp Σ
  ============================
  "HP" : P
  --------------------------------------∗
  |==> P // [!code --]
  P // [!code ++]
```

::::

```rocq
  iApply "HP".
Qed.

```

These modalities both _weaken_ a proposition: `P ⊢ ▷P` and `P ⊢ |==> P`. Of course there will be situations where you can prove `▷P` but not `P` (otherwise there would be no point in having the modality), but we won't actually see those for later, and the update modality won't come up for a while.

Nonetheless you will want to be able to switch from proving `▷P` to `P`, using the `P ⊢ ▷P` rule (do you see why that makes sense as a backward step?). This is done with `iModIntro`.

**Exercise:** complete the proof

```rocq
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

```rocq
Lemma wp_Swap (l1 l2: loc) (x y: w64) :
  {{{ is_pkg_init heap.heap ∗ l1 ↦ x ∗ l2 ↦ y }}}
    @! heap.heap.Swap #l1 #l2
  {{{ RET #(); l1 ↦ y ∗ l2 ↦ x }}}.
Proof.
  wp_start as "(Hx & Hy)".

  (* The next instruction to run is to allocate a pointer for the function
  parameter y. *)
  wp_alloc y_l as "y". wp_pures.
  (* we can automate some of that work, using the variable name *)
  wp_alloc_auto. wp_pures. wp_alloc_auto.
  wp_pures.

  wp_bind (![_] #y_l)%E.
  iApply (@wp_load_ty with "[y]").
  { iFrame. }
  iModIntro. (* remove the ▷ ("later") modality from the goal - you can ignore
  this *)
  (* Notice that the load spec requires ownership over the address [l1] for the
  duration of the call, then returns it in the postcondition. It does this in
  the form of an implication, so we have to use [iIntros] to put the hypothesis
  back in the context. *)
  iIntros "y".

  (* [wp_apply] automates the process of finding where to apply the spec, so we
  don't have to use [wp_bind]. It also automatically removes the ▷ from the
  resulting goal. *)
  wp_apply (@wp_load_ty with "[$Hy]"). iIntros "Hy".

  (* Loading and storing variables is common enough that there's a tactic
  [wp_load] which automates the work of [wp_bind], finding the right hypothesis
  with a points-to fact (that is, something like [l2 ↦ y]), and also
  re-introducing the hypothesis after using the [wp_load_ty] or [wp_store_ty]
  lemma. *)

  wp_pures. wp_store.
  wp_auto.

  iApply "HΦ".
  iFrame.
Qed.

```

**Exercise:** complete the proof.

Re-do above proof, but with the automation tactics.

```rocq
Lemma wp_Swap_ex (l1 l2: loc) (x y: w64) :
  {{{ is_pkg_init heap.heap ∗ l1 ↦ x ∗ l2 ↦ y }}}
    @! heap.heap.Swap #l1 #l2
  {{{ RET #(); l1 ↦ y ∗ l2 ↦ x }}}.
Proof.
Admitted.

```

**Exercise:** complete the proof.

Compare this specification to the one we saw in the separation logic notes.

Prove it using the IPM. You may need to find the specification for `Assert` using `Search` (or you can guess what it's called).

```rocq
Lemma wp_IgnoreOneLocF (x_l y_l: loc) :
  {{{ is_pkg_init heap.heap ∗ x_l ↦ W64 0 }}}
    @! heap.heap.IgnoreOneLocF #x_l #y_l
  {{{ RET #(); x_l ↦ W64 42 }}}.
Proof.
Admitted.

Lemma wp_UseIgnoreOneLocOwnership :
  {{{ is_pkg_init heap.heap }}}
    @! heap.heap.UseIgnoreOneLocOwnership #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

```

**Exercise:** read this function and compare it to the specification.

The `(x_l: loc)` in the postcondition should be read as "there exists (x_l: loc), ..." where the ... is the rest of the postcondition. Special syntax is used so that `x_l` can be used in the `RET` clause itself.

```rocq
Lemma example_stack_escape :
  {{{ is_pkg_init heap.heap }}}
    @! heap.heap.StackEscape #()
  {{{ (x_l: loc), RET #x_l; x_l ↦ W64 42 }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

End proof.
```
