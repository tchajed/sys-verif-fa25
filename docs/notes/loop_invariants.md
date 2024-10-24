---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 12
shortTitle: "Lecture 12: Loop invariants"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 12: Loop invariants

> Follow these notes in Coq at [src/sys_verif/program_proof/loop_invariants.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/loop_invariants.v).

## Learning outcomes

By the end of this lecture, you should be able to:

1. Recall the obligations for a loop invariant to be correct.
2. Struggle to come up with loop invariants for examples.

---

## Loop invariants

The general idea for proving the correctness of a loop is to invent a _loop invariant_, an assertion that is (1) true when the loop starts, and (2) _if_ the loop invariant holds at the start of the loop, it should hold at the end. If you prove these two things, via induction, you've proven that the loop invariant is true at the end of the loop. We also can learn one more fact which is necessary in practice: the loop probably has a "break condition", a property that is true when it terminates. We know the loop invariant is preserved by each iteration, and if the loop exits it satisfies the break condition.

Here's the principle of loop invariants stated formally, for the `for` loop model above. This is a theorem in Perennial (slightly simplified).

```coq
Lemma wp_forBreak (I: bool -> iProp Σ) (body: val) :
  {{{ I true }}}
    body #()
  {{{ r, RET #r; I r }}} -∗
  {{{ I true }}}
    (for: (λ: <>, #true)%V ; (λ: <>, Skip)%V :=
       body)
  {{{ RET #(); I false }}}.
```

The invariant `I` takes a boolean which is true if the loop is continuing and becomes false when it stops iterating.

Note that loop invariants are a _derived principle_. The proof of the theorem above is based only on recursion (since that's how `For` is implemented), and in fact Perennial has some other loop invariant-like rules for special cases of `for` loops, like the common case of `for i := 0; i < n; i++ { ... }`.

You can think of `I true` and `I false` as two slightly different invariants: `I true` means the loop will run again, while `I false` means the loop terminates. Commonly `I false` is a stronger statement which is true only when the loop exits (it reaches some desired stopping condition, like `!(i < n)`).

::: important Main idea

This theorem produces two proof obligations when used:

1. `I` is preserved by the loop. More precisely the loop gets to assume `I true` (since the loop continues), and must prove `I r`, where `r` is the continue/break boolean that the body returns.
2. The loop invariant holds initially. More precisely `I true`.

The result is the assertion `I false`, which is used to verify the rest of the code (after the for loop).

:::

### Exercise (difficult, especially useful)

The informal description above describes a "continue condition" and "break condition", but that is not how `wp_forBreak` is written. In this exercise you'll bridge the gap.

1. Reformulate `wp_forBreak` so that it takes a regular loop invariant and a break condition as separate arguments, to more closely match the principle above. That, state a different theorem (let's call it `wp_for_breakCondition`) for proving a specification about that same expression `(for: (λ: <>, #true)%V ; (λ: <>, Skip)%V := body)`.
2. Prove your new `wp_for_breakCondition` using `wp_forBreak`. You should replace the `-∗` in the theorem statement with a `→` (we will discuss what difference this creates later when we talk about something called the _persistently modality_).

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Perennial.program_proof Require Import std_proof.
From Goose.sys_verif_code Require heap functional.

#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section goose.
Context `{hG: !heapGS Σ}.

```

For our first example, we'll consider a function that adds the numbers from 1 to $n$. We'll prove this produces $n(n+1)/2$.

Before doing this with a loop, let's consider a recursive implementation. The recursive version turns out to be a bit _easier_ in this case because the specification for the entire function is sufficient: we can prove `SumNrec` produces $n(n+1)/2$ by merely assuming that every recursive subcall is already correct. (This reasoning is sound because we aren't proving termination; if it seems magical, it's the same magic that goes into recursion in general.)

This proof strategy does not always work. In general, when we want to prove something with induction or recursion, we might need to _strengthen the induction hypothesis_. But for this example, when implemented recursively, the original specification is enough.

```go
// SumNrec adds up the numbers from 1 to n, recursively.
func SumNrec(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return n + SumNrec(n-1)
}
```

This implementation might overflow a 64-bit number. This specification handles this case by assuming the result doesn't overflow.

```coq
Lemma wp_SumNrec (n: w64) :
  {{{ ⌜uint.Z n * (uint.Z n + 1) / 2 < 2^64⌝ }}}
    functional.SumNrec #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as %Hoverflow.
  iLöb as "IH" forall (n Hoverflow Φ).
  wp_rec. wp_pures.
  wp_if_destruct.
  - iModIntro.
    iApply "HΦ".
    iPureIntro.
    word.
  - wp_pures.
    wp_apply "IH".
    { iPureIntro.
      word. }
    iIntros (m Hm).
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    (* [word] doesn't work on its own here. It's helpful to know how to do some of the work it does manually, to help it along. *)
    rewrite word.unsigned_add_nowrap.
    + rewrite Hm. word.
    + rewrite Hm. word.
Qed.

```

### SumN with a loop

Now let's re-implement this function with a loop instead. Here we handle integer overflow differently: the function `std.SumAssumeNoOverflow(x, y)` returns `x + y` and panics if the result would overflow, but we do not prove this function doesn't panic. This introduces an assumption in our whole verified code that this sum never overflows.

```go
// SumN adds up the numbers from 1 to n, with a loop.
func SumN(n uint64) uint64 {
	var sum = uint64(0)
	var i = uint64(1)
	for {
		if i > n {
			break
		}
		sum = std.SumAssumeNoOverflow(sum, i)
		i++
	}
	return sum
}
```

The first proof we'll attempt for this function has a minimal loop invariant that shows that the heap loads and stores work, but nothing about the values of the `sum` and `i` variables.

This is a problem of not having a strong enough loop invariant. The loop invariant is an invariant: we can prove it holds initially and that it is preserved by the loop. However, it's hopelessly weak for proving that `return sum` is correct after the loop - it only shows that `sum` is an integer.

```coq
Lemma wp_SumN_failed (n: w64) :
  {{{ True }}}
    functional.SumN #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  wp_start as "_".
  wp_alloc sum_l as "sum".
  wp_alloc i_l as "i".
  wp_pures.


```

Supplying loop invariants is a bit of a syntax jumble in Goose. It's things you've seen, but all in one place.

The overall structure here is `wp_apply (wp_forBreak I with "[] [sum i]")`. `wp_forBreak I` just passes the desired invariant to `wp_forBreak`; the lemma works for any invariant, and it can't be guessed from context, so we have to write it down. Due to limitations in Ltac, you need `%I` (a notation scope annotation) for this to be parsed with the separation logic notations, otherwise you'll get an error "Unknown interpretation for notation `_ ∗ _`".

`wp_forBreak` looks like this (somewhat loosely), expanding the continuation passing style and written as math ($I_t$ is `I true` and $I_f$ is `I false`):

$$
% the \phantom{x} below are to get the binary operator spacing around \wand to be correct
\begin{aligned}
& \hoare{I_t}{\mathrm{body} \, ()}{I} \wand \phantom{x} \\
& \forall Φ.\, I_t \wand \phantom{x} \\
& (I_f \wand Φ) \wand \phantom{x} \\
& \wp(\mathrm{For} \, \mathrm{body}, Φ)
\end{aligned}
$$

There are three premises, which you can line up with the obligations for loop invariants: the invariant is preserved by the body, the invariant holds initially, and the rest of the proof assuming the invariant holds (after the loop).

In Coq, `with "[] [sum i]"` is a specialization pattern which decides how the hypothesis should be divided among these three premises. The first one gets nothing (we don't need any of the current facts to prove the loop body's Hoare triple), and the second one gets `"sum"` and `"i"`, since we need the points-to facts for proving the invariant initially. The rest are available for the rest of the proof.

This is a lot to figure out from first principles. You should be able to do so, but it's also fine to use this example as a reference, or see the obligations in Coq and then go back and figure out how to divide up your hypotheses.

```coq
  wp_apply (wp_forBreak
              (λ continue,
                ∃ (sum i: w64),
                  "sum" :: sum_l ↦[uint64T] #sum ∗
                  "i" :: i_l ↦[uint64T] #i)%I
             with "[] [sum i]").
```

:::: info Goals

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  n : w64
  Φ : val → iPropI Σ
  sum_l, i_l : loc
  ============================
  --------------------------------------∗
  {{{ ∃ sum i : w64, "sum" ∷ sum_l ↦[uint64T] #sum ∗ "i" ∷ i_l ↦[uint64T] #i }}}
    (λ: <>,
       if: ![uint64T] #i_l > #n then Break
       else #sum_l <-[uint64T] std.SumAssumeNoOverflow ![uint64T] #sum_l
                                 ![uint64T] #i_l;;
            #i_l <-[uint64T] ![uint64T] #i_l + #(W64 1);; Continue)%V #()
  {{{ (r : bool), RET #r;
      ∃ sum i : w64, "sum" ∷ sum_l ↦[uint64T] #sum ∗ "i" ∷ i_l ↦[uint64T] #i }}}
```

```txt title="goal 2"
  Σ : gFunctors
  hG : heapGS Σ
  n : w64
  Φ : val → iPropI Σ
  sum_l, i_l : loc
  ============================
  "sum" : sum_l ↦[uint64T] #(W64 0)
  "i" : i_l ↦[uint64T] #(W64 1)
  --------------------------------------∗
  ∃ sum i : w64, "sum" ∷ sum_l ↦[uint64T] #sum ∗ "i" ∷ i_l ↦[uint64T] #i
```

```txt title="goal 3"
  Σ : gFunctors
  hG : heapGS Σ
  n : w64
  Φ : val → iPropI Σ
  sum_l, i_l : loc
  ============================
  "HΦ" : ∀ m : w64, ⌜uint.Z m = (uint.Z n * (uint.Z n + 1)) `div` 2⌝ -∗ Φ #m
  --------------------------------------∗
  (∃ sum i : w64, "sum" ∷ sum_l ↦[uint64T] #sum ∗ "i" ∷ i_l ↦[uint64T] #i) -∗
  WP #();; ![uint64T] #sum_l {{ v, Φ v }}
```

::::

```coq
  - (* This goal might look a bit weird: that's because we're proving a Hoare triple as a separation logic `iProp` rather than a `Prop`, hence why it's below a `------*` line (with no separation logic premises). The distinction isn't important for `For` but will be more interesting when we see a proof of a Go higher-order function (that is, a Go function that takes another function as an input). *)
    wp_start as "IH".
    iNamed "IH".
    wp_load.
    wp_pures. wp_if_destruct.
    + iModIntro.
      iApply "HΦ".
      iFrame.
    + wp_load. wp_load.
      wp_apply wp_SumAssumeNoOverflow.
      iIntros (Hoverflow).
      wp_store. wp_load. wp_store.
      iModIntro.
      iApply "HΦ".
      iFrame.
  - iFrame.
  - iIntros "IH". iNamed "IH".
    wp_load.
    iModIntro.
    iApply "HΦ".
    (* oops, didn't prove anything about sum *)
Abort.

```

### Exercise: loop invariant for SumN

What loop invariant does this code maintain that makes the postcondition true? A complete answer should have a loop invariant when continue is true and one when it is false (the two are very similar).

Remember that the loop body needs to satisfy the Hoare triple `{{{ I true }}} body #() {{{ r, RET #r; I r }}}`. The return value `r` is false when the Go code ends with a `break` and true otherwise (either a `continue` or implicitly at the end of the loop body). `I false` is the only thing we will know in the proof after the loop executes.

::: warning

I _strongly_ recommend being fairly confident in your answer before reading the solution. Don't spoil the exercise for yourself!

:::

::: details Solution

Here is a proof with the right loop invariant.

```coq
Lemma wp_SumN (n: w64) :
  {{{ ⌜uint.Z n < 2^64-1⌝ }}}
    functional.SumN #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  wp_start as "%Hn_bound".
  wp_alloc sum_l as "sum".
  wp_alloc i_l as "i".
  wp_pures.
  wp_apply (wp_forBreak
              (λ continue,
                ∃ (sum i: w64),
                  "sum" :: sum_l ↦[uint64T] #sum ∗
                  "i" :: i_l ↦[uint64T] #i ∗
                  "%i_bound" :: ⌜uint.Z i ≤ uint.Z n + 1⌝ ∗
                  "%Hsum_ok" :: ⌜uint.Z sum = (uint.Z i-1) * (uint.Z i) / 2⌝ ∗
              "%Hcontinue" :: ⌜continue = false → uint.Z i = (uint.Z n + 1)%Z⌝)%I
             with "[] [sum i]").
  - wp_start as "IH".
    iNamed "IH".
    wp_load.
    wp_pures. wp_if_destruct.
    + iModIntro.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      split_and!.
      * word.
      * word.
      * intros. word.
    + wp_load. wp_load.
      wp_apply wp_SumAssumeNoOverflow.
      iIntros (Hoverflow).
      wp_store. wp_load. wp_store.
      iModIntro.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      split_and!.
      * word.
      * word.
      * word.
  - iFrame.
    iPureIntro.
    split; word.
  - iIntros "IH". iNamed "IH".
    wp_load.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    rewrite Hsum_ok.
    word.
Qed.

```

:::

### Case study: Binary search

Here is a larger example with a provided loop invariant but not the correctness proof. The code being verified is the following (inspired by [the standard library's sort package](https://go.dev/src/sort/search.go)):

```go
// BinarySearch looks for needle in the sorted list s. It returns (index, found)
// where if found = false, needle is not present in s, and if found = true, s[index]
// == needle.
//
// If needle appears multiple times in s, no guarantees are made about which of
// those indices is returned.
func BinarySearch(s []uint64, needle uint64) (uint64, bool) {
	var i = uint64(0)
	var j = uint64(len(s))
	for i < j {
		mid := i + (j-i)/2
		if s[mid] < needle {
			i = mid + 1
		} else {
			j = mid
		}
	}
	if i < uint64(len(s)) {
		return i, s[i] == needle
	}
	return i, false
}
```

The standard library implementation suggests the following invariant. To relate the more general code for `Find` to `BinarySearch`, use the following relationships:

- `h` in `Find` is `mid` in `BinarySearch`
- The more general `cmp(mid)` becomes the specific comparison function `needle - s[mid]`, so that `cmp(mid) > 0` becomes `s[mid] < needle`.

The suggested invariant is the following:

> Define cmp(-1) > 0 and cmp(n) <= 0.
>
> Invariant: cmp(i-1) > 0, cmp(j) <= 0

Can you see how this invariant relates to the one below? Notice how we had to be much more precise, filling in many missing details above.

A note on Go function names: Go makes a global decision that function calls always use the package name, so other than within the standard library's sort package, the function will be invoked as `sort.Find`. That is how I'll refer to it from now on.

```coq
Definition is_sorted (xs: list w64) :=
  ∀ (i j: nat), (i < j)%nat →
         ∀ (x1 x2: w64), xs !! i = Some x1 →
                  xs !! j = Some x2 →
                  uint.Z x1 < uint.Z x2.

Lemma wp_BinarySearch (s: Slice.t) (xs: list w64) (needle: w64) :
  {{{ own_slice_small s uint64T (DfracOwn 1) xs ∗ ⌜is_sorted xs⌝ }}}
    heap.BinarySearch s #needle
  {{{ (i: w64) (ok: bool), RET (#i, #ok);
      own_slice_small s uint64T (DfracOwn 1) xs ∗
      ⌜ok = true → xs !! uint.nat i = Some needle⌝
  }}}.
Proof.
  wp_start as "[Hs %Hsorted]".
  wp_pures.
  wp_alloc i_l as "i".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  wp_apply (wp_slice_len).
  wp_alloc j_l as "j".
  wp_pures.
  wp_apply (wp_forBreak_cond
           (λ continue, ∃ (i j: w64),
               "Hs" :: own_slice_small s uint64T (DfracOwn 1) xs ∗
               "i" :: i_l ↦[uint64T] #i ∗
               "j" :: j_l ↦[uint64T] #j ∗
               "%Hij" :: ⌜uint.Z i ≤ uint.Z j ≤ Z.of_nat (length xs)⌝ ∗
               "%H_low" :: ⌜∀ (i': nat),
                            i' < uint.nat i →
                            ∀ (x: w64), xs !! i' = Some x →
                                uint.Z x < uint.Z needle⌝ ∗
               "%H_hi" :: ⌜∀ (j': nat),
                            uint.nat j ≤ j' →
                            ∀ (y: w64), xs !! j' = Some y →
                                uint.Z needle < uint.Z y⌝ ∗
               "%Hbreak" ∷ ⌜continue = false → i = j⌝
           )%I
           with "[] [Hs i j]").
  - wp_start as "IH".
    iNamed "IH".
    wp_load. wp_load.
    wp_pures.
    wp_if_destruct.
    + wp_pures.
      wp_load. wp_load. wp_load. wp_pures.
      set (mid := word.add i (word.divu (word.sub j i) (W64 2)) : w64).
      assert (uint.Z mid = (uint.Z i + uint.Z j) / 2) as Hmid_ok.
      { subst mid.
        word. }
      list_elem xs (uint.nat mid) as x_mid.
      wp_apply (wp_SliceGet with "[$Hs]").
      { eauto. }
      iIntros "Hs".
      simpl to_val.
      wp_pures.
      wp_if_destruct.
      * wp_store.
        iModIntro.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        split_and!; try word.
        { intros.
          (* the [revert H] is a bit of black magic here; it [word] operate on H
          by putting it into the goal *)
          assert (i' ≤ uint.nat mid)%nat by (revert H; word).
          admit.
        }
        (* You might ask, why is this super easy? A: we didn't change any relevant variables *)
        eauto.
      * wp_store.
        iModIntro.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        split_and!; try word.
        { auto. }
        admit. (* TODO: fill in based on earlier proof *)
    + iModIntro.
      iApply "HΦ".
      iFrame.
      iPureIntro.
      split_and!; try word; auto.
      intros.
      word.
  - iFrame.
    admit.
  - iIntros "Hpost".
    admit.
Admitted.

```

The standard library implements a more general API than above, since the caller passes in a comparison function. It does not directly assume this comparison function is transitive.

### Exercise: prove the standard library sort.Find

What is Go's `sort.Find` assuming and promising? Translate the prose specification to a Coq predicate. Then, translate the invariant in the implementation to a more formal Coq predicate, similar to what you see in the proof of `BinarySearch`.

Proving the real `sort.Find` with Goose is also a possibility, with minor tweaks to the code due to Goose translation limitations. A tricky part is that `Find` is a higher-order function: it takes a function as an argument. We already saw one such function, `For`, but this was only in GooseLang; now we have to deal with one coming from Go.

```coq
End goose.
```
