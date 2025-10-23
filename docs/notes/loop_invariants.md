---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture-note
tags: literate
order: 13
shortTitle: "Loop invariants"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Loop invariants

> Follow these notes in Rocq at [src/sys_verif/notes/loop_invariants.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/loop_invariants.v).

## Learning outcomes

By the end of this lecture, you should be able to:

1. Recall the obligations for a loop invariant to be correct.
2. Struggle to come up with loop invariants for examples.

---

## Loop invariants

The general idea for proving the correctness of a loop is to invent a _loop invariant_, an assertion that is (1) true when the loop starts, and (2) _if_ the loop invariant holds at the start of the loop, it should hold at the end. If you prove these two things, via induction, you've proven that the loop invariant is true at the end of the loop. We also can learn one more fact which is necessary in practice: the loop probably has a "break condition", a property that is true when it terminates. We know the loop invariant is preserved by each iteration, and if the loop exits it satisfies the break condition.

Here's the principle of loop invariants stated formally, for the `for` loop model above. This is a theorem in Perennial (slightly simplified).

```rocq
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

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init functional_init.

#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section goose.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

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

```rocq
Lemma wp_SumNrec (n: w64) :
  {{{ is_pkg_init functional ∗
      ⌜uint.Z n * (uint.Z n + 1) / 2 < 2^64⌝ }}}
    @! functional.SumNrec #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  iLöb as "IH" forall (n).
  wp_start as "%Hoverflow".
  wp_auto.
  wp_if_destruct.
  - wp_finish.
  - wp_apply "IH".
    { (* [word] doesn't work on its own here. It's helpful to know how to do some of the work it does manually, to help it along. *)
      (* FIXME: word bug? *)
      rewrite -> !word.unsigned_sub_nowrap by word.
      word. }
    iIntros (m Hm).
    wp_finish.
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

```rocq
Lemma wp_SumN_failed (n: w64) :
  {{{ is_pkg_init functional }}}
    @! functional.SumN #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  (* n doesn't change, so persist its points-to assertion *)
  iPersist "n".


```

TODO: describe the new way we supply loop invariants.

```rocq
  iAssert (∃ (sum i: w64),
              "sum" :: sum_ptr ↦ sum ∗
              "i" :: i_ptr ↦ i)%I
          with "[$sum $i]" as "HI".
  wp_for "HI".
  wp_if_destruct.
  - iApply wp_for_post_break.
    wp_auto.
    wp_finish.
    iPureIntro.
    (* oops, don't know anything about sum *)
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

```rocq
Lemma wp_SumN (n: w64) :
  {{{ is_pkg_init functional ∗ ⌜uint.Z n < 2^64-1⌝ }}}
    @! functional.SumN #n
  {{{ (m: w64), RET #m;
      ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  wp_start as "%Hn_bound".
  wp_auto.
  iPersist "n".

  iAssert (∃ (sum i: w64),
              "sum" :: sum_ptr ↦ sum ∗
              "i" :: i_ptr ↦ i ∗
              "%i_bound" :: ⌜uint.Z i ≤ uint.Z n + 1⌝ ∗
              "%Hsum_ok" :: ⌜uint.Z sum = (uint.Z i-1) * (uint.Z i) / 2⌝)%I
         with "[$sum $i]" as "HI".
  { iPureIntro. split; word. }
  wp_for "HI".
  wp_if_destruct.
  - wp_for_post.
    wp_finish.
    iPureIntro.
    assert (uint.Z i = (uint.Z n + 1)%Z) by word.
    word.
  - wp_apply wp_SumAssumeNoOverflow.
    iIntros (Hoverflow).
    wp_auto.
    wp_for_post.
    iFrame.
    iPureIntro.
    split_and!; try word.
    rewrite -> !word.unsigned_add_nowrap by word.
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

```rocq
Definition is_sorted (xs: list w64) :=
  ∀ (i j: nat), (i < j)%nat →
         ∀ (x1 x2: w64), xs !! i = Some x1 →
                  xs !! j = Some x2 →
                  uint.Z x1 < uint.Z x2.

Lemma wp_BinarySearch (s: slice.t) (xs: list w64) (needle: w64) :
  {{{ is_pkg_init heap.heap ∗
        s ↦* xs ∗ ⌜is_sorted xs⌝ }}}
    @! heap.heap.BinarySearch #s #needle
  {{{ (i: w64) (ok: bool), RET (#i, #ok);
      s ↦* xs ∗
      ⌜ok = true → xs !! sint.nat i = Some needle⌝
  }}}.
Proof.
  wp_start as "[Hs %Hsorted]".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hsz.
  iPersist "needle s".

  iAssert (
      ∃ (i j: w64),
               "Hs" :: s ↦* xs ∗
               "i" :: i_ptr ↦ i ∗
               "j" :: j_ptr ↦ j ∗
               "%Hij" :: ⌜0 ≤ sint.Z i ≤ sint.Z j ≤ Z.of_nat (length xs)⌝ ∗
               "%H_low" :: ⌜∀ (i': nat),
                            i' < sint.nat i →
                            ∀ (x: w64), xs !! i' = Some x →
                                uint.Z x < uint.Z needle⌝ ∗
               "%H_hi" :: ⌜∀ (j': nat),
                            sint.nat j ≤ j' →
                            ∀ (y: w64), xs !! j' = Some y →
                                uint.Z needle ≤ uint.Z y⌝
    )%I with "[Hs i j]" as "HI".
  { iFrame. iPureIntro.
    split_and!.
    - word.
    - word.
    - intros. word.
    - intros ??? Hget.
      apply lookup_lt_Some in Hget.
      word.
    - intros ??? Hget.
      apply lookup_lt_Some in Hget.
      word.
  }
  wp_for "HI".
  - wp_if_destruct.
    + wp_pure.
      { rewrite word.signed_add.
        rewrite Automation.word.word_signed_divs_nowrap_pos; [ word | ].
        word. }
      set (mid := word.add i (word.divs (word.sub j i) (W64 2)) : w64).
      assert (sint.Z mid = (sint.Z i + sint.Z j) / 2) as Hmid_ok.
      { subst mid.
        rewrite word.signed_add.
        rewrite Automation.word.word_signed_divs_nowrap_pos; [ word | ].
        word. }
      list_elem xs (sint.nat mid) as x_mid.
      wp_apply (wp_load_slice_elem with "[$Hs]") as "Hs".
      { word. }
      { eauto. }
      wp_if_destruct.
      * wp_for_post.
        iFrame.
        iPureIntro.
        split_and!; try word.
        { intros.
          (* the [revert H] is a bit of black magic here; it [word] operate on H
          by putting it into the goal *)
          assert (i' ≤ sint.nat mid)%nat by (revert H; word).
          (* handle the equal case specially (we need a strict inequality to
          make use of [is_sorted]) *)
          destruct (decide (i' = sint.nat mid)).
          { subst.
            assert (x = x_mid) by congruence; subst.
            assumption. }
          assert (i' < sint.nat mid)%nat as Hi'_lt by word.
          assert (uint.Z x < uint.Z x_mid).
          { apply (Hsorted i' (sint.nat mid)); auto; word. }
          lia.
        }
        (* This is easy because we didn't change any relevant variables *)
        eauto.
      * wp_for_post.
        iFrame.
        iPureIntro.
        split_and!; try word.
        { auto. }
        intros.
        destruct (decide (j' = sint.nat mid)).
        { subst.
          assert (y = x_mid) by congruence; subst.
          word. }
        assert (sint.nat mid < j') as Hj'_gt by word.
        assert (uint.Z x_mid < uint.Z y).
        { apply (Hsorted (sint.nat mid) j'); auto; word. }
        lia.
    + wp_if_destruct.
      * list_elem xs (sint.nat i) as x_i.
        wp_pure.
        { word. }
        wp_apply (wp_load_slice_elem with "[$Hs]") as "Hs".
        { word. }
        { eauto. }
        wp_finish.
        iFrame.
        iPureIntro.
        intros Heq.
        apply bool_decide_eq_true_1 in Heq. subst.
        auto.
      * wp_finish.
Qed.

```

The standard library implements a more general API than above, since the caller passes in a comparison function. It does not directly assume this comparison function is transitive.

### Exercise: prove the standard library sort.Find

What is Go's `sort.Find` assuming and promising? Translate the prose specification to a Coq predicate. Then, translate the invariant in the implementation to a more formal Coq predicate, similar to what you see in the proof of `BinarySearch`.

Proving the real `sort.Find` with Goose is also a possibility, with minor tweaks to the code due to Goose translation limitations. A tricky part is that `Find` is a higher-order function: it takes a function as an argument. We already saw one such function, `For`, but this was only in GooseLang; now we have to deal with one coming from Go.

### Ownership in iterators

Let's revisit the idea of ownership in the context of a loop. Consider a hashmap with an iteration API that looks like this:

```go
func PrintKeys(m HashMap) {
  it := m.KeyIterator()
  for k, ok := it.Next(); ok {
      fmt.Println(k)
  }
}
```

That is, we have an API like this (where `Key` is a placeholder for the key type):

```go
// normal operations:
func (m HashMap) Get(k Key) (v Value, ok bool)
func (m HashMap) Put(k Key, v Value)
func (m HashMap) Delete(k Key)

// iteration:
func (m HashMap) KeyIterator() *Iterator
func (it *Iterator) Next() (k Key, ok bool)
```

Given this API, is this safe?

```go
// does this work?

func PrintValues(m HashMap) {
  it := m.KeyIterator()
  for k, ok := it.Next(); ok {
      v, _ := m.Get(k)
      fmt.Println(v)
  }
}
```

What about this one?

```go
// does this work?

func ClearMap(m HashMap) {
  it := m.KeyIterator()
  for k, ok := it.Next(); ok {
      m.Delete(k)
  }
}
```

::: details Solution

You can't tell from just the API (which does not even describe ownership in comments). For most hashmap implementations, the iterator should be considered to _own_ read-only permission on the entire hashmap. This means that `PrintValues` is safe, but `ClearMap` is not. This problem is often called _iterator invalidation_ since the call to `m.Delete(k)` is considered to _invalidate_ `it` in the next iteration.

:::

```rocq
End goose.
```
