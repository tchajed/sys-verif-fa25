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

<!-- @include: ./macros.snippet.md -->

## Loop invariants in theory

The general idea for proving the correctness of a loop is to invent a _loop invariant_, an assertion that is (1) true when the loop starts, and (2) _if_ the loop invariant holds at the start of the loop, it should hold at the end. If you prove these two things, due to an induction argument, you've proven that the loop invariant is true at the end of the loop. That's it; this is the main idea.

In practice, loops have one more complication, which is that they exit when a specific condition is met, so when they terminate we know that condition holds. This is what tells us that the loop ran for the "correct" number of iterations.

Here's the principle of loop invariants stated formally:

$$
\frac{
\hoare{I(\true)}{body \, ()}{\fun{(r: \mathrm{bool})} I(r)}
}{
\hoare{I(\true)}{\mathrm{loop} \, body}{I(\false)}
}
$$

where $\mathrm{loop} \triangleq \rec{f}{body} \ife{body \, ()}{f \, body}{()}$.

This principle we've stated could just be a theorem about the function $\mathrm{loop}$. We could prove it using induction over the number of steps taken by the loop, for example, though such a low-level proof is somewhat complicated.

::: important Main idea

This theorem produces two proof obligations when used:

1. $I$ is preserved by the loop. More precisely the loop gets to assume $I(\true)$ (since the loop continues), and must prove $I(r)$, where $r$ is the continue/break boolean that the body returns.
2. The loop invariant holds initially. More precisely $I(\true)$.

The result is the assertion $I(\false)$, which is used to verify the rest of the code (after the for loop).

:::

## Using loop invariants in practice

The actual principle proven in Perennial is a bit more complicated than what we see above, because it is designed for `for` loops. A `for` loop looks like this:

```
for i := 0; i < 10; i++ {
  body // might use break, continue
}
```

In this code, `i := 0` is an initializer, which simply runs before the whole `for` loop and is unrelated to loop invariants. `i < 10` is a loop condition that is checked at the _beginning_ of each loop iteration, and provides one way for a loop to exit. In the middle of the loop, the code might execute `continue`; this is easy to understand as simply skipping the rest of the loop body. `break` is more complicated to reason about since it is another way for a loop to stop executing, and it means the condition is not guaranteed to be false when the loop exits. Finally, at the end of every loop iteration (unless `break` is called), the post-iteration code `i++` is executed.

While the theorem that handles all of these features is somewhat complicated, using it is pleasantly simple if you understand the idea of loop invariants.

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init functional_init.

Section goose.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

```

For our first example, we'll consider a function that adds the numbers from 1 to $n$. We'll prove this produces $n(n+1)/2$.

Let's first see what this would look like without a `for` loop, using a recursive implementation and an induction argument.

```rocq
Lemma wp_SumNrec (n: w64) :
  {{{ is_pkg_init functional ∗
      ⌜uint.Z n * (uint.Z n + 1) / 2 < 2^64⌝ }}}
    @! functional.SumNrec #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  (* Löb induction is a somewhat magical principle that says we can assume our function is correct while proving it, as long as we only use its correctness for _recursive_ subcalls (to avoid circular reasoning). The intuitive reason why this makes sense is that we only prove partial correctness, so we assume the function terminates. Given that assumption, what we're doing is  induction on the number of steps the function takes to terminate. *)
  iLöb as "IH" forall (n).
  wp_start as "%Hoverflow".
```

:::: info Goal

```txt
  n : w64
  Φ : val → iPropI Σ
  Hoverflow : (uint.Z n * (uint.Z n + 1)) `div` 2 < 2 ^ 64
  ============================
  "IH" : ∀ (n0 : w64) (x : val → iPropI Σ),
           is_pkg_init functional ∗
           ⌜(uint.Z n0 * (uint.Z n0 + 1)) `div` 2 < 2 ^ 64⌝ -∗
           ▷ (∀ m : w64,
                ⌜uint.Z m = (uint.Z n0 * (uint.Z n0 + 1)) `div` 2⌝ -∗ x (# m)) -∗
           WP # (func_callv functional.SumNrec) (# n0) {{ v, x v }}
  _ : is_pkg_init functional
  --------------------------------------□
  "HΦ" : ∀ m : w64,
           ⌜uint.Z m = (uint.Z n * (uint.Z n + 1)) `div` 2⌝ -∗ Φ (# m)
  --------------------------------------∗
  WP exception_do
       (let: "n" := alloc (# n) in
        (if: ![# uint64T] "n" = # (W64 0) then return:
         # (W64 0) else do: # ()) ;;;
        return: ![# uint64T] "n" +
                (let: "$a0" := ![# uint64T] "n" - # (W64 1) in
                 func_call (# functional.SumNrec) "$a0"))
  {{ v, Φ v }}
```

::::

Notice here how Löb induction gives us the correctness of `functional.SumNrec` as an assumption, but the goal is a proof about the body of that function, so `"IH"` is only useful for recursive calls.

```rocq
  wp_auto.
  wp_if_destruct.
  - wp_finish.
  - wp_apply "IH".
    { (* [word] doesn't work on its own here (possibly a bug in the tactic). It's helpful to know how to do some of the work it does manually, to help it along. *)
      rewrite -> !word.unsigned_sub_nowrap by word.
      word. }
    iIntros (m Hm).
    wp_finish.
Qed.

```

### SumN with a loop

Now let's re-implement this function with a loop instead. Here we handle integer overflow differently: the function `std.SumAssumeNoOverflow(x, y)` returns `x + y` and panics if the result would overflow, but in the proof we ignore the overflow case. This introduces an assumption in our whole verified code that this sum never overflows.

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

We'll see that this loop invariant is indeed an invariant: we can prove it holds initially and that it is preserved by the loop. However, it's hopelessly weak for proving that `return sum` is correct after the `for` loop, which we'll fix in the next attempt.

There are two new tactics specific to for loops:

- When the next piece of code in the WP is a for loop, `wp_for` starts verifying it by reasoning about the loop body. It uses the current proof context (whatever hypotheses you currently have) as the loop invariant, so the standard pattern is to _generalize_ with `iAssert` to something weaker that holds throughout the loop. You can see this below.
- `wp_for` produces a statement `for_postcondition` whenever the loop body finishes (either due to `continue` or just by getting to the end), executes a `break` statement, or calls `return`. In each case, the tactic `wp_for_post` transforms that `for_postcondition` into whatever you should prove next: when the loop exits, that's the loop invariant; when the loop breaks, that's verifying the code after the loop; and for a `return` statement that's whatever the postcondition of the outer function is.

```rocq
Lemma wp_SumN_failed (n: w64) :
  {{{ is_pkg_init functional }}}
    @! functional.SumN #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.

  iAssert (∃ (sum i: w64),
              "sum" :: sum_ptr ↦ sum ∗
              "i" :: i_ptr ↦ i)%I
          with "[sum i]" as "HI".
  { iExists (W64 0), (W64 1). iFrame. }

  wp_for.
  iNamed "HI". wp_auto.
  wp_if_destruct.
  - (* the code breaks in this branch, at which point we have to verify the code after the loop *)
    wp_for_post.
    wp_finish.
    iPureIntro.
    (* oops, don't know anything about sum *)
    admit.
  - (* we can prove the loop preserves the loop invariant *)
    wp_apply (wp_SumAssumeNoOverflow).
    iIntros "%Hoverflow".
    wp_auto.
    wp_for_post.
    iFrame.
Abort.

```

### Exercise: loop invariant for SumN

What loop invariant does this code maintain that makes the postcondition true?

::: warning

Take some time to think about this before reading the solution. Don't spoil the exercise for yourself!

:::

::: details Solution

Here is a proof with the right loop invariant. We also show a couple more tricks to make this proof easier.

```rocq
Lemma wp_SumN (n: w64) :
  {{{ is_pkg_init functional ∗ ⌜uint.Z n < 2^64-1⌝ }}}
    @! functional.SumN #n
  {{{ (m: w64), RET #m;
      ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  wp_start as "%Hn_bound".
  wp_auto.

  iAssert (∃ (sum i: w64),
              "sum" :: sum_ptr ↦ sum ∗
              "i" :: i_ptr ↦ i ∗

```

This time around, we'll be precise about what values our local variables take. Note that we can only prove that $i \leq n + 1$ - the loop really does increment `i` one past the end, but then it doesn't increment the sum with `n+1`. Remember these are properties that are true at the beginning of each loop iteration, but don't have to be proven when the loop breaks.

```rocq
              "%i_bound" :: ⌜uint.Z i ≤ uint.Z n + 1⌝ ∗
              "%Hsum_ok" :: ⌜uint.Z sum = (uint.Z i-1) * (uint.Z i) / 2⌝)%I
         with "[$sum $i]" as "HI".
  { iPureIntro. split; word. }

```

If we use named hypotheses (e.g., the `"sum" ::` label above), then passing the name of the "loop invariant hypothesis" to `wp_for` will destruct it back out afterward.

```rocq
  wp_for "HI".
  wp_if_destruct.
  - wp_for_post.
```

:::: info Goal

```txt
  n : w64
  Φ : val → iPropI Σ
  Hn_bound : uint.Z n < 2 ^ 64 - 1
  n_ptr, sum_ptr, i_ptr : loc
  sum, i : w64
  i_bound : uint.Z i ≤ uint.Z n + 1
  Hsum_ok : uint.Z sum = ((uint.Z i - 1) * uint.Z i) `div` 2
  l : uint.Z n < uint.Z i
  ============================
  _ : is_pkg_init functional
  --------------------------------------□
  "HΦ" : ∀ m : w64,
           ⌜uint.Z m = (uint.Z n * (uint.Z n + 1)) `div` 2⌝ -∗ Φ (# m)
  "n" : n_ptr ↦ n
  "sum" : sum_ptr ↦ sum
  "i" : i_ptr ↦ i
  --------------------------------------∗
  Φ (# sum)
```

::::

With this correct loop invariant, notice the extra pure facts we have when the loop `break`s: `i_bound` and `Hsum_ok` come from the loop invariant, and `n < i` comes from the `if` test we just did.

```rocq
    wp_finish.
    iPureIntro.

```

The combination of the invariant and that test guarantee `i = n + 1`.

```rocq
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

Lemma Z_div_le (a b: Z) :
  0 ≤ a →
  0 ≤ b →
  a `div` b ≤ a.
Proof.
  intros H1 H2.
  destruct (decide (b = 0)).
  { subst. rewrite Z.div_0_r_ext //. }
  destruct (decide (b = 1)).
  { subst. rewrite Z.div_1_r //. }
  replace a with (a `div` 1) at 2.
  {
    apply Zdiv_le_compat_l; lia.
  }
  rewrite Z.div_1_r //.
Qed.

Lemma wp_SumN2 (n: w64) :
  {{{ is_pkg_init functional ∗ ⌜0 ≤ sint.Z n < 2^63⌝ }}}
    @! functional.SumN2 #n
  {{{ (m: w64), RET #m;
      ⌜uint.Z m = sint.Z n * (sint.Z n - 1) / 2⌝ }}}.
Proof.
  wp_start as "%Hn_bound".
  wp_auto.

  iAssert (∃ (i sum: w64),
              "i" ∷ i_ptr ↦ i ∗
              "sum" ∷ sum_ptr ↦ sum ∗
              "%Hi_range" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z n⌝ ∗
              "%Hsum" ∷ ⌜uint.Z sum = sint.Z i * (sint.Z i - 1) / 2⌝
          )%I with "[$i $sum]" as "IH".
  { iPureIntro.
    split_and!; try word.
    reflexivity.
  }
  wp_for "IH".
  wp_if_destruct.
  - wp_apply wp_SumAssumeNoOverflow as "%Hsum_i".
    wp_for_post.
    iFrame.
    iPureIntro.
    split; [ word | ].
```

This is much trickier integer arithmetic reasoning than you will encounter in this class. It is due to the automation not handling the multiplication and division in this example well.

```rocq
    rewrite !word.signed_add.
    rewrite swrap_small; [ word | ].
    rewrite word.unsigned_add_nowrap; [ word | ].
    rewrite Hsum.
    replace (sint.Z i) with (uint.Z i) by word.
    change (sint.Z (W64 1)) with 1.
    replace (uint.Z i + 1 - 1) with (uint.Z i) by lia.
    replace ((uint.Z i + 1) * uint.Z i) with
      (uint.Z i * (uint.Z i - 1) + uint.Z i * 2) by lia.
    rewrite Z_div_plus; [ lia | ].
    lia.
  - wp_finish.
    iPureIntro.
    assert (sint.Z i = sint.Z n) by word.
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
                  (* for simplicity, our definition uses strict inequality which guarantees that elements are distinct *)
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

What is Go's `sort.Find` assuming and promising? Translate the prose specification to a Rocq predicate. Then, translate the invariant in the implementation to a more formal Rocq predicate, similar to what you see in the proof of `BinarySearch`.

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
