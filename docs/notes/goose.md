---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 11
shortTitle: "Lecture 11: Goose"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 11: Goose - Modeling and reasoning about Go

> Follow these notes in Coq at [src/sys_verif/program_proof/goose.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/goose.v).

## Learning outcomes

By the end of this lecture, you should be able to:

1. Map from Go to its Goose translation, and back.
2. Explain what is trusted in a proof using Goose.
3. Struggle to come up with loop invariants.

---

## Motivation

So far, we have a way to specify and verify programs, but in a language that is too restrictive and that we can't run. On the other hand, the language is precisely defined so we know what our programs _do_ (by definition) and therefore what the proofs _mean_.

Now we want to turn our attention to executable code. This lecture outlines one way to do this.

The workflow is that we write the code we plan to run in Go, then translate it to an `expr`-like language in Coq, then do the proofs over the translated code. We concretely use a tool called [Goose](https://github.com/goose-lang/goose) that implements this for Go, translating to a language called GooseLang.

## High-level overview

What goes into making the Goose approach work?

First, we need to define GooseLang, the target of the translation. This language will look a lot like our `expr`s, but an important change is that values will be more realistic primitives - for example, we'll replace numbers of type $\mathbb{Z}$ with 64-bit unsigned integers. GooseLang has a precise semantics in the same style as the notes, a relation $(e, h) \leadsto^* (e', h')$ where $h$ is the heap, a (finite) map from locations to values.

Second, we need to translate Go to GooseLang. The basic idea is to translate each Go package to a Coq file, and each Go function to an expression. Go has structs and _methods_ on structs, which will be translated to GooseLang functions that take the struct as the first argument. Some complications we'll have to deal with when we get to the specifics include handling slices (variable-length arrays), concurrency, and loops.

Finally, we will prove useful reasoning principles about GooseLang that make it convenient to reason about the translation.

Of course, you, the reader, don't have to do these things; they're already done in Goose.

Here's a first taste of what this translation looks like:

```go
func Arith(a, b uint64) uint64 {
	sum := a + b
	if sum == 7 {
		return a
	}
	mid := Midpoint(a, b)
	return mid
}
```

translates to:

```coq
Definition Arith: val :=
  rec: "Arith" "a" "b" :=
    let: "sum" := "a" + "b" in
    (if: "sum" = #7
    then "a"
    else
      let: "mid" := Midpoint "a" "b" in
      "mid").
```

An important aspect of Goose (and any verification methodology for "real" code) is to ask, what do the proofs _mean_? Another way to think about this question is, what do we believe a verified specification says about the code, and what tools do we trust to make this happen?

We've already talked about how to interpret specifications in separation logic and won't go further into that part.

Goose _models_ Go code using GooseLang. You can see one evidence of this modeling above: whereas the Go code has a `return` statement to stop executing a function and return to the caller, the `Arith` in Coq (a `val`, which is a GooseLang value) instead is an expression that evaluates to an integer. If you compare the two you can convince yourself for this example that `Arith` in GooseLang, under the expected semantics you learned, evaluates to the same result as `Arith` in Go (assuming `Midpoint` is also translated correctly). When you use Goose to verify a program, you are essentially trusting that every function in that program has been modeled correctly.

## Goose details

### GooseLang

GooseLang has the following features:

- Values can be bytes, 64-bit integers, strings. As before, we have the unit value $()$ and functions as first-class values.
- The Coq implementation has a concrete syntax. Constructs like `λ:`, `rec:`, and `if:` all have a colon to disambiguate them during parsing from similar Coq syntax. Literals have to be explicitly turned into value with `#`, so we write `#true` and `#()` for the boolean true and the unit value. Similarly, `#(W64 1)` represents the 64-bit integer constant 1.
- Allocation supports arrays that get contiguous locations, to model slices.
- The binary operator `ℓ +ₗ n` implements pointer arithmetic: we can take an offset to a location. Allocating an array returns a single location `ℓ`, and loading and storing at `ℓ +ₗ n` accesses the `n`th element of the array.

In addition, GooseLang has some primitives related to concurrency:

- Pointer loads and stores are _non-atomic_ to model weak memory (we won't talk about this in class)
- Fork creates a new thread, used to model the `go f()` statement that spawns a "goroutine" running `f()`.
- A compare-and-exchange operation that is used in the translation of locks.

There are also some features we won't talk about:

- "External" functions and values allow reasoning about code that interacts with a disk, or distributed systems code.
- Prophecy variables, an advanced technique for doing proofs in concurrent separation logic.

### Local variables

Goose models immutable local variables as `let` bindings, while mutable variables are modeled by allocating them on the heap. In Go, it is permitted and safe to take the address of local variables; conceptually, it would be sound to model all variables as being on the heap. The compiler does a simple _escape analysis_: if the analysis proves that a function's address is never used outside the function, then it is instead allocated on the stack (for example, in the common case that the address is never taken).

Goose uses a `let` binding (vs always using a heap variable) only to make the resulting code easier to reason about: the let binding is a pure operation that is handled by substituting the right-hand side, whereas a heap variable (even if constant) would result in a points-to assertion.

Here's an example where Go and Goose both use a heap-allocated local variable.

```go
func StackEscape() *uint64 {
	var x = uint64(42)
	return &x // x has escaped! // [!code highlight]
}
```

```coq
Definition StackEscape: val :=
  rec: "StackEscape" <> :=
    let: "x" := ref_to uint64T #42 in
    "x".
```

One caveat about this "optimization": Goose translates variables declared with `x := ...` as immutable and variables declared as `var x = ...` as mutable; this is not a feature of Go, in which all local variables are mutable. A future version should probably do an analysis of the function rather than using the syntax.

Go also has a construct `new(T)` that allocates a pointer to a value of type `T` and initializes it to the _zero value_ of the type (and every type in Go has a well-defined zero value). Goose also supports this form of allocation, although allocating by taking the address of a heap variable is more common. (For structs, the most common pattern is actually `&S { ... }` - that is, taking the address of a struct literal.)

### Control flow

GooseLang has no special features for control flow. Instead, it must be modeled in the translation. The current translation handles specific, known patterns and is not fully general, thus there are control flow patterns that are not supported (for example, `return` inside a `for` loop). In those cases the translation fails and the developer must rewrite the code to avoid the tricky control flow. A new version of Goose (a significant rewrite) is in progress that will lift most of these limitations.

The `Arith` example above shows how an `if` statement with an early return is translated. Another set of control flow features is related to loops. Here's an example of a loop translation:

```go
// SumN adds up the numbers from 1 to n, with a loop.
func SumN(n uint64) uint64 {
	var sum = uint64(0)
	var i = uint64(1)
	for {
		if i > n {
			break
		}
		sum += i
		i++
	}
	return sum
}
```

```coq
Definition SumN: val :=
  rec: "SumN" "n" :=
    let: "sum" := ref_to uint64T #0 in
    let: "i" := ref_to uint64T #1 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (![uint64T] "i") > "n"
      then Break
      else
        "sum" <-[uint64T] ((![uint64T] "sum") + (![uint64T] "i"));;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    ![uint64T] "sum".
```

The (GooseLang) syntax `for:` is a very thin Notation around the following _model_ of (Go) `for` loops:

```coq
Definition For: val :=
  λ: "cond" "body" "post",
  (rec: "loop" <> :=
     let: "continue" :=
        (if: "cond" #()
         then "body" #()
         else #false) in
     if: "continue"
     then "post" #();; "loop" #()
     else #()) #().
```

The Go code `for init; cond; post { body }` is translated (roughly) into `init;; For cond body post`. (Unfortunately this isn't the order of arguments of the notation, which goes `for: cond ; post := body`. The function `For` should be fixed.)

`For` takes three _functions_ as arguments (making it a so-called _higher-order function_): cond, body, and post. You can think of it as having the type `For : (unit -> bool) -> (unit -> unit) -> (unit -> unit) -> unit`, where `#() : unit` is the unit value in GooseLang. (You are welcome to think about these types but we don't actually have a type system for GooseLang, so it's only in your imagination.)

You might be confused by the `unit` argument each function takes: this is sometimes called a _thunk_ and is needed to prevent evaluating the condition, body, and post until they are needed in the loop. For example, if for the `cond` we passed a `bool` rather than a `unit -> bool` it would be a constant throughout the entire loop. A function that takes a unit isn't evaluated until desired by passing the argument.

::: info Exercise

Check your understanding: does the `cond` return `true` when the loop should stop or keep going? Try to figure out how this follows from the definition of `For`, not just your expectations.

Next, do you believe this is a correct model of `for` loops?

:::

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

### Exercise (difficult, especially useful)

The informal description above describes a "continue condition" and "break condition", but that is not how `wp_forBreak` is written. In this exercise you'll bridge the gap.

1. Reformulate `wp_forBreak` so that it takes a regular loop invariant and a break condition as separate arguments, to more closely match the principle above. That, state a different theorem (let's call it `wp_for_breakCondition`) for proving a specification about that same expression `(for: (λ: <>, #true)%V ; (λ: <>, Skip)%V := body)`.
2. Prove your new `wp_for_breakCondition` using `wp_forBreak`. You should replace the `-∗` in the theorem statement with a `→` (we will discuss what difference this creates later when we talk about something called the _persistently modality_).

## Proofs with Goose

This section shows some examples of specifications and proofs.

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From Perennial.program_proof Require Import std_proof.
From Goose.sys_verif_code Require heap functional.

#[local] Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section goose.
Context `{hG: !heapGS Σ}.

```

Code being verified:

```go
func Add(a uint64, b uint64) uint64 {
	return a + b
}
```

```coq
Lemma wp_Add (n m: w64) :
  {{{ ⌜uint.Z n + uint.Z m < 2^64⌝ }}}
    functional.Add #n #m
  {{{ (y: w64), RET #y; ⌜(uint.Z y = uint.Z n + uint.Z m)%Z⌝ }}}.
Proof.
  wp_start as "%Hoverflow".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iPureIntro.
  word.
Qed.

```

Code being verified:

```go
func StackEscape() *uint64 {
	var x = uint64(42)
	return &x
}
```

```coq
Lemma wp_StackEscape :
  {{{ True }}}
    heap.StackEscape #()
  {{{ (l: loc), RET #l; l ↦[uint64T] #(W64 42) }}}.
Proof.
  wp_start as "_".
  wp_alloc x as "x".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

```

Code being verified

```go
// SumNrec adds up the numbers from 1 to n, recursively.
func SumNrec(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return n + SumNrec(n-1)
}
```

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
    rewrite word.unsigned_add_nowrap.
    + rewrite Hm.
      word.
    + rewrite Hm. word.
Qed.

```

The proof below has a minimal loop invariant that shows that the heap loads and stores work, but nothing about the values of the `sum` and `i` variables.

### Exercise: loop invariant for SumN

What loop invariant does this code maintain that makes the postcondition true? A complete answer should have a loop invariant when continue is true and one when it is false (the two are very similar).

Remember that the loop body needs to satisfy the Hoare triple `{{{ I true }}} body #() {{{ r, RET #r; I r }}}`. The return value `r` is true when the loop will execute one more iteration and false when it is done and will immediately terminate, so `I false` is the only thing we will know in the proof after the loop executes.

::: warning

I _strongly_ recommend being fairly confident in your answer before reading the solution. Don't spoil the exercise for yourself!

:::

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
  wp_apply (wp_forBreak
              (λ continue,
                ∃ (sum i: w64),
                  "sum" :: sum_l ↦[uint64T] #sum ∗
                    "i" :: i_l ↦[uint64T] #i)%I
             with "[] [sum i]").
  - wp_start as "IH".
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

Here is a larger example with a provided loop invariant but not the correctness proof. The code being verified is the following (inspired by <https://go.dev/src/sort/search.go>):

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

The source for this example suggests the following invariant. To relate the more general code for `Find` to `BinarySearch`, use the following relationships:

- `h` in the original is `mid` in `BinarySearch`
- `cmp(mid)` is what we would write `needle - s[mid]`, so that `cmp(mid) > 0` is `s[mid] < needle`.

The suggested invariant is the following:

> Define cmp(-1) > 0 and cmp(n) <= 0.
>
> Invariant: cmp(i-1) > 0, cmp(j) <= 0

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

End goose.

```

## Implementation

The Goose translation uses [go/ast](https://pkg.go.dev/go/ast) and [go/types](https://pkg.go.dev/go/types) for parsing, type checking, and resolving references (e.g., which function is being called?). Using these official packages reduces chance of bugs, and allows us to rely on types; writing a type inference engine for Go from scratch would be a daunting task, and would be much less trustworthy than the official package. (This package is not literally the one used by the `go` binary, but it is very close. You can read more about the situation by looking at the [`internal/types2`](https://cs.opensource.google/go/go/+/master:src/cmd/compile/internal/types2/README.md) documentation. If you're confused about something in Go, there's a higher than usual chance you can find the answer in the source code.)

Goose is tested at several levels:

- "Golden" outputs help check if translation changes (e.g., if adding a feature, that unrelated inputs aren't affected).
- "Semantics" tests run the same code in Go and GooseLang, using an interpreter for GooseLang.
- Tests of the user interface - package loading, for example.
- Continuously check that the code we're verifying matches what Goose is outputting, to avoid using stale translations.

The semantics tests - a form of _differential testing_ - is one of the most valuable parts of this process. For an example, see [shortcircuiting.go](https://github.com/goose-lang/goose/blob/585abc3cfef50dd466e112d7c535dbdfccd3c0ca/internal/examples/semantics/shortcircuiting.go). The test `testShortcircuitAndTF`, for example, is designed to return `true` in Go. The goose test infrastructure (a) checks that it actually returns true in Go, (b) translates it to GooseLang, and (c) executes it with an interpreter written in Coq for GooseLang and confirms this produces `#true`. Furthermore, the interpreter is verified to ensure that it matches the semantics, so we don't have to trust its implementation for our differential testing.

## What does a proof mean?

You might wonder, what do proofs mean? They must depend on Goose being correct. This is indeed the case, but we can be more precise about what "correct" means (and we should be since this is a verification class).

For a Go program $p$ let $\mathrm{goose}(p)$ be the Goose output on that program. We said $\mathrm{goose}(p)$ should "model" $p$, but what does that mean?

Goose is actually implicitly giving a _semantics_ to every Go program it translates, call it $\mathrm{semantics}(\mathrm{goose}(p))$ (where that semantics is whatever the $(e, h) \leadsto^* (e', h')$ relation says). For Goose proofs to be sound, we need the real execution from running $p$, call it $\mathrm{behavior}(p)$, to satisfy

$$\mathrm{behavior}(p) \subseteq \mathrm{semantics}(\mathrm{goose}(p))$$

The reason this is the direction of the inequality is that the proofs will show that every execution in $\mathrm{semantics}(\mathrm{goose}(p))$ satisfy some specification, and in that case this inclusion guarantees that all the real executable behaviors are also "good", even if the semantics has some extra behaviors. On the other hand it would not be ok to verify a _subset_ of the behaviors of a program since one of the excluded behaviors could be exactly the kind of bug you wanted to avoid.

If translation does not work, sound (can't prove something wrong) but not a good developer experience. Failure modes: does not translate, does not compile in Coq, compiles but GooseLang code is always undefined.

This correctness criteria for Goose makes it easier to understand why the implementation would want the official typechecker and not some other version: whatever the meaning of a Go program, we want the Goose understanding to match the Go compiler's understanding. If they both don't match the reference manual, or if the reference manual is ambiguous, that doesn't affect Goose's correctness.
