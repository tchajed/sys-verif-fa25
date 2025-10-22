---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture-note
tags: literate
shortTitle: "Goose"
order: 11
date: 2025-10-16 8:00:00 -5
pageInfo: ["Date", "Category", "Tag", "Word"]
---

```rocq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init functional_init.

Section goose.
Context `{hG: !heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

```

# Goose - Modeling and reasoning about Go

> Follow these notes in Rocq at [src/sys_verif/notes/goose.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/notes/goose.v).

## Learning outcomes

By the end of this lecture, you should be able to:

1. Map from Go to its Goose translation, and back.
2. Explain what is trusted in a proof using Goose.

---

## Motivation

So far, we have a way to specify and verify programs, but in a language that is too restrictive and that we can't run. On the other hand, the language is precisely defined so we know what our programs _do_ (by definition) and therefore what the proofs _mean_.

Now we want to turn our attention to executable code. This lecture outlines one way to do this.

The workflow is that we write the code we plan to run in Go, then translate it to an `expr`-like language in Rocq, then do the proofs over the translated code. We concretely use a tool called [Goose](https://github.com/goose-lang/goose) that implements this for Go, translating to a language called GooseLang.

::: tip

While you won't have to _write_ Go for this class, it helps to be able to _read_ it. Luckily it's a fairly simple language to learn if you know how to program already. You should spend a few minutes reading the [Tour of Go](https://go.dev/tour/list). For this class, the Basics section and Methods and Interfaces are plenty.

:::

## High-level overview

What goes into making the Goose approach work?

First, we define GooseLang, the target of the translation. GooseLang will be defined in Rocq. The language will look a lot like our `expr`s, but an important change is that values will be more realistic primitives - for example, we'll replace numbers of type $\mathbb{Z}$ with 64-bit unsigned integers. GooseLang has a precise semantics in the same style as the notes, although defined in Rocq: `expr` is an inductive type, and the semantics is given as a relation $(e, h) \leadsto^* (e', h')$ where $h$ is the heap, a (finite) map from locations to values.

Second, we need to translate Go to GooseLang. The basic idea is to translate each Go package to a Rocq file, and each Go function to an expression. Go has structs and _methods_ on structs, which will be translated to GooseLang functions that take the struct as the first argument. Some complications we'll have to deal with when we get to the specifics include handling control flow (`if`, `return`), slices, loops, and concurrency.

Third, we define a separation logic over the GooseLang syntax and semantics, for proving properties of the translated code. As part of this separation logic we also prove all the usual rules (such as the rule of consequence and the frame rule) as lemmas.

Finally, we provide good reasoning principles for verifying the translated code. The translation often uses libraries implemented in GooseLang to model some aspect of Go - for example, control flow - and we provide specifications and proofs for the library code that the user will use for their proofs.

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

```rocq
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

Goose _models_ Go code using GooseLang. You can see one evidence of this modeling above: whereas the Go code has a `return` statement to stop executing a function and return to the caller, the `Arith` in Rocq (a `val`, which is a GooseLang value) instead is an expression that evaluates to an integer. If you compare the two you can convince yourself for this example that `Arith` in GooseLang, under the expected semantics you learned, evaluates to the same result as `Arith` in Go (assuming `Midpoint` is also translated correctly). When you use Goose to verify a program, you are essentially trusting that every function in that program has been modeled correctly.

## Goose details

### GooseLang

GooseLang has the following features:

- Values can be bytes, integers (64, 32, or 16-bit), booleans, strings, and pointers. As before, we have the unit value $()$ and functions as first-class values.
- The Rocq implementation has a concrete syntax. Constructs like `λ:`, `rec:`, and `if:` all have a colon to disambiguate them during parsing from similar Rocq syntax. Literals have to be explicitly turned into value with `#`, so we write `#true` and `#()` for the boolean true and the unit value. Similarly, `#(W64 1)` represents the 64-bit integer constant 1.
- Allocation supports arrays that get contiguous locations, to model slices.
- The binary operator `ℓ +ₗ n` implements pointer arithmetic: we can take an offset to a location. Allocating an array returns a single location `ℓ`, and loading and storing at `ℓ +ₗ n` accesses the `n`th element of the array. Structs are laid out with their fields contiguously in memory, so that we can use pointer arithmetic to get a pointer to an individual field.

In addition, GooseLang has a Fork operation to create a concurrent thread, used to model the `go f()` statement that spawns a "goroutine" running `f()`.

There are also some features we won't talk about:

- "External" functions and values allow reasoning about code that interacts with a disk, or distributed systems code.
- Prophecy variables, an advanced technique for doing proofs in concurrent separation logic.

### Local variables

Goose models all local variables as being on the GooseLang heap. On the other hand, the Go compiler does a simple _escape analysis_: if the analysis proves that a function's address is never used outside the function, then it is instead allocated on the stack (for example, in the common case that the address is never taken). However, it is sound to think of all local variables as being on the heap; stack allocation is just a performance optimization.

Here's an example of this happening in Go:

```go
func StackEscape() *int {
	x := 42
	return &x // x has escaped! // [!code highlight]
}
```

```rocq
Definition StackEscapeⁱᵐᵖˡ : val :=
  λ: <>,
    exception_do (let: "x" := (mem.alloc (type.zero_val #intT)) in
    let: "$r0" := #(W64 42) in
    do:  ("x" <-[#intT] "$r0");;;
    return: ("x")).
```

The key to note here is that `x` is allocated on the heap and then returned.

Go also has a construct `new(T)` that allocates a pointer to a value of type `T` and initializes it to the _zero value_ of the type (and every type in Go has a well-defined zero value). Goose also supports this form of allocation. (For structs, it's typical to write `&S { ... }` to allocate a pointer - that is, taking the address of a struct literal.)

Function parameters are also allocated on the heap, since in Go they are treated as mutable local variables. The way this works is that the values of the parameters are passed to a GooseLang function (that is, the construct with the syntax `λ: "x", ...`), and the function body immediately stores them on the heap. We can see this in the translation of this function:

```go
func Add(a uint64, b uint64) uint64 {
	return a + b
}
```

```rocq
Definition Addⁱᵐᵖˡ : val :=
  λ: "a" "b",
    exception_do (let: "b" := (mem.alloc "b") in
    let: "a" := (mem.alloc "a") in
    return: ((![#uint64T] "a") + (![#uint64T] "b"))).
```

The variables `"a"` and `"b"` are immediately shadowed by pointers to their heap locations. As a result, when they are referenced later they have to be loaded with `![#uint64T] "a"` and `![#uint64T]  "b"`. These loads have a type annotation, which you can largely ignore as a user; we'll see what purpose it serves when talking about the model of structs.

### Control flow

Control flow features are modeled using the primitives of first-class functions and tuples. These use a variety of definitions and notations, implemented in the "GoLang" layer on top of GooseLang in the Perennial codebase.

The `Arith` example shows how control flow is translated:

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

```rocq
Definition Arithⁱᵐᵖˡ : val :=
  λ: "a" "b",
    exception_do (let: "b" := (mem.alloc "b") in
    let: "a" := (mem.alloc "a") in
    let: "sum" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := ((![#uint64T] "a") + (![#uint64T] "b")) in
    do:  ("sum" <-[#uint64T] "$r0");;;
    (if: (![#uint64T] "sum") = #(W64 7)
    then return: (![#uint64T] "a")
    else do:  #());;;
    let: "mid" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := (let: "$a0" := (![#uint64T] "a") in
    let: "$a1" := (![#uint64T] "b") in
    (func_call #Midpoint) "$a0" "$a1") in
    do:  ("mid" <-[#uint64T] "$r0");;;
    return: (![#uint64T] "mid")).
```

Note the `exception_do` wrapper, which is used to implement the control flow for function returns: a `return: e` expression inside will return early, preventing execution of code afterward. On the other hand `do: e` will run as normal and proceed to the next line. This sequencing-with-return is implemented by `;;;`, which is _not_ the same as the usual sequencing `;;`.

As a user, the implementation of these control flow constructs is largely invisible. In proofs, `wp_pures` (which is called by `wp_auto`) will "step" over control flow as needed. `wp_apply` will work inside the `exception_do` wrapper. If you want an idea of the semantics of these operations, see the comments in Perennial's [defn/exception.v](https://github.com/mit-pdos/perennial/blob/master/new/golang/defn/exception.v).

Next this code allocates `"a"` and `"b"` on the heap, as we saw in the previous example.

From there we see a more straightforward correspondence between the Go and the translation. Notice that the `if` has no else branch in Go, but it does have `do: #()` in GooseLang since we always need both branches.

The call to `Midpoint` becomes `func_call #Midpoint $a0 $a1`. What this actually does is look up the code for Midpoint by its name (`Midpoint` is just the full Go path to the function followed by the string "Midpoint") and then call it. The level of indirection is needed to allow recursion, both for one function to call itself and for multiple top-level functions to call each other. As a user of Goose, you can largely ignore this complication: we will state all separation logic triples to be about `func_call` of a function, and `wp_start` handles resolving the function call to the function's code.

Another set of control flow features is related to loops. Here's an example of a loop translation:

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

```rocq
Definition SumNⁱᵐᵖˡ : val :=
  λ: "n",
    exception_do (let: "n" := (mem.alloc "n") in
    let: "sum" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 0) in
    do:  ("sum" <-[#uint64T] "$r0");;;
    let: "i" := (mem.alloc (type.zero_val #uint64T)) in
    let: "$r0" := #(W64 1) in
    do:  ("i" <-[#uint64T] "$r0");;;
    (for: (λ: <>, #true); (λ: <>, #()) := λ: <>,
      (if: (![#uint64T] "i") > (![#uint64T] "n")
      then break: #()
      else do:  #());;;
      let: "$r0" := (let: "$a0" := (![#uint64T] "sum") in
      let: "$a1" := (![#uint64T] "i") in
      (func_call #std.SumAssumeNoOverflow) "$a0" "$a1") in
      do:  ("sum" <-[#uint64T] "$r0");;;
      do:  ("i" <-[#uint64T] ((![#uint64T] "i") + #(W64 1))));;;
    return: (![#uint64T] "sum")).
```

The complexity here is mostly hidden by the `for:` syntax, which picks up the `break: #()` and appropriately stops looping at that point. There is no loop condition, hence why `(λ: <>, #true)` appears as the first argument to `for:`. If you want to see the implementation of loops, you can read it in [defn/loop.v](https://github.com/mit-pdos/perennial/blob/master/new/golang/defn/loop.v). The best place to start is `do_loop`, which models the simplest loop, `for { ... }`, which has no initializer, condition, or post-expression:

```rocq
Definition do_loop_def: val :=
  λ: "body",
  (rec: "loop" <> := exception_do (
     let: "b" := "body" #() in
     if: Fst "b" = #"break" then (return: (do: #())) else (do: #()) ;;;
     if: (Fst "b" = #"continue") || (Fst "b" = #"execute")
          then (return: "loop" #()) else do: #() ;;;
     return: "b"
  )) #().
```

The loop body might produce `break: #()` or `continue: #()`, which get returned in `"b"`. The loop definition handles a `break` by stopping the entire loop. A `continue` doesn't need special handling; its role is to halt execution of the body, which is already handled by `;;;` inside the body.

## Proofs with Goose

This section shows some examples of specifications and proofs.

Code being verified:

```go
func Add(a uint64, b uint64) uint64 {
	return a + b
}
```

You will see `is_pkg_init <pkg>` in all preconditions for functions and methods. This asserts that the package (`functional` in this case) for the relevant function has been initialized. We need this precondition because initialization is where the code for `functional.Add` (the `Addⁱᵐᵖˡ` expression) is stored in a global variable where it is accessed by `func_call`. `wp_start` knows how to handle `is_pkg_init` and automatically puts it in the right place, so you don't mention it in the intro pattern passed to `wp_start`.

```rocq
Lemma wp_Add (n m: w64) :
  {{{ is_pkg_init functional ∗ ⌜uint.Z n + uint.Z m < 2^64⌝ }}}
    @! functional.Add #n #m
  {{{ (y: w64), RET #y; ⌜(uint.Z y = uint.Z n + uint.Z m)%Z⌝ }}}.
Proof.
  wp_start as "%Hoverflow".
  wp_auto.
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

```rocq
Lemma wp_StackEscape :
  {{{ is_pkg_init heap.heap }}}
    @! heap.heap.StackEscape #()
  {{{ (l: loc), RET #l; l ↦ (W64 42) }}}.
Proof.
  wp_start as "#init". iNamed "init".
  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

End goose.

```

## Implementation

The Goose translation uses [go/ast](https://pkg.go.dev/go/ast) and [go/types](https://pkg.go.dev/go/types) for parsing, type checking, and resolving references (e.g., which function is being called?). Using these official packages reduces chance of bugs, and allows us to rely on types; writing a type inference engine for Go from scratch would be a daunting task, and would be much less trustworthy than the official package. (This package is not literally the one used by the `go` binary, but it is very close. You can read more about the situation by looking at the [`internal/types2`](https://cs.opensource.google/go/go/+/master:src/cmd/compile/internal/types2/README.md) documentation. If you're confused about something in Go, there's a higher than usual chance you can find the answer in the source code.)

Goose is tested at several levels:

- "Golden" outputs help check if translation changes (e.g., if adding a feature, that unrelated inputs aren't affected).
- "Semantics" tests run the same code in Go and GooseLang, using an interpreter for GooseLang.
- Tests of the user interface - package loading, for example.
- Continuously check that the code we're verifying matches what Goose is outputting, to avoid using stale translations.

The semantics tests - a form of _differential testing_ - is one of the most valuable parts of this process. For an example, see [shortcircuiting.go](https://github.com/goose-lang/goose/blob/585abc3cfef50dd466e112d7c535dbdfccd3c0ca/internal/examples/semantics/shortcircuiting.go). The test `testShortcircuitAndTF`, for example, is designed to return `true` in Go. The goose test infrastructure (a) checks that it actually returns true in Go, (b) translates it to GooseLang, and (c) executes it with an interpreter written in Rocq for GooseLang and confirms this produces `#true`. Furthermore, the interpreter is verified to ensure that it matches the semantics, so we don't have to trust its implementation for our differential testing.

## What does a proof mean?

You might wonder, what do proofs mean? They must depend on Goose being correct. This is indeed the case, but we can be more precise about what "correct" means (and we should be since this is a verification class).

For a Go program $p$ let $\mathrm{goose}(p)$ be the Goose output on that program. We said $\mathrm{goose}(p)$ should "model" $p$, but what does that mean?

Goose is actually implicitly giving a _semantics_ to every Go program it translates, call it $\mathrm{semantics}(\mathrm{goose}(p))$ (where that semantics is whatever the $(e, h) \leadsto^* (e', h')$ relation says). For Goose proofs to be sound, we need the real execution from running $p$, call it $\mathrm{behavior}(p)$, to satisfy

$$\mathrm{behavior}(p) \subseteq \mathrm{semantics}(\mathrm{goose}(p))$$

The reason this is the direction of the inequality is that the proofs will show that every execution in $\mathrm{semantics}(\mathrm{goose}(p))$ satisfy some specification, and in that case this inclusion guarantees that all the real executable behaviors are also "good", even if the semantics has some extra behaviors. On the other hand it would not be ok to verify a _subset_ of the behaviors of a program since one of the excluded behaviors could be exactly the kind of bug you wanted to avoid.

If translation does not work, sound (can't prove something wrong) but not a good developer experience. Failure modes: does not translate, does not compile in Rocq, compiles but GooseLang code is always undefined.

This correctness criteria for Goose makes it easier to understand why the implementation would want the official typechecker and not some other version: whatever the meaning of a Go program, we want the Goose understanding to match the Go compiler's understanding. If they both don't match the reference manual, or if the reference manual is ambiguous, that doesn't affect Goose's correctness.
