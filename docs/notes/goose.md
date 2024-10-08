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

1. Map from Go to its Goose translation.
2. Explain what is trusted in a proof using Goose.
3. Read proof goals involving Goose pointers and structs.

---

## High-level overview

Goose translates a subset of Go to GooseLang.

Define GooseLang and its semantics in Coq. Same style as lecture `expr`, with the following changes;

- values have machine integers / strings
- pairs and sums
- can allocate arrays

Concurrency features:

- non-atomic memory operations (not covered in class)
- Fork
- Compare-and-exchange to model locks

Basic idea: translate each Go package to a Coq file, and each function to an expression.

Control flow must be captured in an expression language: this cannot model all possible control flow but simplifies reasoning.

Model immutable local variables as let bindings vs heap variables - this "optimizes" the translation to something equivalent but easier to use. Explain how this works in Go.

## Implementation

How the translator uses Go tooling. What Go exposes for type checking.

## What does a proof mean?

Translation is implicitly giving a semantics to Go. Correctness relies on this program being modeled "correctly": modeled behavior should be a subset of Go compiler behavior.

If translation does not work, sound (can't prove something wrong) but not a good developer experience. Failure modes: does not translate, does not compile in Coq, compiles but GooseLang code is always undefined.

## Loops

Higher-order functions with specifications that capture loop invariants. We'll talk about some examples of loop invariants, which is a big topic.

---

::: info Next lecture start (probably)

:::

Ownership in Go

## Structs

Main topic for lecture: how to model structs, then how to reason about them. Need for some "types".

Difference between _shallow_ and _deep_ embedding.

## Slices and map

Modeling length, capacity, and contiguous allocations. Ownership in slices, slice append.

Maps as non-atomic values.

## Fractional permissions

"Fictional separation" models read-only access.
