---
category: lecture
order: 25
shortTitle: "Lecture 25: SMT verification"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 25: Automated verification with SMT

In this lecture we'll talk about verifying sequential programs with Hoare logic, but with a high degree of automation using an SMT solver.

## Learning outcomes

1. Explain what a specification means in an SMT-based tool like Dafny.
2. Translate between the Coq and Dafny styles of proofs.

---

<!-- @include: ./macros.snippet.md -->

$$
\gdef\add{\operatorname{add}}
$$

## Motivation

It can be tedious to write proofs in Coq. Luckily, there are more automated approaches to verification which leverage sophisticated solvers to reduce the proof burden. However, automated verification isn't a solution to all your problems: there are limits to what can be efficiently automatically proven, and in practice the developer still needs to help the solver to prove correct programs. Automation is also more specialized, limiting what programs you can verify, especially when it comes to separation logic and concurrency, and going beyond current tools into research territory. Extending the reach of automation is an active area of research.

## Recall: sequential proofs without separation logic

Remember that we did sequential proofs in a _Hoare outline_ style even before we started using separation logic. These outlines had lines of code separated by an assertion that we know holds at that point in the code, starting with the precondition (assumed to be true) and ending with the postcondition (the final outcome of the proof).

Here is an example we saw before. The code we want to verify is $f$, implemented with helper functions $\add$ and $\min$:

$$
\begin{aligned}
\add &= \lambda x, y.\, x + y \\
\min &= \lambda x, y.\, \ife{x < y}{x}{y} \\
\operatorname{f} &= \fun{x} \add \, (\min \, 0 \, x) \, 1 \\
\end{aligned}
$$

Assume we have specifications for the helper functions (remember that these are intentionally not the most general specification possible):

$$
\hoare{n + m < 2^{64}}%
{\add \, \overline{n} \, \overline{m}}%
{\fun{v} v = \overline{n + m}}
$$

$$
\hoare{\True}%
{\min \, \overline{n} \, \overline{m}}%
{\fun{v} \exists (p: \mathbb{Z}).\, v = \overline{p} \land p \leq n \land p \leq m }
$$

Now we'll prove a specification for $f$ with a this Hoare outline:

$$
\begin{aligned}
&\outlineSpec{n < 2^{64} - 1} \\
&\outlineSpec{\True} \\
&\quad \lete{m}{\min \, 0 \, \overline{n}} \\
&\outlineSpec{\exists p_m.\, m = \overline{p_m} \land p_m \leq 0 \land p_m \leq n} \\
&\quad \lete{y}{\operatorname{add} \, m \, 1} \\
&\outlineSpec{y = \overline{p_m + 1}} \\
&\quad y \\
&\outlineSpec{\exists (p: \mathbb{Z}).\, y = \overline{p} \land p \leq 1)}
\end{aligned}
$$

## Dafny specifications and functions

Dafny is a **verification-oriented programming language**. It has functionality for implementation, specification, and proof all in the same language.

We write the implementations in a language inspired by C#, with the usual imperative features as well as object-oriented features like classes (but not inheritance like in C# and Java). Imperative code is written as `method`s in Dafny. To run the code, Dafny includes a compiler which supports a number of backends, including C#, Java, and Go, which we then link with other code and compile with the language's toolchain.

Specifications are written with pre- and post-conditions attached to methods with the `requires` and `ensures` keywords. Dafny's specification language supports rich functional programs using mathematical data types like `int` (unbounded integers) and `seq<T>` (mathematical sequences), similar to what you saw in Coq before we started verifying imperative programs.

Method specifications are checked mostly automatically by a solver (which we'll talk about shortly), but Dafny also has features for writing proofs to assist the solver when it can't do the proof on its own.

## Example proof

If simple enough, proof of a function goes through automatically (demo)

Sometimes need to give some help to verifier with `assert`, `if` (demo)

## Weakest precondition calculation

Basic idea: translate method and proof (e.g., assertions) into a big formula

negate formula and send to SMT solver: if SAT, have a bug, if UNSAT code method meets spec

how to create formula? weakest precondition algorithm

## Loop invariants

## Problems with SMT solving

Core issue: triggers (brief explanation of trigger patterns and triggering; loop example as motivation)

Solver instability due to heuristics (maybe not strictly dependent on triggers but they help)

## Limitations

Dafny does not support concurrency

Newer tools like Verus (like Dafny but for Rust) have added preliminary support for concurrent verification based on Iris ghost state

Iris is still (currently) the most advanced tool. Due to its _foundational_ nature it's possible to extend Iris in fundamental ways (new programs, new specifications) where other tools bake-in a particular approach; but usability is probably never as good as with automation.
