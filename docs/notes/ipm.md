---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 10
shortTitle: "Lecture 10: IPM"
---

# Lecture 10: Iris Proof Mode

> Follow these notes in Coq at [src/sys_verif/program_proof/ipm.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/ipm.v).

## Learning outcomes

By the end of this lecture, you should be able to

1. Translate goals from paper to the IPM and back
2. Read the IPM tactic documentation
3. Prove entailments in separation logic in Coq

---

<!-- @include: ./macros.snippet.md -->

## Motivation

We now want to move to using separation logic in Coq. If we formalized everything so far and proved all the rules as theorems, we would run into trouble when formalizing the proof outlines we've written so far, even with weakest preconditions. Consider the following entailment we left unproven in the [swap exercise solution](./sep-logic.md#ex-swap):

$\lift{t = a} ∗ x \pointsto b ∗ y \pointsto t ⊢ x \pointsto b ∗ y \pointsto a$.

To prove this in the model would be difficult: there would be the union of three heaps on the left and we would need to match them up with the two on the right. The disjointness on the left implies $x \neq y$, and this would be used to prove disjointness in the right-hand side.

It would also be difficult to use the rules: some re-association (we never even said what the associativity of separating conjunction is; it shouldn't matter) would reach a statement $\lift{t = a} ∗ (x \pointsto b) ∗ (y \pointsto a)$, then something like prop-from-pure would be used to "extract" $t = a$, then we would need to drop it &mdash; but wait, sep-pure-weaken requires the pure proposition on the _right_, so we have to swap the order, then swap back &mdash; and this is quickly getting out of hand.

The Iris Proof Mode (IPM) is the better way to formalize the proofs and also to _think_ about the proof.

::: info Additional resources

- [Interactive Proofs in Higher-Order Concurrent Separation Logic (POPL 2017)](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf). The paper for the first version of the IPM, which remains a very readable introduction.
- [Iris Proof Mode documentation](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md). A reference manual of tactics.

:::

## IPM goals

The Iris Proof Mode provides an interface similar to Coq's proof mode; since you already have experience using that, it's helpful to understand it by analogy to how Coq's proof mode helps you work with the rules of Coq's logic.

In this explanation I'll use φ, ψ, ρ (phi, psi, rho) for Coq propositions and P, Q, R for separation logic propositions.

The IPM is used to prove entailments in separation logic. It's sufficient to get the intuition to imagine that the propositions are heap predicates `gmap loc val → Prop`, the separation logic operations are as defined as given in the notes, and entailment `P ⊢ Q` is defined as `∀ h, P h → Q h` (also as in the notes). However, the actual implementation is _parametric_ in the separation logic - you can "bring your own" separation logic implementation (if it satisfies the expected rules) and prove theorems in it.

An IPM goal looks like the following:

```text
"H1": P
"H2": Q
-----------∗
Q ∗ P
```

This represents the separation logic entailment $P ∗ Q ⊢ Q ∗ P$. However, the IPM goal has a richer representation of the context than a single proposition: it divides it into several _named conjuncts_. The names use Coq strings, which we write with quotes. Notice how this is exactly analogous to how we might have the following Coq goal:

```text
H1: φ
H2: ψ
============
ψ ∧ φ
```

which represents an entailment in the Coq logic `φ ∧ ψ ⊢ ψ ∧ φ`.

To recap: both representations have a _context_ with _named hypotheses_ and a _conclusion_. The names have no semantic meaning but are instead used to refer to hypotheses in tactics.

Now let's see how these look in Coq.

The IPM is _embedded_ in Coq, rather than developed as a separate system. The way this works is that the entire IPM goal, context and conclusion together, will be in a Coq goal, and above that will be a _Coq context_. Thus we will actually be proving that a set of Coq hypotheses imply (at the Coq level) a separation logic entailment.

```coq
From sys_verif.program_proof Require Import prelude.

Section ipm.
Context (Σ: gFunctors).
Implicit Types (φ ψ ρ: Prop).
Implicit Types (P Q R: iProp Σ).

```

In both Coq and the IPM, we will state the original goal using an implication rather than an entailment symbol.

For separation logic, we will use the _separating implication_ or wand.

```coq
Lemma ipm_context_ex P Q :
  P ∗ Q -∗ Q ∗ P.
Proof.
  (* ignore the tactics for now and just focus on reading the goal *)
  iIntros "[H1 H2]".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  P, Q : iProp Σ
  ============================
  "H1" : P
  "H2" : Q
  --------------------------------------∗
  Q ∗ P
```

::::

```coq
  iFrame.
Qed.
```

```coq
Lemma coq_context_ex φ ψ :
  φ ∧ ψ → ψ ∧ φ.
Proof.
  intros [H1 H2].
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  φ, ψ : Prop
  H1 : φ
  H2 : ψ
  ============================
  ψ ∧ φ
```

::::

```coq
  auto.
Qed.

```

## IPM tactics

To prove theorems in Coq, we use tactics to manipulate the proof state. The IPM works the same way, providing a collection of tactics to manipulate the IPM context and conclusion. These tactics are intentionally designed to look like analogous Coq tactics, but there are some key differences that come from separation logic. Let's start with some things that are very similar.

```coq
End ipm.
```
