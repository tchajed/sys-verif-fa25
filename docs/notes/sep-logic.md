---
category: lecture
order: 8
---

# Lecture 8: Separation logic

::: warning Draft

These notes are a work in progress.

:::

## Learning outcomes

After this lecture you should be able to

1. Predict behavior of the separating conjunction from intuition
2. Write proof outlines in separation logic
3. Appreciate the frame rule

---

## Overview

After much time spent on functional programs, we will now finally start talking about _imperative programs_. Specifically we will add (1) mutable variables allocated on the heap and (2) while loops. Separation logic will be the new idea that will allow reasoning about pointers.

$$
\gdef\ife#1#2#3{\text{\textbf{if} } #1 \text{ \textbf{then} } #2 \text{ \textbf{else} } #3}
\gdef\lete#1#2{\text{\textbf{let} } #1 := #2 \text{ \textbf{in} }}
\gdef\letV#1#2{&\text{\textbf{let} } #1 := #2 \text{ \textbf{in} }}
\gdef\true{\mathrm{true}}
\gdef\True{\mathrm{True}}
\gdef\false{\mathrm{false}}
\gdef\hoare#1#2#3{\left\{#1\right\} \, #2 \, \left\{#3\right\}}
\gdef\hoareV#1#2#3{\begin{aligned}%
&\left\{#1\right\} \\ &\quad #2 \\ &\left\{#3\right\}%
\end{aligned}}
\gdef\fun#1{\lambda #1.\,}
\gdef\app#1#2{#1 \, #2}
\gdef\entails{\vdash}
\gdef\eqnlabel#1{\:\:\text{#1}}
\gdef\lift#1{\lceil #1 \rceil}
$$

Separation logic is an extension of Hoare logic. We'll still have a specification of the form $\hoare{P}{e}{\fun{v} Q(v)}$. There are three main extensions:

- Propositions will no longer be pure and equivalent to a Coq `Prop`. Instead, they'll be predicates over the heap, of type `hProp := heap → Prop` (`heap` is our representation of state of these imperative programs, which we'll get to later). The precondition and postcondition will be these heap predicates, so they'll say something about both program variables and the initial and final states of the program.
- In addition to the usual connectives over propositions ($P \land Q$, $P \lor Q$, $\exists x.\, P(x)$), we'll add a new _separating conjunction_ $P \sep Q$. We'll start using the notation $\lift{\phi}$ ("lift phi"), which takes an ordinary `Prop` and turns it into an `hProp`. It'll be more important to distinguish these pure propositions because once true, they remain true, whereas a statement about the state of the program can become false as the state evolves.
- We'll add some new rules for proving separation logic triples (and keep all the old rules).

## Heap predicates

Let's first talk about the _model_ of a separation logic proposition, `hProp := heap → Prop`.

## Separation logic propositions

Separation logic adds a _points-to assertion_ and the _separating conjunction_.

## Separation logic proof rules

Separation logic adds very few rules: the celebrated _frame rule_, and the _small-footprint axioms_ for loads, stores, and allocation.
