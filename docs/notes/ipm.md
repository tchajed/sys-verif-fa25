---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 10
shortTitle: "Lecture 10: IPM"
pageInfo: ["Date", "Category", "Tag", "Word"]
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

Now let's see how these look in Coq. First, we need to do some setup:

```coq
From sys_verif.program_proof Require Import prelude.
From sys_verif.program_proof Require Import empty_ffi.
From Goose.sys_verif_code Require heap.

Section ipm.
(* Ignore this Σ variable; it's part of Iris. *)
Context (Σ: gFunctors).
Implicit Types (φ ψ ρ: Prop).
(* iProp Σ is the type of Iris propositions. These are our separation logic
propositions. *)
Implicit Types (P Q R: iProp Σ).

```

The IPM is _embedded_ in Coq, rather than developed as a separate system. The way this works is that the entire IPM goal, context and conclusion together, will be in a Coq goal, and above that will be a _Coq context_. Thus we will actually be proving that a set of Coq hypotheses imply (at the Coq level) a separation logic entailment.

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

::: warning Draft

TODO: write this section

:::

## Program proofs in the IPM

```coq
Import Goose.sys_verif_code.heap.
Context `{hG: !heapGS Σ}.

```

Recall that we had an example of an (unknown function) $f$ with the following specification:

$\hoare{\ell \mapsto \num{0}}{f \, (\ell, \ell')}{\funblank \ell \mapsto \num{42}}$

that we used in a larger example $e_{\text{own}}$.

We'll now do an analogous proof using Go code for `f` and some code that uses it, demonstrating how to use an existing specification and how to do framing.

The Go code for $f$ looks like this, although we won't cover its proof and will only use its specification.

```go
func IgnoreOneLocF(x *uint64, y *uint64) {
	primitive.Assert( *x == 0 )
	*x = 42
}
```

where `primitive.Assert` is a function provided by the Goose standard library.

```coq
Lemma wp_IgnoreOneLocF (l l': loc) :
  {{{ l ↦[uint64T] #(W64 0) }}}
    IgnoreOneLocF #l #l'
  {{{ RET #(); l ↦[uint64T] #(W64 42) }}}.
Proof.
  (* skip over this proof for now and focus on its usage (the next lemma) *)
  wp_start as "Hl".
  wp_pures.
  wp_load.
  wp_apply (wp_Assert).
  { rewrite bool_decide_eq_true_2 //. }
  wp_store.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

```

We're now going to verify this Go code that uses `IgnoreOneLocF` as a black box:

```go
func IgnoreOneLocF(x *uint64, y *uint64) { ... }

func UseIgnoreOneLocOwnership() {
	var x = uint64(0)
	var y = uint64(42)
	IgnoreOneLocF(&x, &y)
	primitive.Assert(x == y)
}
```

Compare to the example we verified before:

$$
\begin{aligned}
&e_{\text{own}} ::= \\
&\quad \lete{x}{\alloc{\num{0}}} \\ %
&\quad \lete{y}{\alloc{\num{42}}} \\ %
&\quad f \, (x, y)\then \\ %
&\quad \assert{(\load{x} == \load{y})}
\end{aligned}
$$

```coq
Lemma wp_UseIgnoreOneLocOwnership :
  {{{ True }}}
    UseIgnoreOneLocOwnership #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "Hpre". (* precondition is trivial, but we'll name it anyway *)
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  ============================
  "Hpre" : True
  "HΦ" : True -∗ Φ #()
  --------------------------------------∗
  WP let: "x" := ref_to uint64T #(W64 0) in
     let: "y" := ref_to uint64T #(W64 42) in
     IgnoreOneLocF "x" "y";;
     impl.Assert (![uint64T] "x" = ![uint64T] "y");; #()
  {{ v, Φ v }}
```

::::

The next step in the proof outline is this call to `ref_to`, which allocates.

Formally, the proof proceeds by applying the bind rule (to split the program into `ref_to uint64T #(W64 0)` and the rest of the code that uses this value). We can use an IPM tactic to automate this process, in particular identifying the context `K` in the bind rule.

```coq
wp_bind (ref_to uint64T #(W64 0))%E.
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  ============================
  "Hpre" : True
  "HΦ" : True -∗ Φ #()
  --------------------------------------∗
  WP ref_to uint64T #(W64 0)
  {{ v,
     WP let: "x" := v in
        let: "y" := ref_to uint64T #(W64 42) in
        IgnoreOneLocF "x" "y";;
        impl.Assert (![uint64T] "x" = ![uint64T] "y");; #()
     {{ v, Φ v }} }}
```

::::

Take a moment to read this goal: it says we need to prove a specification for just `ref` in which the postcondition contains the remainder of the code. Where the original code had `ref_to ...` it now has `v`, the return value of allocating; this is `K[v]` from the bind rule.

The next step you'd expect is that we need to use the rule of consequence to prove this goal from the existing specification for `ref`:

```coq
Check wp_ref_to.
```

:::: note Output

```txt title="coq output"
wp_ref_to
     : ∀ (t : ty) (stk : stuckness) (E : coPset) (v : val),
         val_ty v t
         → {{{ True }}}
             ref_to t v
           @ stk; E
           {{{ (l : loc), RET #l; l ↦[t] v }}}
```

::::

We do _not_ end up needing the rule of consequence. The reason is that the meaning of `{{{ P }}} e {{{ RET v; Q }}}` in Iris already has consequence built-in.

```coq
iApply wp_ref_to.
  { (* typing-related: ignore for now *)
    auto. }
  { (* the (trivial) precondition in wp_ref_to *)
    auto. }

  iModIntro. (* don't worry about this for now *)
  iIntros (x) "Hx".


```

At this point there is a `let:` binding which we need to apply the pure-step rule to. Thankfully, the IPM has automation to handle this for us.

```coq
wp_pures.
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  x : loc
  ============================
  "Hpre" : True
  "HΦ" : True -∗ Φ #()
  "Hx" : x ↦[uint64T] #(W64 0)
  --------------------------------------∗
  WP let: "x" := #x in // [!code --]
     let: "y" := ref_to uint64T #(W64 42) in // [!code --]
     IgnoreOneLocF "x" "y";;  // [!code --]
     impl.Assert (![uint64T] "x" = ![uint64T] "y");; #() // [!code --]
  WP let: "y" := ref_to uint64T #(W64 42) in // [!code ++]
     IgnoreOneLocF #x "y";;  // [!code ++]
     impl.Assert (![uint64T] #x = ![uint64T] "y");; #() // [!code ++]
  {{ v, Φ v }}
```

::::

The IPM can automate all of the above for allocation, load, and store:

```coq
wp_alloc y as "Hy".
  wp_pures.
  wp_bind (IgnoreOneLocF _ _). (* make the goal easier to understand *)
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  "Hpre" : True
  "HΦ" : True -∗ Φ #()
  "Hx" : x ↦[uint64T] #(W64 0)
  "Hy" : y ↦[uint64T] #(W64 42)
  --------------------------------------∗
  WP IgnoreOneLocF #x #y
  {{ v,
     WP v;; impl.Assert (![uint64T] #x = ![uint64T] #y);; #() {{ v, Φ v }} }}
```

::::

You might think we should do `iApply wp_IgnoreOneLocF`. Let's see what happens if we do that:

```coq
iApply wp_IgnoreOneLocF.
```

:::: info Goals

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  --------------------------------------∗
  x ↦[uint64T] #(W64 0)
```

```txt title="goal 2"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  "Hpre" : True
  "HΦ" : True -∗ Φ #()
  "Hx" : x ↦[uint64T] #(W64 0)
  "Hy" : y ↦[uint64T] #(W64 42)
  --------------------------------------∗
  ▷ (x ↦[uint64T] #(W64 42) -∗
     WP #();; impl.Assert (![uint64T] #x = ![uint64T] #y);; #() {{ v, Φ v }})
```

::::

The first goal is clearly unprovable! It asks us to prove a points-to fact with no assumptions. This is coming from the precondition in `wp_IgnoreOneLocF`. If you look at the second goal, we have the relevant fact in `Hx`.

What's going on is that `wp_IgnoreOneLocF` is of the form:

`∀ Φ, pre -∗ (post -∗ Φ) -∗ WP IgnoreOneLocF #l #l' {{ Φ }}`.

When we `iApply`, as with `apply` we get two subgoals: `pre` and `(post -∗ Φ)` (the postcondition `Φ` is automatically determined by looking at the conclusion prior to `iApply`).

Unlike `apply`, we need to prove the two subgoals from whatever premises we have available, and _they must be divided among the two proofs_. This is a fundamental consequence of separation: if all of our hypotheses were called `hyps` we actually need to prove `hyps ⊢ pre ∗ (post -∗ Φ)`, and this requires using each hypothesis in only one of the sub-proofs.

The IPM provides several mechanisms for deciding on these splits. A _specialization pattern_ (spat) is the simplest one: we'll list in square brackets the hypotheses that should go into the first subgoal, the precondition, and the remainder will be left for the second subgoal (which is the rest of the code and proof).

```coq
Undo 1.
  iApply (wp_IgnoreOneLocF with "[Hx]").
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  "Hpre" : True
  "HΦ" : True -∗ Φ #()
  "Hx" : x ↦[uint64T] #(W64 0)
  "Hy" : y ↦[uint64T] #(W64 42)
  --------------------------------------∗
  ▷ (x ↦[uint64T] #(W64 42) -∗
     WP #();; impl.Assert (![uint64T] #x = ![uint64T] #y);; #() {{ v, Φ v }})
```

::::

```coq
  { iFrame. }

  iModIntro.
  (* this re-introduces the postcondition in `wp_IgnoreOneLocF` *)
  iIntros "Hx".


```

We'll now breeze through the rest of the proof:

```coq
wp_pures.
  wp_load.
  wp_load.
  wp_apply (wp_Assert).
  { rewrite bool_decide_eq_true_2 //. }
  wp_pures.
  iModIntro.
  iApply "HΦ". done.
Qed.

```

```coq
End ipm.
```
