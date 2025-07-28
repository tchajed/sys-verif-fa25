---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 10
shortTitle: "Lecture 10: IPM"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 10: Iris Proof Mode

> Follow these notes in Coq at [src/sys_verif/program_proof/ipm.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/ipm.v).

## Learning outcomes

By the end of this lecture, you should be able to

1. Translate goals from paper to the IPM and back
2. Read the IPM tactic documentation
3. Prove entailments in separation logic in Coq

---

::: info Additional resources

- [Interactive Proofs in Higher-Order Concurrent Separation Logic (POPL 2017)](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf). The paper for the first version of the IPM, which remains a very readable introduction.
- [Iris Proof Mode documentation](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md). A reference manual of tactics.

:::

<!-- @include: ./macros.snippet.md -->

## Motivation

We now want to move to using separation logic in Coq. If we formalized everything so far and proved all the rules as theorems, we would run into trouble when formalizing the proof outlines we've written so far, even with weakest preconditions. Consider the following entailment we left unproven in the [swap exercise solution](./sep-logic.md#ex-swap):

$\lift{t = a} ∗ x \pointsto b ∗ y \pointsto t ⊢ x \pointsto b ∗ y \pointsto a$.

To prove this in the model would be difficult: there would be the union of three heaps on the left and we would need to match them up with the two on the right. The disjointness on the left implies $x \neq y$, and this would be used to prove disjointness in the right-hand side.

It would also be difficult to use the rules: some re-association (we never even said what the associativity of separating conjunction is; it shouldn't matter) would reach a statement $\lift{t = a} ∗ (x \pointsto b) ∗ (y \pointsto a)$, then something like prop-from-pure would be used to "extract" $t = a$, then we would need to drop it &mdash; but wait, sep-pure-weaken requires the pure proposition on the _right_, so we have to swap the order, then swap back &mdash; and this is quickly getting out of hand.

The Iris Proof Mode (IPM) is the better way to formalize the proofs and also to _think_ about the proof.

### Exercise: on-paper proof by hand

Finish the proof of the entailment above using only separation logic rules. This exercise is instructive so you appreciate the IPM and understand why various manipulations are allowed.

## Reading IPM goals

The Iris Proof Mode provides an interface similar to Coq's proof mode; since you already have experience using that, it's helpful to understand it by analogy to how Coq's proof mode helps you work with the rules of Coq's logic.

In this explanation I'll use φ, ψ, ρ (phi, psi, rho) for Coq propositions and P, Q, R for separation logic propositions.

The IPM is used to prove entailments in separation logic. It's sufficient to get the intuition to imagine that the propositions are heap predicates `gmap loc val → Prop`, the separation logic operations are as defined as given in the notes, and entailment `P ⊢ Q` is defined as `∀ h, P h → Q h` (also as in the notes). However, the actual implementation is _parametric_ in the separation logic - you can "bring your own" separation logic implementation (if it satisfies the expected rules) and prove theorems in it.

An IPM goal looks like the following:

```text title="IPM goal"
"H1": P
"H2": Q
-----------∗
Q ∗ P
```

This represents the separation logic entailment $P ∗ Q ⊢ Q ∗ P$. However, the IPM goal has a richer representation of the context than a single proposition: it divides it into several _named conjuncts_. The names use Coq strings, which we write with quotes. Notice how this is exactly analogous to how we might have the following Coq goal:

```text title="Coq goal"
H1: φ
H2: ψ
============
ψ ∧ φ
```

which represents an entailment in the Coq logic `φ ∧ ψ ⊢ ψ ∧ φ`.

To recap: both representations have a _context_ with _named hypotheses_ and a _conclusion_. The names have no semantic meaning but are instead used to refer to hypotheses in tactics.

---

Now let's see how these look in Coq. First, we need to do some setup:

```rocq
From sys_verif.program_proof Require Import prelude.
From sys_verif.program_proof Require Import empty_ffi.
From sys_verif.program_proof Require heap_init.

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

```rocq
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

```rocq
  iFrame.
Qed.
```

```rocq
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

```rocq
  auto.
Qed.

```

### Aside: inputting special symbols

You might be wondering, how do you type this stuff? See the notes on [inputting special symbols](./program-proofs/input.md).

## IPM tactics

To prove theorems in Coq, we use tactics to manipulate the proof state. The IPM works the same way, providing a collection of tactics to manipulate the IPM context and conclusion. These tactics are intentionally designed to look like analogous Coq tactics, but there are some key differences that come from separation logic. Let's see an example, adapted from Figure 2 from the IPM paper. In this example I'll use the names P, Q, R in both, even though they are `Prop`s in one case and `iProp`s in the other:

### Analogy to the Coq proof mode

```rocq
Lemma and_exist_ex A (P Q: Prop) (R: A → Prop) :
  P ∧ (∃ a, R a) ∧ Q → ∃ a, R a ∧ P.
Proof.
  intros (HP & HR & HQ).
  destruct HR as [x HR].
  exists x.
  split.
  - assumption.
  - assumption.
Qed.

```

Now a very similar proof, in the IPM with separating conjunction:

```rocq
Lemma sep_exist_ex A (P Q: iProp Σ) (R: A → iProp Σ) :
  P ∗ (∃ a, R a) ∗ Q -∗ ∃ a, R a ∗ P.
Proof.
  iIntros "(HP & HR & HQ)".
  iDestruct "HR" as (x) "HR".
  iExists (x).
  iSplitL "HR".
  - iAssumption.
  - iAssumption.
Qed.

```

Here's the same thing, but with the goals shown:

```rocq
Lemma sep_exist_ex_v2 A (P Q: iProp Σ) (R: A → iProp Σ) :
  P ∗ (∃ a, R a) ∗ Q -∗ ∃ a, R a ∗ P.
Proof.
  iIntros "(HP & HR & HQ)".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  A : Type
  P, Q : iProp Σ
  R : A → iProp Σ
  ============================
  P ∗ (∃ a : A, R a) ∗ Q -∗ ∃ a : A, R a ∗ P // [!code --]
  "HP" : P // [!code ++]
  "HR" : ∃ a : A, R a // [!code ++]
  "HQ" : Q // [!code ++]
  --------------------------------------∗ // [!code ++]
  ∃ a : A, R a ∗ P // [!code ++]
```

::::

```rocq
  iDestruct "HR" as (x) "HR".
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  A : Type
  P, Q : iProp Σ
  R : A → iProp Σ
  x : A // [!code ++]
  ============================
  "HP" : P
  "HR" : ∃ a : A, R a // [!code --]
  "HR" : R x // [!code ++]
  "HQ" : Q
  --------------------------------------∗
  ∃ a : A, R a ∗ P
```

::::

```rocq
  iExists (x).
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  A : Type
  P, Q : iProp Σ
  R : A → iProp Σ
  x : A
  ============================
  "HP" : P
  "HR" : R x
  "HQ" : Q
  --------------------------------------∗
  ∃ a : A, R a ∗ P // [!code --]
  R x ∗ P // [!code ++]
```

::::

```rocq
  iSplitL "HR".
```

:::: info Goals

```txt title="goal 1"
  Σ : gFunctors
  A : Type
  P, Q : iProp Σ
  R : A → iProp Σ
  x : A
  ============================
  "HR" : R x
  --------------------------------------∗
  R x
```

```txt title="goal 2"
  Σ : gFunctors
  A : Type
  P, Q : iProp Σ
  R : A → iProp Σ
  x : A
  ============================
  "HP" : P
  "HQ" : Q
  --------------------------------------∗
  P
```

::::

```rocq
  - iAssumption.
  - iAssumption.
Qed.

```

Notice how `iIntros`, `iDestruct`, `iExists`, and `iAssumption` are all very similar to the analogous Coq tactics. You can see in `iDestruct` and `iExists` that we sometimes need to mix Coq-level identifiers (`x` is given to name the variable in `iDestruct` and passed as an argument to `iExists`) and IPM hypotheses (which all appear in quotes).

What is different in this proof is that `iSplit` is written `iSplitL "HR"`. This is because if we're proving $R ⊢ P ∗ Q$, we have to decide how to split up the hypotheses in $R$. Each hypothesis can be used for $P$ or $Q$ but not both; this is coming directly from the _separation_ in separation logic, and no such decision is needed in the Coq logic since all hypotheses can be used on both sides. The tactic `iSplitL` defines the split by naming all the hypotheses that should be used for the left-hand side; similarly `iSplitR` takes the hypotheses that should be used on the right-hand side.

### Separation logic-specific features

There are a few more tactics with behavior specific to separation logic.

- `iApply` is analogous to `apply`, but applying a wand rather than an implication. It can be used with Coq lemmas as well.
- `iDestruct` is similar to `iApply` but for forward reasoning. It can also be used with Coq lemmas.
- `iFrame` automates the process of proving something like `P1 ∗ P3 ∗ P2 ⊢ P1 ∗ P2 ∗ P3` by lining up hypotheses to the goal and "canceling" them out.

```rocq
Lemma apply_simple_ex P Q :
  (P -∗ Q) ∗ P -∗ Q.
Proof.
  iIntros "[HPQ HP]".
  iApply "HPQ".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  P, Q : iProp Σ
  ============================
  "HP" : P
  --------------------------------------∗
  P
```

::::

```rocq
  iAssumption.
Qed.

```

Applying is a little trickier when there are multiple hypotheses. Just like with `iSplit` we have to decide how hypotheses are divided up. We also see an example below where the wand comes from a Coq-level assumption; more realistically imagine that this is a lemma.

```rocq
Lemma apply_split_ex P1 P2 P3 Q :
  ((P1 ∗ P3) -∗ P2 -∗ Q) →
  P1 ∗ P2 ∗ P3 -∗ Q.
Proof.
  intros HQ.
  iIntros "(H1 & H2 & H3)".
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  P1, P2, P3, Q : iProp Σ
  HQ : P1 ∗ P3 -∗ P2 -∗ Q
  ============================
  "H1" : P1
  "H2" : P2
  "H3" : P3
  --------------------------------------∗
  Q
```

::::

At this point `iApply HQ` needs to produce two subgoals: one for `P1 ∗ P3` and another for `P2`. By default, it will assume you want all hypotheses for the last subgoal, which makes this proof unprovable.

Instead, we will use a _specialization pattern_ `with "[H1 H3]"` to divide the premises up.

```rocq
  iApply (HQ with "[H1 H3]").
  - (* This is a perfect use case for `iFrame`, which spares us from carefully
    splitting this goal up. *)
    iFrame.
  - iFrame.
Qed.

```

We did the proof "backward" with `iApply`. Let's see a forward proof with `iDestruct`;

```rocq
Lemma destruct_ex P1 P2 P3 Q :
  ((P1 ∗ P3) -∗ P2 -∗ Q) →
  P1 ∗ P2 ∗ P3 -∗ Q.
Proof.
  intros HQ.
  iIntros "(H1 & H2 & H3)".

  iDestruct (HQ with "[H1 H3]") as "HQ".
```

:::: info Goals

```txt title="goal 1"
  Σ : gFunctors
  P1, P2, P3, Q : iProp Σ
  HQ : P1 ∗ P3 -∗ P2 -∗ Q
  ============================
  "H1" : P1
  "H3" : P3
  --------------------------------------∗
  P1 ∗ P3
```

```txt title="goal 2"
  Σ : gFunctors
  P1, P2, P3, Q : iProp Σ
  HQ : P1 ∗ P3 -∗ P2 -∗ Q
  ============================
  "H2" : P2
  "HQ" : P2 -∗ Q
  --------------------------------------∗
  Q
```

::::

The first goal is the premise of `HQ` (using the hypotheses we made available using `with "[H1 H3]"`). The second goal has `HQ`.

```rocq
  { iFrame. }


```

"H2" and "HQ" are lost after this tactic, which is actually required because of separation logic; the wand is "used up" in proving `Q`, in the same ay that "H1" and "H3" were used in the premise of `HQ`.

```rocq
  iDestruct ("HQ" with "[H2]") as "HQ".
  { iFrame. }

  iFrame.
Qed.

```

All of these calls to `iFrame` are tedious. The IPM provides some features in specialization patterns and intro patterns to automate things better. Here's a quick demo, but see the documentation to learn more.

```rocq
Lemma destruct_more_framing_ex P1 P2 P3 Q :
  ((P1 ∗ P3) -∗ P2 -∗ Q) →
  P1 ∗ P2 ∗ P3 -∗ Q.
Proof.
  intros HQ.
  iIntros "(H1 & H2 & H3)".


```

`$H1` in a specialization pattern frames that hypothesis right away. We don't do the same with `"H3"` only for illustration purposes.

```rocq
  iDestruct (HQ with "[$H1 H3]") as "HQ".
```

:::: info Goals

```txt title="goal 1"
  Σ : gFunctors
  P1, P2, P3, Q : iProp Σ
  HQ : P1 ∗ P3 -∗ P2 -∗ Q
  ============================
  "H3" : P3
  --------------------------------------∗
  P3
```

```txt title="goal 2"
  Σ : gFunctors
  P1, P2, P3, Q : iProp Σ
  HQ : P1 ∗ P3 -∗ P2 -∗ Q
  ============================
  "H2" : P2
  "HQ" : P2 -∗ Q
  --------------------------------------∗
  Q
```

::::

```rocq
  { iFrame "H3". }


```

`as "$"` is an introduction pattern that does not name the resulting hypothesis but instead immediately frames it with something in the goal. In this case that finishes the proof.

```rocq
  iDestruct ("HQ" with "[$H2]") as "$".
Qed.

```

One more commonly used intro pattern is used for pure facts `⌜φ⌝` that show up within a separation logic statement.

(Ignore the `{hG: !heapGS Σ}` part, this is needed to use ↦ in this example.)

```rocq
Lemma pure_intro_pattern `{hG: !heapGS Σ} (t a b: w64) (x y: loc) :
  ⌜t = a⌝ ∗ x ↦ b ∗ y ↦ t -∗ x ↦ b ∗ y ↦ a.
Proof.

```

The `%Heq` intro pattern moves the hypothesis into the Coq context (sometimes called the "pure" context). It is unusual in that `Heq` appears in a string but turns into a Coq identifier.

```rocq
  iIntros "(%Heq & Hx & Hy)".
  iFrame.
  rewrite Heq.
  iFrame.
Qed.

```

Here's a different way to move something into the pure context:

```rocq
Lemma pure_intro_pattern_v2 `{hG: !heapGS Σ} (t a b: w64) (x y: loc) :
  ⌜t = a⌝ ∗ x ↦ b ∗ y ↦ t -∗ x ↦ b ∗ y ↦ a.
Proof.
  iIntros "(Heq & Hx & Hy)".
  iDestruct "Heq" as %Heq. subst.
  iFrame.
Qed.

```

One last tactic: you will need to use `iModIntro` in a couple situations. What's going on here is beyond the scope of this lecture.

`iModIntro` "introduces a modality". You'll use it for the _later modality_ `▷ P` (rarely) and for the _fancy update modality_ `|==> P` (often pronounced "fup-d", or "update").

```rocq
Lemma iModIntro_later P :
  P -∗ ▷ P.
Proof.
  iIntros "H".
  iModIntro.
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  P : iProp Σ
  ============================
  "H" : P
  --------------------------------------∗
  ▷ P // [!code --]
  P // [!code ++]
```

::::

```rocq
  iAssumption.
Qed.

Lemma iModIntro_fupd P :
  P -∗ |==> P.
Proof.
  iIntros "H".
  iModIntro.
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  P : iProp Σ
  ============================
  "H" : P
  --------------------------------------∗
  |==> P // [!code --]
  P // [!code ++]
```

::::

```rocq
  iAssumption.
Qed.

```

### Exercise: find the documentation for these features

Go to the [IPM documentation](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md) and find the _exact_ lines where the `%Heq` in both the first proof and second proof are documented.

## Program proofs in the IPM

There are two parts to understanding how program proofs are mechanized:

- How specifications are encoded (which goes slightly beyond what we've seen so far around weakest preconditions).
- Tactics specific to program proofs (the `wp_*` family of tactics).

### Specifications

Recall that weakest preconditions can be characterized in terms of triples by the following equation:

$$
P \entails \wp(e, Q) \iff \hoare{P}{e}{Q}
$$

The syntax `{{{ P }}} e {{{ RET v; Q(v) }}}` does not quite mean exactly the above. It is defined as:

$$∀ Φ.\, P \wand (∀ v.\, Q(v) \wand Φ(v)) \wand \wp(e, Φ)$$

To understand this, it helps to first rewrite it to an equivalent entailment with fewer wands:

$$∀ Φ.\, P ∗ (∀ v.\, Q(v) \wand Φ(v)) ⊢ \wp(e, Φ)$$

This is like a _continuation-passing style_ version of $P ⊢ \wp(e, Q)$ (if you've seen the term that might give some intuition). Observe that it is at least as strong: we can set $Φ = Q$ and recover the original triple. It also includes framing; it is like applying the wp-ramified-rule.

The benefit of applying the frame rule is that this form of specification gives a way to prove $\wp(e, Φ)$ for an arbitrary postcondition. However, it requires that the user prove $∀ v.\, Q(v) \wand Φ(v)$. The benefit of using this rule is that it can be applied whenever the goal is about $e$ while deferring the proof that $Q$ implies $Φ$.

The practical consequence, as we will see in Coq below, is convenience when we _use_ the specification in a larger proof. If we are in the midst of proving $R ⊢ \wp(e, Ψ)$ for some $Ψ$, we can use the specification $\hoare{P}{e}{Q}$ by splitting the context into $R ⊢ R_{\text{pre}} ∗ R_f$ and then proving the following things:

- $R_{\text{pre}} ⊢ P$
- $∀ v.\, Q(v) ∗ R_f ⊢ Ψ(v)$

Intuitively, the $R_f$ are the "leftover" facts that were not needed for the call to $e$, and thus they can be used for the remainder of the proof. This is exactly what the frame rule would give with $R_f$ as the frame (what we called $F$ in the rule). This reasoning does follow from separation logic rules, but it's okay if you don't see that right away; it's useful to see the intuition for this reasoning without deriving it purely formally.

### IPM tactics for WPs

The IPM has some tactics for weakest precondition reasoning specifically. It's actually not much:

- `wp_pures` is the most commonly used tactic. It applies the pure-step rule: if $e \purestep e'$, then $\wp(e', Q) ⊢ \wp(e, Q)$. Applying this rule has the effect of going from $e$ to the $e'$ that it reduces to, something that can be computed automatically. `wp_pures` applies the pure-step as many times as it can, but without going into the bodies of functions.
- `wp_bind e` automatically applies the bind rule, finding a way to split the current goal into `e` followed by `K[e]` (and failing if `e` is not actually the next part of the code to execute).
- `wp_apply lem` uses `wp_bind` to find a way to apply the already-proven triple `lem`.
- `wp_load`, `wp_store`, and `wp_alloc` automate using those specifications, since they are so commonly used.

All of these are easiest understood by seeing them in context; read on for an example.

```rocq
Import sys_verif.program_proof.heap_init.
Context `{hG: !heapGS Σ}.
Context `{!goGlobalsGS Σ}.

```

Recall that we had an example of an (unknown function) $f$ with the following specification:

$\hoare{\ell \mapsto \num{0}}{f \, (\ell, \ell')}{\funblank \ell \mapsto \num{42}}$

that we used in a larger example $e_{\text{own}}$.

We'll now do an analogous proof using Go code for `f` and some code that uses it, demonstrating how to use an existing specification and how to do framing.

The Go code for $f$ looks like this, although we won't cover its proof and will only use its specification.

```go
func IgnoreOneLocF(x *uint64, y *uint64) {
	std.Assert( *x == 0 )
	*x = 42
}
```

where `std.Assert` is a function provided by the Goose standard library.

```rocq
Lemma wp_IgnoreOneLocF (l l': loc) :
  {{{ is_pkg_init heap.heap ∗ l ↦ (W64 0) }}}
    heap.heap @ "IgnoreOneLocF" #l #l'
  {{{ RET #(); l ↦ (W64 42) }}}.
Proof.
  (* skip over this proof for now and focus on its usage (the next lemma) *)
  wp_start as "Hl".
  wp_alloc_auto; wp_pures.
  wp_alloc_auto; wp_pures.
  wp_load; wp_pures.
  wp_load; wp_pures.
  wp_apply (wp_Assert).
  { rewrite bool_decide_eq_true_2 //. }
  wp_pures.
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
	std.Assert(x == y)
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

```rocq
Lemma wp_UseIgnoreOneLocOwnership :
  {{{ is_pkg_init heap }}}
    heap.heap @ "UseIgnoreOneLocOwnership" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "Hpre". (* precondition is trivial, but we'll name it anyway *)
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  ============================
  _ : is_pkg_init heap
  "Hpre" : emp
  --------------------------------------□
  "HΦ" : True -∗ Φ (# ())
  --------------------------------------∗
  WP exception_do
       (let: "x" := alloc (zero_val uint64T) in
        let: "$r0" := # (W64 0) in
        (do: "x" <-[# uint64T] "$r0") ;;;
        let: "y" := alloc (type.zero_val (# uint64T)) in
        let: "$r0" := # (W64 42) in
        (do: "y" <-[# uint64T] "$r0") ;;;
        (do: (let: "$a0" := "x" in
              let: "$a1" := "y" in
              func_call (# heap) (# "IgnoreOneLocF"%go) "$a0" "$a1")) ;;;
        (do: (let: "$a0" := ![# uint64T] "x" = ![# uint64T] "y" in
              func_call (# std) (# "Assert"%go) "$a0")) ;;;
        return: # ())
  {{ v, Φ v }}
```

::::

```rocq
  rewrite -default_val_eq_zero_val.

```

The next step in the proof outline is this call to `ref_to`, which allocates.

Formally, the proof proceeds by applying the bind rule (to split the program into `ref_to uint64T #(W64 0)` and the rest of the code that uses this value). We can use an IPM tactic to automate this process, in particular identifying the context `K` in the bind rule.

```rocq
  wp_bind (alloc #(default_val w64))%E.
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  ============================
  _ : is_pkg_init heap
  "Hpre" : emp
  --------------------------------------□
  "HΦ" : True -∗ Φ (# ())
  --------------------------------------∗
  WP alloc (# (default_val w64))
  {{ v,
     WP exception_do
          (let: "x" := v in
           let: "$r0" := # (W64 0) in
           (do: "x" <-[# uint64T] "$r0") ;;;
           let: "y" := alloc (type.zero_val (# uint64T)) in
           let: "$r0" := # (W64 42) in
           (do: "y" <-[# uint64T] "$r0") ;;;
           (do: (let: "$a0" := "x" in
                 let: "$a1" := "y" in
                 func_call (# heap) (# "IgnoreOneLocF"%go) "$a0" "$a1")) ;;;
           (do: (let: "$a0" := ![# uint64T] "x" = ![# uint64T] "y" in
                 func_call (# std) (# "Assert"%go) "$a0")) ;;;
           return: # ())
     {{ v, Φ v }} }}
```

::::

Take a moment to read this goal: it says we need to prove a specification for just `ref` in which the postcondition contains the remainder of the code. Where the original code had `ref_to ...` it now has `v`, the return value of allocating; this is `K[v]` from the bind rule.

The next step you'd expect is that we need to use the rule of consequence to prove this goal from the existing specification for `ref`:

```rocq
  Check wp_alloc.
```

:::: note Output

```txt title="rocq output"
wp_alloc
     : ∀ (v : ?V) (stk : stuckness) (E : coPset) (Φ0 : val → iPropI Σ),
         True -∗
         ▷ (∀ l : loc, l ↦ v -∗ Φ0 (# l)) -∗
         WP alloc (# v) @ stk; E {{ v, Φ0 v }}
where
?V :
  [Σ : gFunctors
   hG : heapGS Σ
   goGlobalsGS0 : goGlobalsGS Σ
   Φ : val → iPropI Σ
  |- Type]
?IntoVal0 :
  [Σ : gFunctors
   hG : heapGS Σ
   goGlobalsGS0 : goGlobalsGS Σ
   Φ : val → iPropI Σ
  |- IntoVal ?V]
```

::::

We do _not_ end up needing the rule of consequence. The reason is that the meaning of `{{{ P }}} e {{{ RET v; Q }}}` in Iris already has consequence built-in.

```rocq
  iApply wp_alloc.
  { (* the (trivial) precondition in wp_alloc *)
    auto. }

  iModIntro. (* don't worry about this for now *)
  iIntros (x) "Hx".


```

At this point there is a `let:` binding which we need to apply the pure-step rule to. Thankfully, the IPM has automation to handle this for us.

```rocq
  wp_pures.
```

:::: info Goal diff

```txt title="goal diff"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  x : loc
  ============================
  _ : is_pkg_init heap
  "Hpre" : emp
  --------------------------------------□
  "HΦ" : True -∗ Φ (# ())
  "Hx" : x ↦ default_val w64
  --------------------------------------∗
  WP exception_do
       (let: "x" := # x in // [!code --]
        let: "$r0" := # (W64 0) in // [!code --]
        (do: "x" <-[# uint64T] "$r0") ;;; // [!code --]
       ((do: # x <-[# uint64T] # (W64 0)) ;;; // [!code ++]
        let: "y" := alloc (type.zero_val (# uint64T)) in
        let: "$r0" := # (W64 42) in
        (do: "y" <-[# uint64T] "$r0") ;;;
        (do: (let: "$a0" := "x" in // [!code --]
        (do: (let: "$a0" := # x in // [!code ++]
              let: "$a1" := "y" in
              func_call (# heap) (# "IgnoreOneLocF"%go) "$a0" "$a1")) ;;;
        (do: (let: "$a0" := ![# uint64T] "x" = ![# uint64T] "y" in // [!code --]
        (do: (let: "$a0" := ![# uint64T] (# x) = ![# uint64T] "y" in // [!code ++]
              func_call (# std) (# "Assert"%go) "$a0")) ;;;
        return: # ())
  {{ v, Φ v }}
```

::::

The IPM can automate all of the above for allocation, load, and store:

```rocq
  wp_store. wp_pures.
  wp_alloc y as "Hy".
  wp_pures.
  wp_store. wp_pures.
  wp_bind (heap @ "IgnoreOneLocF" _ _)%E. (* make the goal easier to understand *)
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  _ : is_pkg_init heap
  "Hpre" : emp
  --------------------------------------□
  "HΦ" : True -∗ Φ (# ())
  "Hx" : x ↦ W64 0
  "Hy" : y ↦ W64 42
  --------------------------------------∗
  WP # (func_callv heap "IgnoreOneLocF") (# x) (# y)
  {{ v,
     WP exception_do
          ((do: v) ;;;
           (do: (let: "$a0" := ![# uint64T] (# x) = ![# uint64T] (# y) in
                 func_call (# std) (# "Assert"%go) "$a0")) ;;;
           return: # ())
     {{ v, Φ v }} }}
```

::::

You might think we should do `iApply wp_IgnoreOneLocF`. Let's see what happens if we do that:

```rocq
  iApply wp_IgnoreOneLocF.
```

:::: info Goals

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  _ : is_pkg_init heap
  "Hpre" : emp
  --------------------------------------□
  is_pkg_init heap ∗ x ↦ W64 0
```

```txt title="goal 2"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  _ : is_pkg_init heap
  "Hpre" : emp
  --------------------------------------□
  "HΦ" : True -∗ Φ (# ())
  "Hx" : x ↦ W64 0
  "Hy" : y ↦ W64 42
  --------------------------------------∗
  ▷ (x ↦ W64 42 -∗
     WP exception_do
          ((do: # ()) ;;;
           (do: (let: "$a0" := ![# uint64T] (# x) = ![# uint64T] (# y) in
                 func_call (# std) (# "Assert"%go) "$a0")) ;;;
           return: # ())
     {{ v, Φ v }})
```

::::

The first goal is clearly unprovable! It asks us to prove a points-to fact with no assumptions. This is coming from the precondition in `wp_IgnoreOneLocF`. If you look at the second goal, we have the relevant fact in `Hx`.

What's going on is that `wp_IgnoreOneLocF` is of the form:

`∀ Φ, pre -∗ (post -∗ Φ) -∗ WP IgnoreOneLocF #l #l' {{ Φ }}`.

When we `iApply`, as with `apply` we get two subgoals: `pre` and `(post -∗ Φ)` (the postcondition `Φ` is automatically determined by looking at the conclusion prior to `iApply`).

Unlike `apply`, we need to prove the two subgoals from whatever premises we have available, and _they must be divided among the two proofs_. This is a fundamental consequence of separation: if all of our hypotheses were called `hyps` we actually need to prove `hyps ⊢ pre ∗ (post -∗ Φ)`, and this requires using each hypothesis in only one of the sub-proofs.

The IPM provides several mechanisms for deciding on these splits. A _specialization pattern_ (spat) is the simplest one: we'll list in square brackets the hypotheses that should go into the first subgoal, the precondition, and the remainder will be left for the second subgoal (which is the rest of the code and proof).

```rocq
  Undo 1.
  iApply (wp_IgnoreOneLocF with "[Hx]").
```

:::: info Goal

```txt title="goal 1"
  Σ : gFunctors
  hG : heapGS Σ
  goGlobalsGS0 : goGlobalsGS Σ
  Φ : val → iPropI Σ
  x, y : loc
  ============================
  _ : is_pkg_init heap
  "Hpre" : emp
  --------------------------------------□
  "Hx" : x ↦ W64 0
  --------------------------------------∗
  is_pkg_init heap ∗ x ↦ W64 0
```

::::

```rocq
  { iFrame. iPkgInit. (* normally the use of [wp_apply] would have handled this for us *) }

  iModIntro.
  (* this re-introduces the postcondition in `wp_IgnoreOneLocF` *)
  iIntros "Hx".


```

We'll now breeze through the rest of the proof:

```rocq
  wp_pures.
  wp_load.
  wp_load.
  wp_pures.
  wp_apply (wp_Assert).
  { rewrite bool_decide_eq_true_2 //. }
  wp_pures.
  iApply "HΦ". done.
Qed.

```

```rocq
End ipm.
```
