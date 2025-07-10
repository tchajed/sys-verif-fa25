---
# Auto-generated from literate source. DO NOT EDIT.
order: -2
---

# Ltac reference

```coq
From Perennial.Helpers Require Import ListLen.
From stdpp Require Import gmap.

From sys_verif Require Import options.

Close Scope Z_scope.

```

## Forward and backward reasoning

`intros`, `apply`, `assumption`

There are two basic styles of reasoning: a **backward** proof uses `Q -> R` to move from proving `R` to proving `Q` (working _backward from the goal_, trying to reach the hypotheses), while a **forward** proof uses `P -> Q` and a hypothesis `P` to derive `Q` (working _forward_ from the known hypotheses to try to reach the goal).

Both styles are valid and you should be aware of each; which you use in each case is a matter of intuition and convenience. A very brief demo of each is below, but there are more tactics related to each.

A "backwards" proof, working from the goal to the premises.

```coq
Lemma propositional_demo_1 (P Q R : Prop) :
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros HPQ HQR HP.
  apply HQR.
```

:::: info Goal diff

```txt title="goal diff"
  P, Q, R : Prop
  HPQ : P → Q
  HQR : Q → R
  HP : P
  ============================
  R // [!code --]
  Q // [!code ++]
```

::::

```coq
  apply HPQ.
  apply HP.
Qed.

```

A "forwards" proof, working from the premises to the goal.

```coq
Lemma propositional_demo_2 (P Q R : Prop) :
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros HPQ HQR HP.
  apply HPQ in HP.
```

:::: info Goal diff

```txt title="goal diff"
  P, Q, R : Prop
  HPQ : P → Q
  HQR : Q → R
  HP : P // [!code --]
  HP : Q // [!code ++]
  ============================
  R
```

::::

```coq
  apply HQR in HP.
  assumption.
Qed.

```

`destruct` on a hypothesis of the form `A ∨ B` produces two goals, one for `A` and one for `B`. Below we also use `as [HP | HQ]` to name the hypothesis in each goal.

```coq
Lemma propositional_demo_or (P Q : Prop) :
  (Q -> P) ->
  (P ∨ Q) -> P.
Proof.
  intros H1 HPQ.
  destruct HPQ as [HP | HQ].
  - assumption.
  - apply H1. assumption.
Qed.


```

## Computation: `simpl`, `reflexivity`

```coq
Inductive play := rock | paper | scissors.
Definition beats (p1 p2: play) : bool :=
  match p1, p2 with
  | rock, scissors => true
  | scissors, paper => true
  | paper, rock => true
  | _, _ => false
  end.

```

`simpl` computes or "reduces" functions in the goal

`reflexivity` solves a goal of the form `a = a` or fails. It also solves `a = b` if `a` and `b` compute to the same thing (so `simpl` is unnecessary in the proof below).

```coq
Lemma beats_ex_1 : beats paper rock = true.
Proof.
  simpl.
```

:::: info Goal

```txt title="goal 1"
  ============================
  true = true
```

::::

```coq
 reflexivity.
Qed.

```

## `destruct` for inductive datatype

```coq
Lemma beats_irrefl (p: play) : beats p p = false.
Proof.
  destruct p.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

```

## Using `;` to chain tactics

`t1; t2` runs `t1`, then `t2` on every subgoal generated from `t1`. This can be used to shorten proofs, like this one (compare to `beats_irrefl` above):

```coq
Lemma beats_irrefl' (p: play) : beats p p = false.
Proof.
  (* we don't need to repeat [reflexivity] three times *)
  destruct p; reflexivity.
Qed.

```

`t1; [t2 | t3]` runs `t1`, then runs `t2` on the first generated subgoal and `t3` on the second. It fails if there aren't exactly two subgoals.

`t3` can be ommitted (as below), in which case nothing is run in that subgoal.

This generalizes to more than two with `t1; [t2 | t3 | t4]` and so on.

```coq
Lemma add_0_r (n: nat) :
  n + 0 = n.
Proof.
  induction n as [ |n IHn]; simpl; [ reflexivity | ].
```

:::: info Goal

```txt title="goal 1"
  n : nat
  IHn : n + 0 = n
  ============================
  S (n + 0) = S n
```

::::

```coq
  (* note that we already ran `simpl` in this goal *)
  rewrite IHn. reflexivity.
Qed.

```

## Miscellaneous

### `subst`

`subst` repeatedly finds an equality of the form `x = ...` and substitutes `x` for the right-hand side: it rewrites the lemma everywhere, then removes `x` from the context (since it is no longer used). Useful to clean up the context.

```coq
Lemma subst_example (a b c: nat) (f: nat → nat) :
  a = b →
  b = c →
  f a = f c.
Proof.
  intros H1 H2.
  subst.
```

:::: info Goal diff

```txt title="goal diff"
  a, b, c : nat // [!code --]
  c : nat // [!code ++]
  f : nat → nat
  H1 : a = b // [!code --]
  H2 : b = c // [!code --]
  ============================
  f a = f c // [!code --]
  f c = f c // [!code ++]
```

::::

```coq
  reflexivity.
Qed.


```

## List tactics

You'll mainly use list lemmas together with the general tactics `apply`, `apply ... in`, and `assert`.

### `autorewrite with len`, `list_elem`

We have two useful tactics: `autorewrite with len` simplifies `length (...)` for various list functions, and `list_elem` is best explaining by the demo below.

```coq
Lemma list_reasoning_demo (l1 l2: list Z) (i: nat) (x: Z) :
  l1 `prefix_of` l2 →
  l1 !! i = Some x →
  l2 !! i = Some x.
Proof.
  intros Hpre Hget1.
  rewrite /prefix in Hpre.
  destruct Hpre as [l1' Heq]; subst.
  (* [Search lookup app] would be a good way to find this lemma. If you don't
  know what names to use for the notations, start with [Locate "!!"] (to find
  `lookup`) and [Locate "++"] (to find `app`). It's enough to search for one
  "token" (sequence of symbols) from the notation. *)

```

::::: details Output of Search lookup app

```coq
  Search lookup app.
```

:::: note Output

```txt title="coq output"
List.lookup_snoc:
  ∀ {A : Type} (l : list A) (x : A), (l ++ [x]) !! length l = Some x
lookup_app_l:
  ∀ {A : Type} (l1 l2 : list A) (i : nat),
    i < length l1 → (l1 ++ l2) !! i = l1 !! i
list_lookup_middle:
  ∀ {A : Type} (l1 l2 : list A) (x : A) (n : nat),
    n = length l1 → (l1 ++ x :: l2) !! n = Some x
lookup_app_l_Some:
  ∀ {A : Type} (l1 l2 : list A) (i : nat) (x : A),
    l1 !! i = Some x → (l1 ++ l2) !! i = Some x
lookup_app_r:
  ∀ {A : Type} (l1 l2 : list A) (i : nat),
    length l1 ≤ i → (l1 ++ l2) !! i = l2 !! (i - length l1)
take_drop_middle:
  ∀ {A : Type} (l : list A) (i : nat) (x : A),
    l !! i = Some x → take i l ++ x :: drop (S i) l = l
take_S_r:
  ∀ {A : Type} (l : list A) (n : nat) (x : A),
    l !! n = Some x → take (S n) l = take n l ++ [x]
lookup_app:
  ∀ {A : Type} (l1 l2 : list A) (i : nat),
    (l1 ++ l2) !! i =
    match l1 !! i with
    | Some x => Some x
    | None => l2 !! (i - length l1)
    end
elem_of_list_split_length:
  ∀ {A : Type} (l : list A) (i : nat) (x : A),
    l !! i = Some x → ∃ l1 l2 : list A, l = l1 ++ x :: l2 ∧ i = length l1
lookup_snoc_Some:
  ∀ {A : Type} (x : A) (l : list A) (i : nat) (y : A),
    (l ++ [x]) !! i = Some y
    ↔ i < length l ∧ l !! i = Some y ∨ i = length l ∧ x = y
lookup_app_Some:
  ∀ {A : Type} (l1 l2 : list A) (i : nat) (x : A),
    (l1 ++ l2) !! i = Some x
    ↔ l1 !! i = Some x ∨ length l1 ≤ i ∧ l2 !! (i - length l1) = Some x
```

::::

:::::

```coq
  rewrite lookup_app_l.
  { (* [apply ... in] applies the tactic to a premise, working forward from the
       hypotheses. (In this case the result exactly matches the goal, but this
       proof strategy is more general.) *)
    apply lookup_lt_Some in Hget1.
    lia. }
  auto.
Qed.

```

`list_elem l i as x` takes a list `l`, an index `i`, and produces a variable `x` and a hypothesis `Hx_lookup : l !! i = Some x`. As a side condition, you must prove `i < length l` (required for such an `x` to exist); some automation tries to prove this fact for you, though.

```coq
Lemma list_elem_demo (l1 l2: list Z) (i: nat) :
  (i < length l1 + length l2)%nat →
  ∃ x, (l1 ++ l2) !! i = Some x.
Proof.
  intros Hi.
  list_elem (l1 ++ l2) i as x.
  (* no side condition - `i < length l1` is proven automatically *)
  exists x; auto.
Qed.

```

## Rewriting

Rewriting is the act of using `a = b` to replace `a` with `b`. It's a powerful and useful proof technique.

Let's first see a simple example:

```coq
Lemma rewriting_demo1 (n1 n2 x: nat) :
  n1 = n2 →
  n1 + x = n2 + x.
Proof.
  intros Heq.
  rewrite Heq.
```

:::: info Goal diff

```txt title="goal diff"
  n1, n2, x : nat
  Heq : n1 = n2
  ============================
  n1 + x = n2 + x // [!code --]
  n2 + x = n2 + x // [!code ++]
```

::::

It's a seemingly small change but the left and right-hand sides are now equal!

```coq
  reflexivity.
Qed.


```

Here are some more examples, which require a little setup:

```coq
Module rewriting.

(* some arbitrary type for map values *)
Definition V: Type := (nat*nat).
(* this command uses the names of parameters to give them a default type, a
common mathematical practice *)
Implicit Types (m: gmap Z V) (k: Z) (v: V).

Lemma gmap_lookup_delete m k :
  delete k m !! k = None.
Proof. apply lookup_delete. Qed.

Lemma gmap_lookup_delete_ne m k k' :
  k ≠ k' →
  delete k m !! k' = m !! k'.
Proof. apply lookup_delete_ne. Qed.

```

### rewrite

```coq
Lemma lookup_delete_ex1 m k v :
  delete k (<[k := v]> m) !! k = delete k m !! k.
Proof.
  rewrite gmap_lookup_delete.
```

:::: info Goal diff

```txt title="goal diff"
  m : gmap Z V
  k : Z
  v : V
  ============================
  delete k (<[k:=v]> m) !! k = delete k m !! k // [!code --]
  None = delete k m !! k // [!code ++]
```

::::

```coq
  rewrite gmap_lookup_delete.
  done.
Qed.

```

### rewrite !

```coq
Lemma lookup_delete_ex2 m k v :
  delete k (<[k := v]> m) !! k = delete k m !! k.
Proof.

```

`rewrite !lem` rewrites `lem` one or more times (fails if it never applies)

```coq
  rewrite !gmap_lookup_delete.
```

:::: info Goal

```txt title="goal 1"
  m : gmap Z V
  k : Z
  v : V
  ============================
  None = None
```

::::

```coq
  done.
Qed.

```

### rewrite //

```coq
Lemma lookup_delete_ex3  m k v :
  delete k (<[k := v]> m) !! k = delete k m !! k.
Proof.

```

The `//` is an _action_ that tries to prove "trivial" goals (or subgoals from rewrite side conditions). We can use it to give a one-line proof.

```coq
  rewrite !gmap_lookup_delete //.
Qed.

```

### rewrite side conditions

```coq
Lemma lookup_delete_ne_ex1 m k v k' :
  k ≠ k' →
  delete k (<[k := v]> m) !! k' = delete k m !! k'.
Proof.
  intros Hne.

```

This lemma to rewrite with has a premise or _side condition_: it only applies if the two keys involved are not equal. By default, `rewrite` creates a subgoal for every side condition, so we are left with the modified goal and the side condition.

```coq
  rewrite gmap_lookup_delete_ne.
```

:::: info Goals

```txt title="goal 1"
  m : gmap Z V
  k : Z
  v : V
  k' : Z
  Hne : k ≠ k'
  ============================
  k ≠ k'
```

```txt title="goal 2"
  m : gmap Z V
  k : Z
  v : V
  k' : Z
  Hne : k ≠ k'
  ============================
  <[k:=v]> m !! k' = delete k m !! k'
```

::::

```coq
  (* We could now write a structured proof with `{ proof1. } proof2.` or
  bullets. *)

Abort.

```

Let's demonstrate something else for this kind of simple side condition.

```coq
Lemma lookup_delete_ne_ex2 m k v k' :
  k ≠ k' →
  delete k (<[k := v]> m) !! k' = delete k m !! k'.
Proof.
  intros Hne.

```

`rewrite -> lem by t` causes it to succeed only if all side conditions can be proven with the tactic `t`. This is especially useful because if a side condition is false, the goal might become unprovable after applying the rewrite, and we want to avoid getting stuck in those situations (without realizing it).

Unfortunately Coq actually has two `rewrite` tactics: one from the standard library and one from a library called SSReflect; the latter is what we're using because it has some other useful features, but `rewrite ... by t` is only in the standard one. We can use the standard rewrite with `rewrite ->`.

```coq
  rewrite -> gmap_lookup_delete_ne by done.
```

:::: info Goal diff

```txt title="goal diff"
  m : gmap Z V
  k : Z
  v : V
  k' : Z
  Hne : k ≠ k'
  ============================
  delete k (<[k:=v]> m) !! k' = delete k m !! k' // [!code --]
  <[k:=v]> m !! k' = delete k m !! k' // [!code ++]
```

::::

It's more cumbersome but we can still assert that the side condition is proven with SSReflect's rewrite. The syntax here is `t; [ t1 | ]`, which runs `t2` only on the first goal from `t`. (You can also do `t; [ | t2 ]` or even `t; [ t1 |t2 ]`).

```coq
  rewrite gmap_lookup_delete_ne; [ done | ].
```

:::: info Goal diff

```txt title="goal diff"
  m : gmap Z V
  k : Z
  v : V
  k' : Z
  Hne : k ≠ k'
  ============================
  <[k:=v]> m !! k' = delete k m !! k' // [!code --]
  <[k:=v]> m !! k' = m !! k' // [!code ++]
```

::::

Another trick is to use `rewrite lem //`, and then only proceed if this leaves one goal. This won't work when you want a tactic more powerful than `done`.

```coq
  rewrite lookup_insert_ne //.
Qed.
```

If you're only going to remember one of these, I would use the first whenever you have a side condition. Hopefully someday the SSReflect `rewrite` supports a `by` clause...

```coq
End rewriting.

```

## Automation tactics

`lia` solves goals involving arithmetic (with `nat` or `Z`).

```coq
Lemma lia_example x y z :
  x + y - 3 < z →
  z - y <= 2 ->
  x < 5.
Proof. lia. Qed.

```

`auto` runs a proof search using hints that can be programmed with commands like `Hint Resolve`, for example. `auto` automatically tries to solve both sides of an `and`, introduces `forall`s, and tries to apply `P -> Q` in the context, but the programmed hints greatly affect what it can do. Solves the goal or does nothing.

`intuition` destructs ∧ in the hypotheses, splits ∧ in the goals, destructs ∨ in the hypotheses, looks for `H1: P → Q` and derives `Q` if it can prove `P` with `auto`, and finally calls `auto` to try to prove the goal. This is essentially all of the forward propositional reasoning above, plus `auto`. This is all relatively simple reasoning individually but collectively can be very powerful, especially because it also incorporates the power of `auto`.

**Note**: the tactic name `intuition`, confusingly, does not refer to an obvious or instinctive proof, but to _intuitionistic logic_. This is a version of logic in which doesn't use _classical logic_'s "excluded middle", which says that `∀ P, P ∨ ¬P` holds. For the most part you can ignore this distinction (if you ever need it, Coq does also support adding excluded middle as an axiom and working in classical logic.)

```coq
Lemma propositional_demo_3 (P Q R : Prop) :
  (P -> Q) ∧ (Q -> R) -> P -> R.
Proof.
  intuition.
Qed.

```

`set_solver` is a tactic from the [std++](https://gitlab.mpi-sws.org/iris/stdpp) library that automates solving many goals involving sets, with support for reasoning about `∈`, `∪` (union), `∩` (intersection), `s1 ∖ s2` (set subtraction), `⊆`, and equality between sets.

`done` solves "simple" goals with limited automation. Fails or solves the goal.

## Proof automation

This is a bigger topic than this reference can cover, but here are a few tactics you might see when reading code and a brief description.

### Tacticals

A "tactical" is a tactic that takes another tactic as an argument and modifies how it works.

`try t` runs `t` and catches any failures, doing nothing in that case.

`repeat t` runs `t` until it fails to make progress.

`progress t` runs `t` and fails if it doesn't make progress. (Think about `simpl` vs `progress simpl`.)

`solve [ t ]` runs `t` and fails if it doesn't solve the goal

`t1 || t2` runs `t1` and _if it fails to make progress_ runs `t2`.

`first [ t1 | t2 ]` runs `t1`, but if it fails instead runs `t2`.

`first t` runs `t` on the first subgoal. `t1; first t2` is the same as `t1; [ t2 | .. ]` (the `..` allows this to work regardless of how many additional subgoals there are, including none).

### Primitives

Some tactics make more sense to use from automation or with tacticals than in interactive use.

`fail <n> "msg"` fails and reports `msg`. `fail "msg"` is equivalent to `fail 0 "msg"`. The `n` is used to break through n levels of "catching" failures, so for example `try fail "msg"` does nothing, but `try fail 1 "msg"` breaks through the `try` and fails.

`idtac` does nothing. Can be useful when a tactic is required.

`idtac "msg"` prints a string to the responses output
