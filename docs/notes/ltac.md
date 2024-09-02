---
# Auto-generated from literate source. DO NOT EDIT.
order: -2
---

# Ltac reference

```coq
From sys_verif Require Import options.

From stdpp Require Import gmap.

```

## Propositional logic

`intros`, `apply`, `assumption`, `intuition`.

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

An automated proof using a solver.

```coq
Lemma propositional_demo_3 (P Q R : Prop) :
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intuition auto.
Qed.

```

You'll almost always want to use `intuition auto` - `intuition` takes another
tactic to use for solving side conditions but `auto` is a good choice.

Note: the tactic name `intuition`, confusingly, does not refer to an obvious or
instinctive proof, but to _intuitionistic logic_. This is a version of logic in
which doesn't use _classical logic_'s "excluded middle", which says that `∀ P, P
∨ ¬P` holds.  For the most part you can ignore this distinction, and Coq
supports assuming the law of excluded middle and thus using classical logic.
## Rewriting

Rewriting is the act of using `a = b` to replace `a` with `b`. It's a powerful
and useful proof technique.

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
It's a seemingly small change but the left and right-hand sides are now
  equal!

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

###  rewrite !

```coq
Lemma lookup_delete_ex2 m k v :
  delete k (<[k := v]> m) !! k = delete k m !! k.
Proof.
  
```

`rewrite !lem` rewrites `lem` one or more times (fails if it never
  applies)

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

###  rewrite //

```coq
Lemma lookup_delete_ex3  m k v :
  delete k (<[k := v]> m) !! k = delete k m !! k.
Proof.
  
```

The `//` is an _action_ that tries to prove "trivial" goals (or subgoals
  from rewrite side conditions). We can use it to give a one-line proof.

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

This lemma to rewrite with has a premise or _side condition_: it only
  applies if the two keys involved are not equal. By default, `rewrite` creates
  a subgoal for every side condition, so we are left with the modified goal and
  the side condition.

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

Let's demonstrate something else for this kind of simple side
  condition.

```coq
Lemma lookup_delete_ne_ex2 m k v k' :
  k ≠ k' →
  delete k (<[k := v]> m) !! k' = delete k m !! k'.
Proof.
  intros Hne.
  
```

Adding `by t` to a `rewrite` causes it to succeed only if all side
  conditions can be proven with the tactic `t`. This is especially useful
  because if a side condition is false, the goal might become unprovable after
  applying the rewrite, and we want to avoid getting stuck in those situations
  (without realizing it).

  Unfortunately Coq actually has two `rewrite` tactics: one from the standard
  library and one from a library called SSReflect; the latter is what we're
  using because it has some other useful features, but `rewrite ... by t` is
  only in the standard one. We can use the standard rewrite with `rewrite ->`.


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
  <[k:=v]> m !! k' = delete k m !! k' // [!code --]
  delete k (<[k:=v]> m) !! k' = delete k m !! k' // [!code ++]
```
::::
It's more cumbersome but we can still assert that the side condition is
  proven with SSReflect's rewrite. The syntax here is `t; [ t1 | ]`, which runs
  `t2` only on the first goal from `t`. (You can also do `t; [ | t2 ]` or even
  `t; [ t1 |t2 ]`).

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
  <[k:=v]> m !! k' = delete k m !! k'
```
::::
Another trick is to use `rewrite lem //`, and then only proceed if this
  leaves one goal. This won't work when you want a tactic more powerful than
  `done`.

```coq
rewrite lookup_insert_ne //.
Qed.
```

If you're only going to remember one of these, I would use the first
  whenever you have a side condition. Hopefully someday the SSReflect
  `rewrite` supports a `by` clause...

```coq
End rewriting.
```

