---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 3
---

# Lecture 3: Induction

## Learning outcomes

By the end of this lecture, you should be able to

1. Prove theorems about `nat`s with induction
2. Translate informal proof to tactics


```coq
Set Default Goal Selector "!".

```

## Review exercise: safe vs unsafe tactics (part 1)

Recall some tactics we saw last lecture:

- `intros`
- `reflexivity`
- `rewrite`
- `simpl`
- `exists` (provides a witness when the goal is `exists (x: T), P x`)

Define an **unsafe tactic** as one that can turn a true goal into an unprovable
(false) goal. Define a **safe tactic** as a not unsafe tactic (bonus exercise: how to
state that?).

Which of the above goals are safe? Why?
## Proofs about recursive functions

```coq
Module NatDefs.
  Inductive nat : Type :=
  | O
  | S (n: nat).

  Fixpoint add (n1: nat) (n2: nat) : nat :=
    match n1 with
    | O => n2
    (* notice _shadowing_ of [n1] *)
    | S n1 => S (add n1 n2)
    end.
End NatDefs.

Module MoreNatProofs.

Lemma add_0_l n :
  0 + n = n.
Proof.
  simpl. (* Works because [add] pattern matches on the first argument. *)
  reflexivity.
Qed.

```

The above proof is a "proof by computation" which followed from the
definition of `add`. The reverse doesn't follow from just computation: `add`
pattern matches on `n`, but it's a variable. Instead, we need to prove this by
induction:


```coq
Lemma add_0_r_failed n :
  n + 0 = n.
Proof.
  destruct n as [|n].
  - simpl.
    reflexivity.
  - simpl.
    (* do this again?? *)
    destruct n as [|n].
Abort.

```

Recall the _principle of induction_: if $P$ is some property of natural
numbers and we want to prove $\forall n, P(n)$, then we can do the proof as
follows:

- **base case:** show that $P(0)$ is true
- **inductive step:** for any $n'$, assume $P(n')$ and prove $P(1 + n')$.

From these two we conclude exactly what we wanted: $\forall n, P(n)$.

This is exactly what we can do with the `induction` tactic. What Coq will do for us is
infer the property of `n` we're proving based on the goal.


```coq
Lemma add_0_r n :
  n + 0 = n.
Proof.
  induction n as [|n IHn].
  - (* base case *)
    simpl.
    reflexivity.
  - (* inductve step, with [IHn] as the inductive hypothesis *)
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

```

We'll now go through some "propositional" proofs that follow from the rules for
manipulating logical AND (`∧`) and OR (`∨`).

First, let's just recall the rules with toy examples. In these examples, `P`,
`Q`, `R` will be used as arbitrary "propositions" - for the intuition it's
sufficient to think of these as boolean-valued facts that can be true or false.
They would be things like `n = 3` or `n < m`. The reason they aren't booleans in
Coq is a deep theoretical one we won't worry about.


```coq
Lemma or_intro_r (P Q R: Prop) :
  Q -> P \/ Q.
Proof.
  intros HQ.
  
```

Pick the right disjunct to prove. Similarly, `left` would leave use to
  prove `P`.

```coq
right.
  assumption.
Qed.

Lemma or_elim (P Q R: Prop) :
  (P -> R) ->
  (Q -> R) ->
  (P \/ Q) -> R.
Proof.
  intros HR1 HR2 H.
  
```

`destruct` on H, which is an `∨`, leaves us with two goals: why? what are
  they?

```coq
destruct H as [HP | HQ].
```


:::: info Goals
```txt title="goal 1"
  P, Q, R : Prop
  HR1 : P -> R
  HR2 : Q -> R
  HP : P
  ============================
  R
```

```txt title="goal 2"
  P, Q, R : Prop
  HR1 : P -> R
  HR2 : Q -> R
  HQ : Q
  ============================
  R
```

::::

```coq
  - apply (HR1 HP).
  - apply (HR2 HQ).
Qed.

Lemma and_intro P Q :
  P ->
  Q ->
  P /\ Q.
Proof.
  intros HP HQ.
  
```

`split` turns a proof of A ∧ B into two separate goals

```coq
split.
```


:::: info Goals
```txt title="goal 1"
  P, Q, R : Prop
  HR1 : P -> R
  HR2 : Q -> R
  HQ : Q
  ============================
  R
```

```txt title="goal 2"
  P, Q : Prop
  HP : P
  HQ : Q
  ============================
  P
```

::::

```coq
  - assumption.
  - assumption.
Qed.

Lemma and_elim_r P Q :
  (P /\ Q) -> Q.
Proof.
  intros H.
  
```

`destruct` on an `∧` has a very different effect - why?

```coq
destruct H as [HP HQ]. (* {GOALS DIFF} *)
  apply HQ.
Qed.

```

### Proof trees

On board: we can visualize the effect of each of these strategies as a _proof
tree_.


### Back to nat

```coq
Lemma O_or_succ n :
  n = 0 \/ n = S (Nat.pred n).
Proof.
  destruct n as [ | n']. (** Make a case distinction on [n]. *)
  - (** Case [n = 0] *)
    left.
    reflexivity.
  - (** Case [n = S n'] *)
    right.
    simpl. (** [pred (S n')] simplifies to [n']. *)
    reflexivity.
Qed.

```

This proof uses `intros` and `rewrite`.

Coq allows you to write `intros` without arguments, in which case it will
automatically select names. We strongly recommend in this class to always give
names, since it makes your proof easier to read and modify, as well as making it
easier to read the context while you're developing a proof.

```coq
Lemma eq_add_O_2 n m :
  n = 0 -> m = 0 -> n + m = 0.
Proof.
  (** The goal is an implication, and we can "introduce" an hypothesis with the
  [intros] tactic - notice the effect on the goal *)
  intros Hn.
```


:::: info Goal diff
```txt title="goal diff"
  P, Q : Prop
  HP : P
  HQ : Q
  ============================
  P // [!code --]
  Q // [!code ++]
```
::::

```coq
  intros Hm.

  
```

`rewrite` is another fundamental proof technique

```coq
rewrite Hn.
```


:::: info Goal diff
```txt title="goal diff"
  n, m : nat
  Hn : n = 0 // [!code ++]
  ============================
  n = 0 -> m = 0 -> n + m = 0 // [!code --]
  m = 0 -> n + m = 0 // [!code ++]
```
::::

```coq
  rewrite Hm.
  simpl.
  reflexivity.
Qed.

```

This lemma is a proof of a disequality, a "not equals". Even this isn't
built-in to Coq but built from simpler primitives.

```coq
Lemma neq_succ_0 n :
  S n <> 0.
Proof.
  (* Wade through the sea of notation *)
  Locate "<>".
```


:::: note Output
```txt title="coq output"
goal 1 is:
  
  n, m : nat
  Hn : n = 0
  Hm : m = 0
  ============================
  n + m = 0
```
::::

```coq
  Locate "~".
```


:::: note Output
```txt title="coq output"
goal 1 is:
  
  n, m : nat
  Hn : n = 0
  Hm : m = 0
  ============================
  0 + m = 0
```
::::

```coq
  Print not.
```


:::: note Output
```txt title="coq output"
Notation "x <> y  :> T" := (not (eq x y)) : type_scope
  (default interpretation)
Notation "x <> y" := (not (eq x y)) : type_scope (default interpretation)
```
::::

```coq
  (** We see that [a <> b] is notation for [not (a = b)], which is by definition
  [a = b -> False]. *)

  unfold not.

  (** Since our goal is an implication, we use [intros]: *)
  intros Hn.

  (** It is impossible for [S ...] to be equal to [0], we can thus derive
  anything, including [False], which is otherwise never provable. The
  [discriminate] tactic looks for an impossible equality and solves any goal by
  contradiction. *)
  discriminate.
Qed.

Lemma succ_pred n : n <> 0 -> n = S (Nat.pred n).
Proof.
  intros Hn.
  destruct (O_or_succ n) as [H0|HS].
  - unfold not in Hn.
    (* There are a few different ways to proceed. Here's one: *)
    exfalso. (* [exfalso] encodes the strategy of proving [False] from the
    current hypotheses, from which the original conclusion follows (regardless
    of what it is). *)
    apply Hn.
    assumption.
  - assumption.
Qed.

```

Here's a toy example to illustrate what using and proving with AND looks
like.

```coq
Lemma and_or_example (P Q: Prop) :
  (P /\ Q) \/ (Q /\ P) -> P /\ Q.
Proof.
  intros H.
  destruct H as [H | H].
  - assumption.
  - destruct H as [HQ HP].
    split.
    + assumption.
    + assumption.
Qed.

Lemma add_O_iff n m :
  (n = 0 /\ m = 0) <-> n + m = 0.
Proof.
  Locate "<->".
```


:::: note Output
```txt title="coq output"
Notation "~ x" := (not x) : type_scope (default interpretation)
```
::::

```coq
  unfold iff.
  split.
  - intros [Hn Hm].
    subst.
    reflexivity.
  - intros H.
    destruct n as [|n].
    + rewrite add_0_l in H.
      split.
      { reflexivity. }
      assumption.
    + simpl in H.
      (* in the rest of this class, more commonly [congruence] *)
      discriminate.
Qed.

```

You can see the use of bullets `-` and `+` to structure the proof above. You
can also use `{ ... }` (used once above), which are often preferred if the proof
of the first subgoal is small compared to the rest of the proof (such as the
single-line `{ reflexivity. }` above).
## Exercise: safe vs unsafe tactics

```coq
Lemma add_comm n1 n2 :
  n1 + n2 = n2 + n1.
Proof.
  induction n1 as [|n1 IHn].
  - simpl.
    
```

An important part of your job in constructing both the informal and
    formal proof is to think about how previously proven (by you or someone
    else) lemmas might help you. In this case we did this part of the proof
    above.

```coq
rewrite add_0_r.
    reflexivity.
  - simpl.
    
```

### Exercise: what lemma to prove?

```coq
Abort.



```

Think before looking ahead.

```coq
Lemma add_succ_r n1 n2 :
  n1 + S n2 = S (n1 + n2).
Proof.
  induction n1 as [|n1 IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma add_comm n1 n2 :
  n1 + n2 = n2 + n1.
Proof.
  induction n1 as [|n1 IHn].
  - simpl.
    
```

An important part of your job in constructing both the informal and
    formal proof is to think about how previously proven (by you or someone
    else) lemmas might help you. In this case we did this part of the proof
    above.

```coq
rewrite add_0_r.
    reflexivity.
  - simpl.
    rewrite add_succ_r. (* now go use the lemma we factored out *)
    rewrite IHn.
    reflexivity.
Qed.

End MoreNatProofs.

```

## Option monad

This section introduces two more core features of functional programming:
polymorphic types (also called "generics" in other languages) and "higher-order
functions" (functions that take other functions as parameters).



```coq
Module Option.

  
```

`option` is a polymorphic type: it takes a type `A` as an argument, and
  (maybe) contains a value of that arbitrary type. `option A` is the simplest
  "container" type.

```coq
Inductive option (A: Type) :=
  | Some (x: A)
  | None.

  
```

Here are some functions you can define on `option`. There are good
  motivations for _why_ you should define these particular ones, but we won't
  get into that (and it isn't all that important for this class). For now, just
  try to understand the behavior.
`map` runs `f` "inside" the optional value.

```coq
Definition map {A B} (ma: option A) (f: A -> B) : option B :=
    match ma with
    | Some _ x => Some B (f x)
    | None _ => None B
    end.

  
```

Notice the extra type argument we had to provide to `Some`, and the
  somewhat odd `_` in the pattern match. To make it easier to work with
  polymorphic functions, Coq has a feature called _implicit arguments_.
These commands modify how type inference treats `Some` and `None`, making
  the type argument implicit (that's what the curly braces mean). Don't worry
  about the syntax; you won't need to do this yourself.

```coq
Arguments Some {A} x.
  Arguments None {A}.

  
```

We'll now define `return_` (it should be called `return` but that's a Coq
  keyword) and `bind`. These make `option` into a _Monad_ but you don't need
  to understand that, just read the definitions.

```coq
Definition return_ {A} (x: A) : option A := Some x.

  Definition bind {A B} (ma: option A) (f: A -> option B) : option B :=
    match ma with
    | Some x => f x
    | None => None
    end.

  
```

These are some properties of `return_` and `bind` (again, good reason for
  these but not relevant here).

```coq
Lemma return_left_id {A B} (x: A) (f: A -> option B) :
    bind (return_ x) f = f x.
  Proof. reflexivity. Qed.

  Lemma return_right_id {A} (ma: option A) :
    bind ma return_ = ma.
  Proof. destruct ma; reflexivity. Qed.

  Lemma bind_assoc {A B C} (ma: option A) (f: A -> option B) (g: B -> option C) :
    bind (bind ma f) g = bind ma (fun x => bind (f x) g).
  Proof. destruct ma; reflexivity. Qed.

End Option.
```

