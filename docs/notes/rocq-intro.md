---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 2
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 2: Introduction to Rocq

> Follow these notes in Rocq at [src/sys_verif/coq/intro.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/coq/intro.v).

In this lecture, we'll introduce Rocq as a system, functional programming, and proving theorems about functional programs.

## Learning outcomes

By the end of this lecture, you should be able to

1. Interact with the Rocq prover
2. Implement functions with pattern matching and recursion
3. Prove simple theorems about functions

## Rocq as an interactive theorem prover

The Rocq prover is a lot like a programming language, but it is fundamentally _interactive_ in a way that is unlike programming languages you've used. The interaction is necessary to write theorems, but understanding the interaction model is an important part of how you will write definitions, find already proven lemmas, and debug type errors.

::: info Rocq vs Coq

Rocq was formerly called Coq, with the name change implemented around January 2025. See the [note on the Rocq website](https://rocq-prover.org/about#Name). You will still see references to Coq, in particular in Software Foundations.

:::

Three programming languages: terms, vernacular, tactics

- Calculus of inductive constructions is the theory behind the term language.
- Due to dependent types, there is no distinction between terms and types; it's all the same language.
- Vernacular is a sequence of stateful commands. They create definitions, change attributes. They can also be queries which don't affect the state but help you write code. When you use Rocq interactively, you've executed a prefix of the vernacular commands. You can move forward and backward, undoing commands.
- When you are done with a development, you generally re-run Rocq in "batch mode" like a compiler, which runs the same vernacular commands and produces a compiled output file. This is needed to make sure everything gets checked, and because Rocq uses those outputs when it needs to import another file.
- Vernacular commands create new types, definitions, and start proofs. Creating new types is especially interesting.
- Tactics are used to prove theorems. This is yet another language (quite different from both vernacular and terms) that is stateful. At any point in a proof, you have N goals left. Tactics make progress or solve goals. Once a theorem is proven, you can generally ignore how it was proven; only the statement matters. However, the tactics are also code that is subject to maintenance as definitions/theorems change.

## Functional programming

To write functional programs, we'll start by defining some data types for our functions to operate on. This is an "enumerated type". It defines `day`, and seven constructors for that type.

```rocq
Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

```

Now what we have `day`, we can define functions on days:

```rocq
(** next_weekday is a simple example of a function operating on [day] *)
Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

```

Rocq has a number of commands for interacting with the system while it's running. The first one we'll see is `Compute` below, which allows us to manually check the behavior of the function we just defined.

```rocq
Compute (next_weekday friday).
```

:::: note Output

```txt title="rocq output"
     = monday
     : day
```

::::

The main use of Rocq is to prove theorems - it is a proof assistant after all. We'll get to more interesting theorems shortly, but for now let's prove a "unit test" theorem.

NOTE: Theorem/Lemma/Example are all synonyms. In this class we'll try to stick to Lemma.

```rocq
Lemma next_weekday_test : next_weekday (next_weekday friday) = tuesday.
Proof.
  simpl.
```

:::: info Goal

```txt title="goal 1"
  ============================
  tuesday = tuesday
```

::::

```rocq
  reflexivity.
Qed.

```

## Booleans and the usual functions

```rocq
Module BooleanPlayground.

Inductive bool : Type :=
| true
| false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Lemma test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Lemma test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Lemma test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

```

Note `if` is an _expression_ and not a _statement_ (there are no statements). Like Rust but not C or Go. Python has both (`if:` vs `e1 if b else e2`).

```rocq
Definition negb' (b: bool) : bool :=
  if b then false else true.
Definition andb' (b1 b2: bool) : bool :=
  if b1 then b2 else false.

```

Note on `if`: since booleans aren't built-in, and we just defined `bool` above, Rocq's `if` expression works for any type with two constructors. Just to convince you `andb'` has the same behavior as `andb` above.

```rocq
Lemma andb'_eq_andb : forall b1 b2, andb' b1 b2 = andb b1 b2.
Proof.
  intros b1 b2.
  (* this proof is not important right now *)
  destruct b1, b2; simpl; reflexivity.
Qed.

```

### In-class exercise: decoding type errors

Think about these two errors on your own and try to explain how they were produced. What is needed to fix each?

```rocq
Fail Definition complex_expr1 (b1 b2 b3: bool) :=
  orb (andb' b2 false) (andb (orb (b1)) (b3)) b2.
(*
Error:
In environment
b1 : bool
b2 : bool
b3 : bool
The term "orb b1" has type "bool -> bool" while it is expected to have type "bool".
 *)

Fail Definition complex_expr2 b1 b2 b3 :=
  andb (andb b1 (b2 (orb b3 b1))) b2.
(*
Error:
In environment
b1 : bool
b2 : bool -> bool
b3 : bool
The term "b2" has type "bool -> bool" while it is expected to have type "bool".
*)

End BooleanPlayground.

```

## Tuple types

```rocq
Module TuplePlayground.

Inductive bit : Type :=
| B1
| B0.

```

A single constructor with multiple parameters creates a "tuple" type (in PL called a "product" type). Rocq has syntactic sugar for "record types" that extend this feature slightly.

```rocq
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
```

:::: note Output

```txt title="rocq output"
     = false
     : bool
```

::::

```rocq
Compute (all_zero (bits B0 B0 B0 B0)).
```

:::: note Output

```txt title="rocq output"
     = true
     : bool
```

::::

```rocq
End TuplePlayground.

```

## Natural numbers

```rocq
Module NatPlayground.

```

So far, every type has finitely many values. For infinite types, we need something more.

```rocq
Inductive nat : Type :=
| O
| S (n: nat).

```

There's a lot to unpack here.

First, what values does `nat` have? It produces the numbers `O`, `S O`, `S (S O)`, which we will interpret as 0, 1, 2, ....

Second, this _defines_ `nat`, `O : nat`, and `S : nat -> nat`, but doesn't give them any meaning - we'll do that as humans reading the code, and via the functions we define.

Another definition of numbers that we could use to mean the same thing:

```rocq
Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

End NatPlayground.

```

## Proof strategy

We'll do another exercise to get you thinking about how to approach a proof.

You will always have two challenges in completing a proof in this class: (1) why is the theorem true?, and (2) how do we turn that into a Rocq proof?. It's extremely helpful to understand the distinction to be able to develop these skills independently.

Let's go back to our `day` type.

```rocq
Definition next_day (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

```

Proving an [exists] is complicated and we'll have more to say, but try to think through this intuitively for now.

```rocq
Lemma wednesday_has_prev_day : exists d, next_day d = wednesday.
Proof.
  exists tuesday.
  simpl. reflexivity.
Qed.

```

## In-class exercise: informal proof

Now let's prove something more interesting: every day has a previous day.

Think-pair-share and come up with an informal proof strategy. Then I'll show how to translate it to a Rocq proof.

```rocq
Lemma every_day_has_prev : forall d, exists d', next_day d' = d.
Proof.
  (* Goal is a forall, so introduce it. *)
  intros d.
Abort.

```

## Option monad

This section introduces two more core features of functional programming: polymorphic types (also called "generics" in other languages) and "higher-order functions" (functions that take other functions as parameters).

```rocq
Module Option.


```

`option` is a polymorphic type: it takes a type `A` as an argument, and (maybe) contains a value of that arbitrary type. `option A` is the simplest "container" type.

```rocq
  Inductive option (A: Type) :=
  | Some (x: A)
  | None.


```

Here are some functions you can define on `option`. There are good motivations for _why_ you should define these particular ones, but we won't get into that (and it isn't all that important for this class). For now, just try to understand the behavior. `map` runs `f` "inside" the optional value.

```rocq
  Definition map {A B} (ma: option A) (f: A -> B) : option B :=
    match ma with
    | Some _ x => Some B (f x)
    | None _ => None B
    end.


```

Notice the extra type argument we had to provide to `Some`, and the somewhat odd `_` in the pattern match. To make it easier to work with polymorphic functions, Rocq has a feature called _implicit arguments_. These commands modify how type inference treats `Some` and `None`, making the type argument implicit (that's what the curly braces mean). Don't worry about the syntax; you won't need to do this yourself.

```rocq
  Arguments Some {A} x.
  Arguments None {A}.


```

We'll now define `return_` (it should be called `return` but that's a Rocq keyword) and `bind`. These make `option` into a _Monad_ but you don't need to understand that, just read the definitions.

```rocq
  Definition return_ {A} (x: A) : option A := Some x.

  Definition bind {A B} (ma: option A) (f: A -> option B) : option B :=
    match ma with
    | Some x => f x
    | None => None
    end.


```

These are some properties of `return_` and `bind` (again, good reason for these but not relevant here).

```rocq
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

## More proof tactics

```rocq
Module MoreNatProofs.

Lemma add_0_l n :
  0 + n = n.
Proof.
  simpl. (* Works because [add] pattern matches on the first argument. *)
  reflexivity.
Qed.

```

The above proof is a "proof by computation" which followed from the definition of `add`. We'll now go through some "propositional" proofs that follow from the rules for manipulating logical AND (`∧`) and OR (`∨`).

```rocq
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

Rocq allows you to write `intros` without arguments, in which case it will automatically select names. We strongly recommend in this class to always give names, since it makes your proof easier to read and modify, as well as making it easier to read the context while you're developing a proof.

```rocq
Lemma eq_add_O_2 n m :
  n = 0 -> m = 0 -> n + m = 0.
Proof.
  (** The goal is an implication, and we can "introduce" an hypothesis with the
  [intros] tactic - notice the effect on the goal *)
  intros Hn.
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

```rocq
  intros Hm.


```

`rewrite` is another fundamental proof technique

```rocq
  rewrite Hn.
```

:::: info Goal diff

```txt title="goal diff"
  n, m : nat
  Hn : n = 0
  Hm : m = 0
  ============================
  n + m = 0 // [!code --]
  0 + m = 0 // [!code ++]
```

::::

```rocq
  rewrite Hm.
  simpl.
  reflexivity.
Qed.

```

This lemma is a proof of a disequality, a "not equals". Even this isn't built-in to Rocq but built from simpler primitives.

```rocq
Lemma neq_succ_0 n :
  S n <> 0.
Proof.
  (* Wade through the sea of notation *)
  Locate "<>".
```

:::: note Output

```txt title="rocq output"
Notation "x <> y  :> T" := (not (eq x y)) (* T in scope _type_scope *)
  : type_scope (default interpretation) (from Corelib.Init.Logic)
Notation "x <> y" := (not (eq x y)) : type_scope (default interpretation)
  (from Corelib.Init.Logic)
```

::::

```rocq
  Locate "~".
```

:::: note Output

```txt title="rocq output"
Notation "~ x" := (not x) (* x in scope _type_scope *) : type_scope
  (default interpretation) (from Corelib.Init.Logic)
```

::::

```rocq
  Print not.
```

:::: note Output

```txt title="rocq output"
not = fun A : Prop => A -> False
     : Prop -> Prop

Arguments not A%_type_scope
```

::::

```rocq
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

End MoreNatProofs.
```
