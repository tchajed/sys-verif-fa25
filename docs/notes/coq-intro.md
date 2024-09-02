---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
order: 2
---

# Lecture 2: Introduction to Coq

In this lecture, we'll get an introduction to functional programming and see
how Coq supports both writing and verifying functional programs.

To write functional programs, we'll start by defining some data types for
our functions to operate on.

```coq
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

```coq
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

Coq has a number of commands for interacting with the system while it's
running. The first one we'll see is `Compute` below, which allows us to manually
check the behavior of the function we just defined.

```coq
Compute (next_weekday friday).
```


:::: note Output
```txt title="coq output"
     = monday
     : day
```
::::
The main use of Coq is to prove theorems - it is a proof assistant after
all. We'll get to more interesting theorems shortly, but for now let's prove a
"unit test" theorem.

```coq
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

```coq
  reflexivity.
Qed.
```

