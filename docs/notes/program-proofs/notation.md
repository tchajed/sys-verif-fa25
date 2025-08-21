---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
---

# Notation

Coq has a very general mechanism for extending its syntax with what are called "notations". Even if you don't write your own notations, you'll work with them, so it's helpful to understand some aspects of their implementation.

For more details beyond this document you can read the Coq reference manual documentation on [syntax extensions](https://coq.inria.fr/doc/master/refman/user-extensions/syntax-extensions.html).

## A first example

Let's start with an example; we'll write our own list type `List` and give it notations with a slightly different syntax than the `[1; 2; 3]` notation for normal `list`s. Ignore the 6 commands of setup for now and look at the overall effect in the examples.

```rocq
Inductive List {A:Type} :=
| Nil
| Cons (x: A) (l: List).
Arguments List A : clear implicits.

Declare Scope angle_list_scope.
Delimit Scope angle_list_scope with A.
Open Scope angle_list_scope.

Notation "<>" := Nil : angle_list_scope.
Notation "<< x >>" := (Cons x Nil) : angle_list_scope.
Notation "<< x ; y ; .. ; z >>" := (Cons x (Cons y .. (Cons z Nil) .. ))
  (format "<< '[' x ;  '/' y ;  '/' .. ;  '/' z ']' >>") : angle_list_scope .

```

The notations have extended Coq's syntax:

```rocq
Definition ex1: List bool := <>.
Definition ex2: List Z := << 1; 34; 4; 7 >>.

```

Not only that, but Coq will use these notations in _reverse_ for printing as well:

```rocq
Print ex2.
```

:::: note Output

```txt
ex2 = <<1; 34; 4; 7>>
     : List Z
```

::::

The notations are truly being used for printing; it's not just that printing `ex2` shows how the term was defined. Here's an example where we write a list without the notation but it gets printed with it:

```rocq
Check (Cons 1 (Cons 3 (Cons 7 Nil))).
```

:::: note Output

```txt
<<1; 3; 7>>
     : List Z
```

::::

## How notations work

The most important aspect of notations to remember is that they are organized into _scopes_ so they can be selectively enabled and to pick between two different interpretations of the same notation. For the notations above, we used `Declare Scope angle_list_scope` to create a new scope.

A typical example is the numeric notations, where the notation for `nat` numbers is defined in scope `nat_scope` while for `Z` is defined in `Z_scope`. There is a **scope stack** that determines what scopes are "open" and in what order, which determines what notation is used by default. For the notations above, we wanted them to be available right away so we used `Open Scope angle_list_scope`.

Currently, due to the import of Zarith at the top of the file, numbers are parsed as `Z`. The syntax `e%nat` parses `e` but with `nat` as the first scope, which allows us to override the default temporarily to parse a literal as a `nat`.

```rocq
Check 3 : Z.
Check 3%nat : nat.

```

Unfortunately this override mechanism requires yet another concept of a **scope delimiting key**. The above command `Delimit Scope angle_list_scope with A` says that `%A` should be used for `angle_list_scope`; similarly `%nat` is used for `nat_scope` and `%Z` is used for `%Z_scope`. If we didn't have `angle_list_scope` open, we could still use it with the delimiting key:

```rocq
Close Scope angle_list_scope.

Fail Definition ex3 := << 3 >>.
Definition ex3': List Z := << 3 >>%A.

(* the scope is used for the whole expression, so we don't have to put `%nat` on
each number individually. *)
Definition ex4: List nat := << 3; 4; 5 >>%nat%A.

```

There are a few more details about notations you should know, although I won't detail how to use them.

Some of the syntax you use routinely in Coq is actually not built-in but provided as notations; for example, the pair notation `(x, y)` (actually even the `pair` data type isn't built-in). The most surprising one might be that `A -> B` is actually notation for `forall (_: A), B`, but this starts getting into dependent types which I won't explain here.

Notations extend the Coq parser (which is based on the camlp5 library) at runtime. This makes it complicated to describe what's required for notations to be parseable (without ambiguity for example), and to give good error messages. One aspect that might help is to note that when notations are created, they create new tokens in the parser (really, the lexer) for the sequences of symbols (like `<<` and `>>` above) and any newly-created keywords.

Notations can be recursive, like the `<< x ; y ; .. ; z >>` list notation above.

The way notations are printed can be customized; specifically, we can control whitespace, how line breaks are inserted, and indentation if a notation overflows a line while printing. This is what enables large multi-line notations that are still printed nicely. You can actually see an example of such control above in the `format` specifier for the recursive list notation. That one is copied from Coq's built-in list notation; one of the things it does is to break up a long list by putting a newline between elements, after each semicolon, and without indentation.

Notations are by default used for printing and parsing, as we saw above. They can be defined as _parsing only_ or _printing only_ instead. We might have one general notation used for printing things, but several shorthands that are useful to save typing. Printing-only notations are a bit more obscure. In the Iris Proof Mode they're used to create the goal displays you see. It turns out the goals are just an ordinary Coq proposition that the IPM tactics manipulate, but with a (fairly fancy) printing-only notation.

The numeric notations are subject to scoping, but the way they're defined uses some features specific to parsing numbers; obviously there isn't a `Notation` command for every possible number literal. See the documentation on [number notations](https://coq.inria.fr/doc/master/refman/user-extensions/syntax-extensions.html#number-notations) for the interface Coq provides.

## Controlling notation scope

Coq has some features that allow controlling the notation scope without requiring an annotation like `%nat`. Unfortunately, these can be a bit confusing if you don't know about them, since they silently change how things are parsed.

The first is that notation scopes can be attached to types. This has already been done for `nat`, but here's the command that does it:

```rocq
Bind Scope nat_scope with nat.

```

Now, if an argument to a function is known to be of type nat (because of the function's type), then the expression we put there will be parsed in `nat_scope`. In the following example, the constant `3` would normally be parsed as a Z except for the type of `Nat.add` and the scope binding.

```rocq
Definition use_nat_add (x: nat) := Nat.add x 3.

```

This example uses the same feature in a slightly different way. The notation `x + y` is ambiguous (it could be `Z.add` or `Nat.add`), and `Z.add` is the default. Because of the return type annotation here, `x + y` gets parsed as a `nat` addition.

```rocq
Definition use_nat_plus (x y: nat): nat := x + y.
```

In Iris specifically this is commonly why we write `: iProp Σ` for proposition definitions, since it causes them to be parsed in the correct scope to disambiguate the logical operators like `∀` and `∃`; `iProp` is associated with `bi_scope`. Sometimes nothing else causes `bi_scope` to be used and you'll need to write `%I` explicitly.

As one last scope control feature, it's also possible to associate a notation scope to each argument of a definition, regardless of the types involved. If you ever need to see what these are, you can use `About` which includes scope info.

```rocq
Definition takes_nat_scope {A: Type} (x: A) := x.
Arguments takes_nat_scope {A} x%nat.
Check takes_nat_scope 3 : nat.

```

The relevant part of the About output is `Arguments takes_nat_scope {A} x%nat_scope`, in which `x%nat_scope` means that argument will be parsed in `nat_scope`.

```rocq
About takes_nat_scope.
```

:::: note Output

```txt
takes_nat_scope : ∀ {A : Type}, A → A

takes_nat_scope is not universe polymorphic
Arguments takes_nat_scope {A} x%nat_scope
takes_nat_scope is transparent
Expands to: Constant __input.takes_nat_scope
Declared in library __input, line 42, characters 11-26
```

::::
