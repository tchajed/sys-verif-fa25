---
order: 2
shortTitle: "Assignment 1: Coq"
icon: file-lines
---

# Assignment 1: Coq

This assignment has two purposes:

1. Learn how to use Coq to prove theorems. This is a skill you'll build on and use to verify programs in the rest of the class, so it's important you put enough practice in now.
2. Practice verifying functional programs. The nice thing about this domain is that we can start with small programs and specs. Functional programs themselves are often used in the _specifications_ of more complex imperative programs, so it's also a way to practice the functional style of programming.

## Part 0: setup

The [main assignments page](../) has instructions on getting the sys-verif-fa24-proofs repo and Coq set up. Follow those first.

::: warning
You might run into unexpected difficulties with installing the software, so do it early and ask for help quickly if you get stuck. It isn't a goal of the class to teach you to install software, but it is necessary to make progress on anything else.
:::

## Part 1: Basics from Software Foundations

First, you'll read [Basics](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html), the first chapter of the online textbook Software Foundations, and do the exercises there. Do the exercises in the Basics.v file in the proofs repo. The online version is the same as the Coq version, just with a pretty HTML rendering.

Only two parts of this chapter are optional:

- You can skip the "Fixpoints and Structural Recursion" section.
- We aren't using the autograder described in "Testing your solutions". To test your solutions in this class just run `make` (in the VS Code terminal if you're using Docker). Please make sure your code compiles before submitting; use `Admitted` to end proofs you didn't finish (and check that you didn't unintentionally leave something admitted).

::: important
This chapter has a lot of small, easy exercises to get you practice. If these are difficult, that's a bad sign. If they're easy, note that proofs will become more difficult quickly after this.
:::

## Part 2: verifying functional programs

TODO: provide additional exercises
