---
order: 2
shortTitle: "Assignment 1"
icon: file-lines
date: 2024-09-04 08:00:00 -5
---

# Assignment 1: Rocq

This assignment has two purposes:

1. Learn how to use Rocq to prove theorems. This is a skill you'll build on and use to verify programs in the rest of the class, so it's important you put enough practice in now.
2. Practice with functional programs. This is a warm up to imperative and concurrent programs as well as useful on its own, since functional programs are often used in the _specification_ of imperative programs.

## Submitting

See [submitting assignments](./setup#submitting-assignments) on the assignment setup page.

**The assignment is due Tuesday, Oct 1st at 11pm.** However, you are welcome and encouraged to submit early with partial progress to keep me informed of how the class is doing. If you have questions, just mention them briefly in the Canvas submission so I know to look.

I would recommend aiming to finish parts 0 and 1 by Tuesday, Sep 17th to be on track.

## Part 0: setup

The [assignment setup page](./setup) has instructions on getting the sys-verif-fa25-proofs repo and installing Rocq. Follow those first.

::: warning

You might run into unexpected difficulties with installing the software, so do it early and ask for help quickly if you get stuck. It isn't a goal of the class to teach you to install software, but it is necessary to make progress on anything else.

:::

## Part 1: Software Foundations exercises

We'll use the free online textbook Software Foundations to learn the basics of using the Rocq prover to prove theorems. You'll read the three early chapters ([Basics](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html), [Induction](https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html), and [Logic](https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html)) and do (a selection of) the exercises in Rocq. I also strongly encourage you to look at the [Polymorphism](https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html) chapter, particularly if you haven't used generics.

Software Foundations is written as a Rocq file per chapter, with places for you to fill in your answers. You should do the exercises in the sys-verif-fa25-proofs repo by filling out the missing definitions and proofs in the three chapter files in `src/software_foundations/`, `Basics.v`, `Induction.v`, and `Logic.v`. You should also read the chapters, either online or within VS Code (the HTML version is a nice rendering of the Rocq sources).

Most of these chapters is assigned (including the exercises marked "optional" in the text), but there are a few optional parts:

- Basics:
  - You can skip the "Fixpoints and Structural Recursion" section.
  - We aren't using the autograder described in "Testing your solutions". Just run `make` (in the VS Code terminal if you're using the Docker container).
- Induction:
  - You can skip the last section, "Bin to Nat and Back to Bin" (but do the previous one, "Nat to Bin and Back to Nat").
- Logic:
  - You should read "Working with Decidable Properties" but don't need to do the proofs. We'll use an approach slightly different from what the chapter explains, and you won't need to do any related proofs.
  - You can skip the last section, "The Logic of Rocq" (though that material is interesting if you care about theoretical issues)
- Poly:
  - This is only assigned as optional reading, but don't let that stop you from doing the exercises.
  - The last section on Church Numerals is a theoretical topic that isn't relevant to this class.

::: important

These chapters have a lot of small, easy exercises to get you practice. If you find anything difficult, come to office hours sooner rather than later to get it sorted out. If they're easy, note that proofs will become more difficult quickly after this.

:::

## Part 2: verifying functional programs

Finish the exercises in `src/sys_verif/assignments/hw1/rocq_exercises.v`. You can view a rendering of [Assignment 1 part 2](./rocq_exercises.md) as a reference.
