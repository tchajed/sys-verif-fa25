---
order: 2
shortTitle: "Assignment 1"
icon: file-lines
---

# Assignment 1: Coq

This assignment has two purposes:

1. Learn how to use Coq to prove theorems. This is a skill you'll build on and use to verify programs in the rest of the class, so it's important you put enough practice in now.
2. Practice with functional programs. This is a warm up to imperative and concurrent programs as well as useful on its own, since functional programs are often used in the _specification_ of imperative programs.

## Submitting

See [submitting assignments](./setup#submitting-assignments) on the assignment setup page.

**The assignment is due Tuesday, Oct 1st at 11pm.** However, you are welcome and encouraged to submit early with partial progress to keep me informed of how the class is doing. If you have questions, just mention them briefly in the Canvas submission so I know to look.

I would recommend aiming to finish parts 0 and 1 by Tuesday, Sep 17th to be on track.

## Part 0: setup

The [assignment setup page](./setup) has instructions on getting the sys-verif-fa24-proofs repo and installing Coq. Follow those first.

::: warning
You might run into unexpected difficulties with installing the software, so do it early and ask for help quickly if you get stuck. It isn't a goal of the class to teach you to install software, but it is necessary to make progress on anything else.
:::

## Part 1: Software Foundations exercises

We'll use the free online textbook Software Foundations to learn the basics of using Coq to prove theorems. You'll read the three early chapters ([Basics](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html), [Induction](https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html), and [Logic](https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html)) and do (a selection of) the exercises in Coq. I also strongly encourage you to look at the [Polymorphism](https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html) chapter, particularly if you haven't used generics.

Software Foundations is written as a Coq file per chapter, with places for you to fill in your answers. You should do the exercises in the sys-verif-fa24-proofs repo by filling out the missing definitions and proofs in the three chapter files in `src/software_foundations/`, `Basics.v`, `Induction.v`, and `Logic.v`. You should also read the chapters, either online or within VS Code (the HTML version is a nice rendering of the Coq sources).

Most of these chapters is assigned, but there are a few optional parts:

- Basics:
  - You can skip the "Fixpoints and Structural Recursion" section.
  - We aren't using the autograder described in "Testing your solutions". Just run `make` (in the VS Code terminal if you're using the Docker container).
- Induction:
  - You can skip the last section, "Bin to Nat and Back to Bin" (but do the previous one, "Nat to Bin and Back to Nat").
- Logic:
  - You should read "Working with Decidable Properties" but don't need to do the
    proofs. We'll use an approach slightly different from what the chapter
    explains, and you won't need to do any related proofs.
  - You can skip the last section, "The Logic of Coq". I omit this because it's not terribly relevant to this class but I personally think this part is fascinating.
- Poly:
  - This is only assigned as optional reading, but don't let that stop you from doing the exercises.
  - The last section on Church Numerals is a theoretical topic that isn't relevant to this class.

::: important
These chapters have a lot of small, easy exercises to get you practice. If you find anything difficult, come to office hours sooner rather than later to get it sorted out. If they're easy, note that proofs will become more difficult quickly after this.
:::

## Part 2: verifying functional programs

Finish the exercises in `src/sys_verif/coq/assignment1_part2.v`. You can view a
rendering of [Assignment 1 part 2](./assignment1_part2.md) as a reference.
