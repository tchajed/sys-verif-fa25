---
order: 1
icon: book-open
shortTitle: "Software Foundations"
---

# Software Foundations exercises

We'll use the free online textbook Software Foundations to learn the basics of using the Rocq prover to prove theorems. You'll read the three early chapters ([Basics](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html), [Induction](https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html), and [Logic](https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html)) and do (a selection of) the exercises in Rocq. I also strongly encourage you to look at the [Polymorphism](https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html) chapter, particularly if you haven't used generics.

Software Foundations is written as a Rocq file per chapter, with places for you to fill in your answers. You should do the exercises in the sys-verif-fa25-proofs repo by filling out the missing definitions and proofs in the three chapter files in `src/software_foundations/`, `Basics.v`, `Induction.v`, and `Logic.v`. You should also read the chapters, either online or within VS Code (the HTML version is a nice rendering of the Rocq sources).

Most of these chapters is assigned (including the exercises marked "optional" in the text), but there are a few optional parts:

- Basics:
  - Skip "testing your solutions" - we aren't using the autograder described there. Just run `make` (in the VS Code terminal if you're using the Docker container).
- Induction:
  - You should do the entire chapter.
- Logic:
  - You should read "Working with Decidable Properties" but don't need to do the proofs. We'll use an approach slightly different from what the chapter explains, and you won't need to do any related proofs.
  - You can skip the last section, "The Logic of Rocq" (though that material is interesting if you care about theoretical issues)
- Poly:
  - This is only assigned as optional reading, but don't let that stop you from doing the exercises.
