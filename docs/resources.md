---
shortTitle: "Resources"
icon: "book"
---

# Additional resources

A core resource is the course [lecture notes](./notes/), which include some
explanations and references not tied to any specific lecture.

## Coq

If you want more practice I encourage you to read [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html) beyond the assigned chapters, and even to do additional exercises.

The [Coq reference manual](https://coq.inria.fr/doc/master/refman/index.html) can be helpful, if you know what you're looking for. You should specifically use the [tactic reference](https://coq.inria.fr/doc/master/refman/coq-tacindex.html) if you're using a built-in Coq tactic.

The textbook [Certified Programming with Dependent Types (CPDT)](http://adam.chlipala.net/cpdt/cpdt.pdf) is excellent for many advanced topics.

## Go

We will be working with Go code in this class. It will help to have at least
reading familiarity with Go, which you can get by following [A Tour of
Go](https://go.dev/tour/welcome/1) (you only really need the Basics and Methods
chapters).

To verify code, it must also be in the subset of Go supported by
[Goose](https://github.com/goose-lang/goose). You'll mostly be verifying
provided code so won't need to understand these restrictions, but if your
project involves writing new code I'll work with you to help you write it in the
Goose-supported subset.

## Iris

Use the [IPM
documentation](https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md)
as a reference for the tactics.

The lecture notes for [Semantics of Type Systems](https://plv.mpi-sws.org/semantics-course/lecturenotes.pdf) at MPI explains Iris "on paper". However, some background in programming language theory is needed to skip to the part on Iris and understand it.

The [Iris lecture notes](https://iris-project.org/tutorial-material.html) from Aarhus University explain Iris "on paper", in a self-contained manner. However, there is no connection to Coq and some knowledge of logic is expected to understand the material.

[Iris from the ground
up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf) is an
excellent reference if you want to understand how Iris works internally (though
way too much if you just want to use it).

## Papers

These papers are directly relevant to the class:

- [Separation Logic (CACM 2019)](https://dl.acm.org/doi/pdf/10.1145/3211968)
- [A beginner's guide to Iris, Coq and separation logic (Indiana University
  Bachelor's Thesis, 2021)](https://arxiv.org/pdf/2105.12077)
- [Interactive Proofs in Higher-Order Concurrent Separation Logic](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf)

These are interesting papers for verification more broadly:

- [Formal verification of a realistic compiler (CACM 2009)](https://dl.acm.org/doi/pdf/10.1145/1538788.1538814)
- [How Amazon Web Services Uses Formal Methods (CACM 2015)](https://assets.amazon.science/67/f9/92733d574c11ba1a11bd08bfb8ae/how-amazon-web-services-uses-formal-methods.pdf)
- [BP: Formal Proofs, the Fine Print and Side Effects (IEEE SecDev 2018)](https://6826.csail.mit.edu/2020/papers/secdev2018.pdf)
