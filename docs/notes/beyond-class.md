---
order: 28
shortTitle: "Beyond this class"
---

# Systems verification beyond this class

Here are a few pointers to verification research.

## Distributed systems

[IronFleet](https://www.andrew.cmu.edu/user/bparno/papers/ironfleet.pdf) is a good starting point to learn about verifying distributed systems.

[Grove](https://pdos.csail.mit.edu/papers/grove:sosp23.pdf) extends Perennial with distributed systems reasoning. Add support for reasoning about multiple machines, a network, and reasoning about failures of individual machines.

There's lots of work on reasoning about protocols independently of implementing those protocols. The [Ivy](https://dl.acm.org/doi/pdf/10.1145/2908080.2908118) paper is a useful starting point. Most of the followup work has been about automating finding inductive invariants to prove safety of a protocol.

## New specifications

Iris is well suited to extensions to handle new language features and specifications. For example:

- Verifying [randomized algorithms](https://iris-project.org/pdfs/2024-popl-clutch.pdf) where the probability of an outcome is part of the specification.
- Verifying [storage systems](https://pdos.csail.mit.edu/papers/perennial:sosp19.pdf) that want to reason about crashes at any time (for example due to power failure).
- One part of verifying a system is secure is proving confidentiality. Formalizing confidentiality often involves some form of [non-interference specification](https://iris-project.org/pdfs/2021-popl-tiniris-final.pdf).
- [Weak memory](https://people.mpi-sws.org/~dreyer/papers/compass/paper.pdf), a fundamental feature of concurrent programs on real hardware.
- [Persistent memory](https://iris-project.org/pdfs/2023-oopsla-spirea.pdf) is like memory but persists across reboots. These proofs need to combine techniques for crashes with techniques for weak memory.

Note that in each of these areas there is other work not using Iris that tackles the same underlying problem.

## Practical verification

The techniques in class require learning quite a bit before you can apply them to real code. One line of research is making verification easier to apply, including scaling up to real code, usable by engineers, and integrated with usual software development.

AWS used verification as a core part of their [process for the Cedar policy language](https://dl.acm.org/doi/pdf/10.1145/3663529.3663854).

AWS also uses [verification for their distributed protocols](https://assets.amazon.science/67/f9/92733d574c11ba1a11bd08bfb8ae/how-amazon-web-services-uses-formal-methods.pdf). In addition to TLA+ as described by that article, they also use [P](https://p-org.github.io/P/).

[Verus](https://www.andrew.cmu.edu/user/bparno/papers/verus-sys.pdf) is a new language for verification using Rust.
