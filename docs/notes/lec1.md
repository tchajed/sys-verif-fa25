# Lecture 1: What is verification?

::: important Main idea
Program verification consists of some _code_ we want to run, a _specification_ that says what the code "should" do, and a _proof_ that shows the code follows the specification.
:::

In this class, code will be a Go program and proofs will be written by a human and checked by a machine. Verification encompasses other approaches, though.

Verification is different from other software engineering approaches in having a _soundness guarantee_: we can clearly articulate what the process guarantees, subject to some assumptions.

In this class you'll learn to read and write specifications, carry out proofs, and articulate the resulting guarantees.

## Motivation: important software still has bugs

Software is critical to society: think of your phone or cloud services that you rely on every day. This software is large and complex, built in a tall stack of layers. Yet even some of the most critical software, used by many applications and near the bottom of the stack, still has bugs.

How do we make reliable software? Spectrum of approaches (ranging from "less formal" to "more formal"):

- Deployment: beta testing, bug reporting
- Social: code review
- Methodological: version control, style checking, testing
- Technological: static analysis, fuzzing, property-based testing
- Mathematical: type systems, formal verification

Not a tradeoff: should use the whole spectrum. First, less formal techniques are less expensive. Second, even formal techniques have holes:

- Is your specification what you wanted? Ultimately there is always a gap in translating the requirements and goal in your head to something precise.
- Do your assumptions hold in practice? The proof makes assumptions, at least about the unverified software and hardware you depend on, if not the inputs and the way the software is used.

Big distinction between techniques that have a specification give some guarantee and those that don't. Testing, static analysis, fuzzing, and property-based testing all include some property of interest that the code should satisfy (eg, doesn't crash, or produces the right answer on certain inputs).

Verification is distinguished in this list for giving a guarantee for all inputs and all executions. However, it requires both a written specification and proof.

## Why learn verification?

**New, exciting, active area of research.** Huge progress in the last decade:

- CompCert is a verified C compiler that was an early success of verification (ok, it's more than a decade old), using techniques closely related to what we'll use in this class. A study of C compilers found bugs in every compiler: CompCert had no wrong code generation bugs, and the bugs found were in the (at the time) unverified frontend.
- seL4 is a verified microkernel used in critical applications like helicopter software and other defense applications.
- Fiat Crypto and HACL* were used to verify cryptography primitives used in the Chrome and Firefox browsers, respectively. This code is subtle, performance critical, has to run on many architectures, and bugs can cause security vulnerabilities. Chrome was particularly interested in verifying the browser crypto because fixing vulnerabilities requires an update that users might take weeks to install.
- Amazon Web Services (AWS) uses formal methods to reason about the protocols that their services implement. They especially care about things like avoiding data loss in S3, their core storage service.
- Bedrock Systems is a company developing a verified hypervisor; one key customer is automative companies wanting to replace N different computers with a hypervisor they trust to isolate the components.

Other successes in academic work (not a particularly complete list): CakeML (verified ML compiler), Kami (verified RISC-V processor), Vellvm (formal semantics of LLVM IR), VST (verified C software), DaisyNFS (verified file system), Bedrock (verified packet processing), CertiKOS (verified operating system).

**Rigorous thinking tool.** Even if you don't use verification or do research in the area, verification is a way to learn how to think rigorously about software. Being forced to write and prove a precise specification will give you _thinking tools_ for other software you use and write, which might improve your code even if you don't go to verify it. This is especially useful for concurrency, where the formal reasoning can be _easier_ than trying to grapple with the code informally.

## What is verification not good for?

We'll focus in this class on understanding how to use verification, but before we dive into that I don't want you to forget that it isn't always the solution.

::: details Fun stories where verification wouldn't have mattered

Here are three stories, all coincidentally from game development, where verification would not have been the solution.

Changing the spec: Starcraft 1 was plagued by path-finding problems during development. The algorithm was okay, but in some cases just didn't work. One of those was harvesting units, which would repeatedly go between your base and some minerals like crystals or vespene gas. While the player was busy doing something else, the harvesters would jam up and be unable to continue harvesting, holding up all builds and being extremely frustrating. The solution implemented was to have harvesting units ignore collisions if they were on their way to get minerals or carrying back minerals; they just changed the spec to workaround a difficult implementation. ([source](https://www.codeofhonor.com/blog/the-starcraft-path-finding-hack))

Bugs are sometimes okay: The first release of The Elder Scrolls V: Skyrim was full of little bugs, like exploits for easy money or skill progression, or a bug where you could place a bucket on a shopkeeper's head and steal from them. First, it would be hard to specify what guarantee these bugs were violating, Second, it didn't matter for the actual goal of making money and being entertaining: the game sold well and these exploits were mostly viewed as funny. ([source](https://gamerant.com/skyrim-best-glitches/))

Bugs are sometimes not okay: The first release of Cyberpunk 2077 was also full of bugs. These were often performance bugs and crashes; we could write a specification that the game never crashed, but performance would be quite challenging. In this case the bugs were bad enough on Xbox One and PlayStation 4 that CD Project Red had to issue refunds ([source](https://www.polygon.com/2021/4/22/22398340/cd-projekt-red-april-2021-investors-call-refund-details-costs)). _However_, these bugs were basically fixed in "patch 2.0" and the game is highly regarded after this fix. The reason for these bugs was basically schedule pressure, and verification as it currently stands is unlikely to let you ship sooner, only with better guarantees that you won't have bugs later.

:::

Verification matters when you have a specification, and bugs are consequential.

## Example: fast exponentiation

An example to understand specifications: `FastExp` is some code we might want to verify. Its informal specification is captured by the comment: it returns b to the power n.

```go
// FastExp returns b to the power of n
func FastExp(b int, n int) int {
  a := 1
  c := b
  for n > 0 {
    if n%2 == 1 {
      a = a * c
      n = n / 2
    } else {
      n = n / 2
    }
    c = c * c
  }
  return a
}
```

To formalize the specification, we might say `FastExp` always returns the same value as an easy-to-understand function like `SlowExp`. Here we also make explicit the assumption that `0 <= n` in the form of a `panic`.

```go
// SlowExp return b to the power n
func SlowExp(b int, n int) int {
  if n < 0 {
    panic("negative exponent")
  }
  if n == 0 {
    return 1
  }
  return b * SlowExp(b, n-1)
}
```

The specification of `FastExp` can now be written as:
$$
  \forall b, n\ldotp 0 \leq n \to \texttt{FastExp}(b, n) = \texttt{SlowExp}(b, n).
$$
The equation looks pretty but it's still not totally precise! Why can we treat `FastExp` (and `SlowExp` for that matter) as a function? What if it doesn't terminate, or prints to the screen? What about a similar function that takes a pointer as an input? We'll solve these issues eventually.

If we can formalize the statement above, and _prove_ it, we gain a lot of confidence in `FastExp`'s correctness: it's as good as using `SlowExp`, with the advantage of being faster (due to a separate analysis; performance isn't part of the verification guarantees).

## Outline of this class

- **Coq foundations: functional programs**
  - Coq: mechanized theorem proving
  - Functional programming
  - Specifying and verifying functional programs
- **Separation logic: Go programs**
  - GooseLang: Modeling Go programs
  - Separation logic for heap reasoning
  - Verifying Go programs
  - Sequential data structure case studies
- **Concurrency**
  - Ghost state
  - Separation logic specs for concurrency primitives
  - Concurrent data structure case studies
