---
category: lecture
order: 1
---

# Lecture 1: What is verification?

::: important Main idea

Program verification consists of some _code_ we want to run, a _specification_ that says what the code should do, and a _proof_ that shows the code follows the specification.

:::

When you write a program, how do you know it does what you want? You've definitely seen testing: run the program and see what it does. Maybe you also write some test cases and re-run them when the code changes. But testing isn't enough to be confident in your code, which you might want if it was really important.

This class is about a more rigorous approach to program correctness. In program verification, we'll learn how to write a proof that a program does what it's intended to do. A major part of this class will be a focus on making mathematically precise "what the program is intended to do," what we call a _specification_. If we want to write a proof we have to know what we're proving. Second, we'll learn techniques to allow us to write _proofs_ that some program meets some useful specification. The class focuses on a few specific types of _programs_ for which we'll learn the relevant specification and proof techniques; we'll mostly focus on programs in Go, including pointers and concurrency.

The specifications in this class will generally be what's called "functional correctness", meaning the behavior or functionality of the program is as intended. There are weaker guarantees that are useful (because they're easier to prove), like memory safety (e.g., your program always accesses arrays in bounds, and has no double-free errors). There are specifications that go beyond functional correctness, such as security and performance properties, but these are even more difficult to prove. Orthogonally there are also aspects of the program that are hard to formalize (and thus outside the field of formal verification) but nonetheless important, like readability and maintainability.

The proofs in this class will be interesting compared to proofs you've done so far because we'll write them in a computer, and a program called an _interactive theorem prover_ will check the proofs (and help us write it in the first place). This might seem unrelated to program verification, and in a way it is - we could instead prove the correctness of programs the same way we prove theorems in math, on paper. However, program verification deserves the higher assurance of machine-checked proofs because the proofs will have many more details than a typical mathematical proof, and it's easy to overlook a case or premise that needs to be proven. Since the entire goal was to have reliable software, we don't want to shift "is my program correct?" to "is my proof correct?". Furthermore, doing the entire thing in a computer will allow a much tighter connection to the code we run, so we make sure to capture all the behaviors of the code we wrote rather than something abstract on paper.

This kind of proof isn't the only approach to verifying programs. A common alternative is to use _automated theorem proving_ with a solver like Z3. There are also specifications which we can prove with little to no proof. We won't talk much about these alternatives, focusing on techniques where you can see all the parts of the proof. Another advantage of using interactive theorem proving is that it scales naturally to advanced features like concurrency; it will take a little more effort, but it will be possible to reason about concurrency without drastically different techniques.

In summary, program verification involves taking some _code_ we want to run, writing a _specification_ that says what the code should do, and then writing a _proof_ that the code meets the specification. In this class, the code will be written in Go, the specifications will be about functional correctness, and the proofs will be machine-checked.

Verification is different from other software engineering approaches that also aim to make correct software in that it has a _soundness guarantee_: we can clearly articulate what the process guarantees, subject to some assumptions. Compare this with, for example, testing, which has been empirically shown to improve correctness but doesn't guarantee anything about lack of bugs or even fewer bugs. One of the things you'll learn in this class is how to articulate what the guarantees of verification are.

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
- Fiat Crypto and HACL\* were used to verify cryptography primitives used in the Chrome and Firefox browsers, respectively. This code is subtle, performance critical, has to run on many architectures, and bugs can cause security vulnerabilities. Chrome was particularly interested in verifying the browser crypto because fixing vulnerabilities requires an update that users might take weeks to install.
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

## Example: pointer aliasing

Quick: does the following function modify `*y`?

```go
func ModifyOne(x *int, y *int) int {
  *x = 1
  // what is *y?
}
```

The answer is that it depends! When reasoning about imperative programs with pointers, a key challenge is _pointer aliasing_: It's possible `x == y` (as pointers) and it does, or they might be distinct. If such a simple one-line function is complicated to think about, how can we handle thinking about larger programs?

The answer in this class will be to use _separation logic_, a powerful way to reason about such programs by capturing when pointers don't alias. If you're familiar with Rust, there's a deep connection with ownership in Rust. Separation logic is a more general way to think about ownership that will allow us to not only know our programs are safe, but also that they do the right thing.

## Example: concurrent read-optimized hash map

Verification really shines with concurrency, where it's hard to even think about correctness without some scaffolding.

In contrast, I think you could re-invent the proof of fast exponentiation's correctness. The strategy (in short, using a loop invariant) is something you could pull out of your math classes. The specific example would take some time, especially because it relies on some perhaps unfamiliar math facts, but you could do it.

Concurrency is much harder. Consider the following concurrent data structure, an example of something we can prove with the techniques of this class, where my proof is about 200 lines of Coq code.

```go
type HashMap struct {
  clean *atomicPtr
  mu    *sync.Mutex
}

func (h *HashMap) Load(key uint64) (uint64, bool) {
  clean := h.clean.load()
  value, ok := clean[key]
  return value, ok
}

// Clone the input map by copying all values.
func mapClone(m map[uint64]uint64) map[uint64]uint64 { ... }

func (h *HashMap) dirty() map[uint64]uint64 {
  clean := h.clean.load()
  return mapClone(clean)
}

func (h *HashMap) Store(key uint64, value uint64) {
  h.mu.Lock()
  dirty := h.dirty()
  dirty[key] = value
  h.clean.store(dirty)
  h.mu.Unlock()
}
```

Do you see what's going on? I certainly didn't the first time. Basically, the "clean" pointer has the current, logical, read-only value of the map, and it is returned by `h.dirty()`. The mutex `mu` is required to change its value, so that between reading the current value and storing no concurrent changes can happen.

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
