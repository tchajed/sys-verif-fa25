# Lecture 1: What is verification?

::: important Main idea
Program verification consists of some _code_ we want to run, a _specification_
that says what the code "should" do, and a _proof_ that shows the code follows
the specification.
:::

In this class, code will be a Go program and proofs will be written by a human
and checked by a machine. Verification encompasses other approaches, though.

Verification is different from other software engineering approaches in having a
_soundness guarantee_: we can clearly articulate what the process guarantees,
subject to some assumptions.

In this class you'll learn to read and write specifications, carry out proofs, and
articulate the resulting guarantees.

## Motivation: important software still has bugs

Software is critical to society: think of your phone or cloud services that you
rely on every day. This software is large and complex, built in a tall stack of
layers. Yet even some of the most critical software, used by many applications
and near the bottom of the stack, still has bugs.

How do we make reliable software? Spectrum of approaches:

- Deployment: beta testing, bug reporting
- Social: code review
- Methodological: testing, version control, style checking
- Technological: static analysis, fuzzing, random testing
- Mathematical: type systems, formal verification

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
