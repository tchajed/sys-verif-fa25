---
# Auto-generated from literate source. DO NOT EDIT.
tags: literate
---

# Inputting special symbols

One early question when you start using Perennial (and Iris, which it is based on) is "how do you type all those funny symbols?".

The answer is that these are simply Unicode characters, and we have some IDE setup to input them by typing their typical LaTeX commands; when I type `\forall` it automatically turns into `∀` (in a Coq file).

For this class, the setup should be performed for VS Code via the `.vscode/settings.json` file in the assignment repo.

In general (for other IDEs, for example) you should look at the [Iris editor setup instructions](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md?ref_type=heads).

Once you have the setup, you'll need to use the right LaTeX commands. Here's a reference to the commonly used symbols, especially if you're less familiar with LaTeX. One to especially note: `\named` produces `∷`, which is used for _named hypotheses_ - this is a library we use in the class but it not part of Iris, nor is it a standard LaTeX command.

| input | symbol | meaning |
| --- | --- | --- |
| `\forall` | ∀ | forall quantifier |
| `\exists` | ∃ | exists quantifier |
| `\land` | ∧ | **l**ogical **and** |
| `\lor` | ∨ | **l**ogical **or** |
| `\sep` | ∗ | separating conjunction (note: not same as usual `*`) |
| `\mapsto` | ↦ | points-to for separation logic |
| `\named` | ∷ | used for named propositions |
| `\lc` and `\rc` | ⌜ and ⌝ | brackets for pure propositions |

Here are some notations that you don't have to use because they have ASCII equivalents, but you will see in existing code.

| input    | symbol | meaning            | ASCII              |
| -------- | ------ | ------------------ | ------------------ |
| `\leq`   | ≤      | less or equal      | `<=`               |
| `\to`    | →      | function type      | `->`               |
| `\gamma` | γ      | Greek letter gamma | use any other name |

Note that `∀` and `∃` are overloaded for use in Coq propositions and Iris propositions (`iProp`), and within Iris only the Unicode symbol is supported, so I recommend you stick with that. However, you can write `forall` and `exists` instead.

Similarly, `∧` can usually be written `/\` and `∨` can be written `\/`. You'll need `∨` within Iris, and I also find the ASCII versions of these two much more awkward to type.
