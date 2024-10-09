---
# Auto-generated from literate source. DO NOT EDIT.
category: lecture
tags: literate
order: 12
shortTitle: "Lecture 12: Ownership in Go"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 11: Goose - Ownership reasoning

> Follow these notes in Coq at [src/sys_verif/program_proof/ownership.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/ownership.v).

## Learning outcomes

1. Understand the assertions for structs in Goose.
2. State the right ownership over a slice for a function.
3. Use and understand fractional permissions in specifications.

Theme for today: ownership in Go and in GooseLang

---

## Structs

How to model structs, then how to reason about them. Need for some "types".

Difference between _shallow_ and _deep_ embedding.

## Slices and map

Modeling length, capacity, and contiguous allocations. Ownership in slices, slice append.

Maps as non-atomic values.

## Fractional permissions

"Fictional separation" models read-only access.
