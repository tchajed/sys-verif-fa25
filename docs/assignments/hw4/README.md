---
category: assignment
icon: circle-exclamation
shortTitle: "Assignment 4"
dir:
  icon: file-lines
  order: 5
---

# Assignment 4: concurrent sharded hash map

In this assignment, you'll finish the proof of a concurrent, sharded hash map. Substantial proof is already provided, which means you'll spend more time reading code than writing it.

You should start by reading and understanding the [code](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/sharded_hashmap/sharded_hashmap.go). While reading it, spend some time figure out why you think it works and how you would explain its correctness without any of the tools in this proof - the first exercise in the Rocq file is to write down this explanation.

Then start working on the assignment at `src/sys_verif/assignments/hw4/sharded_hashmap.v` in the proofs repo. You can also view a rendered version of the assignment at [sharded_hashmap](./sharded_hashmap.md).
