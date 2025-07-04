---
# Auto-generated from literate source. DO NOT EDIT.
category: assignment
tags: literate
order: 5
shortTitle: "Assignment 3: queue"
---

# Assignment 3: queue using two stacks

The code at [go/heap/queue.go](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/go/heap/queue.go) implements a queue using two stacks. Don't worry if you haven't seen this before (or don't remember it); part of the assignment is figuring out how the data structure works enough to verify it.

To simplify the code and the proof, the stack has been factored out into its own data structure. You can see its specifications and proofs in [src/sys_verif/program_proof/heap_proof/stack_proof.v](https://github.com/tchajed/sys-verif-fa25-proofs/blob/main/src/sys_verif/program_proof/heap_proof/stack_proof.v). That file has already been imported here, so you can refer to its definitions and specifications.

This part of the assignment intentionally provides you with almost nothing: you'll write a representation invariant, the specifications, and the proofs. **I suggest starting this part early**, since you will likely need to go back and forth between `queue_rep`, the specifications, the loop invariants, and the proofs; working on later parts of this sequence will cause you to discover bugs in earlier parts.

```coq
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_proof.stack_proof.
From Goose.sys_verif_code Require Import heap.

Section proof.
Context `{hG: !heapGS Σ}.

Definition queue_rep (v: val) (els: list w64): iProp Σ :=
  False.
Hint Rewrite @length_reverse : len.

Lemma wp_NewQueue : False.
Proof.
Admitted.

Lemma wp_Queue__Push : False.
Proof.
Admitted.

Lemma wp_Queue__emptyBack : False.
Proof.
Admitted.

Lemma wp_Queue__Pop : False.
Proof.
Admitted.

End proof.
```
