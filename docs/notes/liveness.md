---
category: lecture-note
order: 26
shortTitle: "Liveness"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Liveness

## Learning outcomes

1. Understand how fairness makes liveness complicated
2. Explain the meaning of an LTL liveness specification

---

$$
\gdef\always{\box}
\gdef\eventually{\Diamond}
% \lift reuses macro and notation from Iris
\gdef\action#1{\langle #1 \rangle}
\gdef\enabled{\mathrm{enabled}}
\gdef\WF{\mathit{WF}}
\gdef\leadsto{\rightsquigarrow}

%% semantics
\gdef\nat{\mathbb{N}}
\gdef\State{\operatorname{State}}

\gdef\init{\mathit{init}}
\gdef\next{\mathit{next}}
$$

<!-- @include: ./macros.snippet.md -->

## Motivation

We've only talked about _safety_ so far: we prove the program "doesn't go wrong" as long as it wrongs, but the postcondition only holds if the function terminates.

Real systems also care about _liveness_ properties: proving that programs terminate and systems _eventually_ produce results.

In fact systems also care about (quantitative) _performance_ properties: achieving certain throughput or latency targets. These have generally been out of scope for verification simply because the properties are too hard to formalize (performance is a complex interplay between many factors), but there is still some work in this area.

Liveness is an important topic when reasoning about distributed systems especially.

## Example: spinlock

Consider the following implementation of a spinlock-based mutex. Three points in the control flow are labeled, pc0, pc1, and pc2; each of the two spawned threads in `main` goes through these states.

```go
type Mutex = bool;
const UNLOCKED = false;
const LOCKED = true;

func (m *Mutex) Lock() {
  // pc0
  for CompareAndSwap(m, UNLOCKED, LOCKED) {}
}

func (m *Mutex) Unlock() {
  // pc1
  *m = UNLOCKED
  // pc2
}

func main() {
  var m Mutex
  go func() {
     m.Lock()
     m.Unlock()
  }()
  go func() {
     m.Lock()
     m.Unlock()
  }()
}
```

`CompareAndSwap(m, UNLOCKED, LOCKED)` atomically checks if `*m = UNLOCKED` and if it does, sets it to `LOCKED`. If `*m` is not UNLOCKED, the call does nothing. `CompareAndSwap` returns true if it successfully changed the value of `*m`, so that `Lock()` loops until it successfully acquires the lock.

The full state of this program can be modeled as a state machine. The state consists of a program counter for each thread (either pc0, pc1, or pc2) plus the value of the single mutex.

The state of each thread in `main` follows these transitions:

```mermaid
stateDiagram-v2
  direction LR
  [*] --> pc0
  state pc0_choice <<choice>>
  pc0 --> pc0_choice
  pc0_choice --> pc0: if m = LOCKED
  pc0_choice --> pc1: if m = UNLOCKED <br /> m ≜ LOCKED
  pc1 --> pc2: m ≜ UNLOCKED
  pc2 --> [*]
```

The key transition is that the `CompareAndSwap` loop advances from pc0 to pc1 only if the mutex is unlocked, and atomically sets the mutex value to locked.

Each thread independently goes through this loop.

**Exercise:** argue as rigorously as you can why the two threads must both terminate.

::: details Solution

First, we can observe that one of the two threads must win the race to acquire the mutex; they cannot both simultaneously fail.

However, why should the other thread acquire the mutex? A key issue this exercise brings up is _fairness_. The system's scheduler must run both threads "often enough" in order to guarantee that if the first thread acquires the mutex, it gets to run at some point and finish its critical section (represented by whatever happens in the pc1 state) so it can unlock the mutex. Otherwise it would be possible for the second thread to spin forever, waiting for a mutex that will never be released.

:::

## Linear Temporal Logic

To talk about liveness formally we will introduce Linear Temporal Logic (LTL). You've already seen separation logic, so this won't be your first time seeing a logic.

First, we will use LTL to describe traces of system behavior. The semantics (the meaning) of an LTL formula is a set of traces, where a trace is a sequence of states. We will these formulas to describe two things: (1) what is a legal trace that comes from running our system?, and (2) what traces meet our liveness specification? The first-order logic and separation logic we've seen so far has been all about describing a single state; LTL is all about sequences of states. It turns out to be simplest to always talk about infinite sequences of states; if a system terminates at some point we'll model its execution by repeating the terminating state infinitely once it's reached.

::: important Key idea

The key idea to remember about LTL is that a formula describes a set of traces (equivalently, a formula either holds or doesn't hold for a given trace), where a trace is an infinite sequence of states.

This tells you what form the semantics has, which is necessary to understand any particular LTL construct or formula.

:::

### Syntax

Let's start working through the syntax of LTL formulas, with brief intuition behind each construct.

$$
\begin{aligned}
P &\triangleq \lift{\phi} \mid \action{a} \\
&\quad \mid \always P \mid \eventually P \\
&\quad \mid \lnot P \mid P_1 \land P_2 \mid P_1 \lor P_2
\end{aligned}
$$

The first construct $\lift{\phi}$ is actually the boring one. It _lifts_ a propositional formula $\phi$ about a single state into temporal logic about a trace; what it asserts is just that the first state in the trace satisfies $\phi$. You can think about what $\phi$ is in one of two ways: its a formula describing one state with a bunch of variables over finite domains (like booleans or the program counter `pc0 | pc1 | pc2` in the example above), or you can just imagine $\phi : \State \to \Prop$ in Coq and it describe a single state (though $\phi$ is not technically propositional in that it could use quantifiers; this distinction isn't important to understand LTL). We can take any such formula $\phi$ for a single state and turn it into an LTL formula with $\lift{\phi}$ (this is intentionally the same notation we used to lift pure propositions into separation logic).

Next we have an _action_ $\langle a \rangle$ where $a : (\State \times \State) \to \Prop$ (a relation between two states). This construct is used to describe _transition systems_ within LTL; we will see that it allows us to easily say that a trace corresponds to the behavior of a state machine, where $a$ is the relation describing the state machine's transitions. In temporal logic $\action{a}$ says that the $a$ holds between the first and second states of the trace.

The second row has the key novelty of LTL: the temporal operators. $\always P$ (pronounced "always $P$") says that $P$ holds _from now onward_ or _henceforth_. $\eventually P$ (pronounced "eventually $P$") says that $P$ holds _eventually_; that is, starting at some point in the future from the current moment.

The third row has the usual connectives of a logic, negation, $P \land Q$ (logical and), and $P \lor Q$. There's nothing exceptional about these in LTL. We can write $P \Rightarrow Q$ for implication, and it's the same as $\lnot P \lor Q$ as in regular propositional logic.

### Semantics

Now let's formally give the semantics of an LTL formula. In this logic I think it helps to directly look at the semantics to get an intuition; it's simple enough to do so.

We'll take every $P$ in the grammar above and describe it as a $\mathrm{trace} \to \Prop$, where $\mathrm{trace} \triangleq \nat \to \State$. A concrete trace can be written as a sequence, like $t = t_0, t_1, \dots$, but note that it is important that this be an infinite sequence. A trace is a function so in this example we can say $t(0) = t_0$ and $t(1) = t_1$.

Define a shift operator on traces that removes the first $k$ elements $t[k..]$. Formally we can define it to be $t[k..] = \lambda n.\, t(n+k)$. Notice $t[0..] = t$. (The notation is intentionally meant to evoke Go's `t[k..]` sub-slicing, but note that $t[k..]$ is defined and makes sense even for infinite traces.)

Now we can give the semantics of each temporal operator. The first four definitions are interesting:

$\lift{\phi}(t) = \phi(t(0))$

$\langle a \rangle(t) = a(t(0), t(1))$

$(\always P)(t) = \forall k.\, P(t[k..])$

$(\eventually P)(t) = \exists k.\, P(t[k..])$

The other connectives are boring (they don't talk about time in any interesting way):

$(\lnot P)(t) = \lnot (P(t))$

$(P \land Q)(t) = P(t) \land Q(t)$

$(P \lor Q)(t) = P(t) \lor Q(t)$

### Examples

$\lift{\phi}$ we can think of as reflecting the following picture:

$$\phi, t_1, t_2, ...$$

where we mean "a state satisfying $\phi$", then arbitrary states $t_1$, $t_2$ and so on. $\lift{\phi}$ only cares about the first state in a trace.

$\always \lift{\phi}$ has this picture:

$$\phi, \phi, \phi, ...$$

Every state must satisfy $\phi$ (although the concrete states could all be different).

$\eventually \lift{\phi}$:

$$\lnot \phi, \lnot \phi, \phi, \lnot \phi, \phi, ...$$

Notice that $\phi$ must show up in this list, but after that anything can happen (we could go back and forth, or $\lnot \phi$ could hold from then on).

Now consider what happens when start combining the modalities:

The picture for $\eventually \always \lift{\phi}$ is this:

$$\lnot \phi, \lnot \phi, \phi, \lnot \phi, \phi, \phi, \phi, ...$$

The definition says that there is a time somewhere in the future (this is the $\eventually$) where from that point forward (this is the $\always$), $\phi$ holds. The example shows that at logical time 2 $\phi$ becomes true, but that's not the point where it holds _from then on_: that only happens at time 4. This trace still satisfies the temporal formula.

**Exercise:** what's the intuition and picture for $\eventually \always P$?

::: details Solution

The picture for $\always \eventually \lift{\phi}$ is this:

$$(\lnot \phi, \phi), (\lnot \phi, \lnot \phi, \phi), (\phi), ...$$

I've grouped these into runs where $\eventually \lift{\phi}$ holds in each segment (the grouping is just to help you see the pattern).

This one is more complicated. Expanding the definitions, the formula says that at every time step (this is $\always$), there is a later time (this is $\eventually$) where $\phi$ holds.

:::

**Exercise:** what does $\always \always P$ mean? What does $\eventually \eventually P$ mean? Try to reason from the definitions as well as intuitively.

Negation: $\lnot \always P \iff \eventually (\lnot P)$ and $\lnot \eventually Q \iff \always (\lnot Q)$.

**Exercise:** simplify $\lnot \eventually \always P$.

::: details Solution

Push the negation inward to get $\always \eventually \lnot P$.

Notice that $\always$ flips to $\eventually$ under negation, and the composite modality $\eventually \always$ flips to $\always \eventually$. The same holds in reverse in both cases! We say that $\always$ and $\eventually$ are _dual_ and similarly that $\eventually \always$ and $\always \eventually$ are dual.

:::

Fun fact: $\eventually \always \eventually \always P \iff \eventually \always P$.

## State machine definition

We can describe the spinlock example in temporal logic as follows:

The state consists of locked (a boolean) and two program counters: t1 for thread 1 and t2 for thread2. The program counters will be inductive datatypes with three values, pc0, pc1, and pc2, corresponding to the labeled points in the code. The threads will start in pc0 and terminate in pc2, to keep the state machine as small as possible.

There are three possible transitions for thread 1:

- $cas\_fail_1(s, s') \triangleq s.t1 = pc_0 \land s.locked = \true \land s' = s$
- $cas\_succ_1(s, s') \triangleq s.t1 = pc_0 \land s.locked = \false \land s'.t1 = pc_1 \land s'.locked = \true \land s'.t2 = s.t2$
- $unlock_1(s, s') \triangleq s.t1 = pc_1 \land \land s'.t1 = pc_2 \land s'.locked = s.locked \land s'.t2 = s.t2$

These correspond to the CompareAndSwap failing, CompareAndSwap succeeding, and the call to Unlock.

The transitions for thread 2 are the same but with the roles of the threads reversed. It can be easier to read these if we introduce notation for changing just one field of the state: $s.(t2 := pc_2)$ is the state $s$ but with the field $t2$ changed to the value $pc_2$.

- $cas\_fail_2(s, s') \triangleq s.t2 = pc_0 \land s.locked = \true \land s' = s$
- $cas\_succ_2(s, s') \triangleq s.t2 = pc_0 \land s.locked = \false \land s' = s.(t2 := pc_1).(locked := \true)$
- $unlock_2(s, s') \triangleq s.t2 = pc_1 \land \land s'.t2 = pc_2 \land s' = s.(t2 := pc_2$

It helps to read these as consisting of a "guard" over the initial state that says when the transition can happen together with an "update" that says how $s'$ is derived from $s$.

The entire behavior of the spinlock can now be written in temporal logic. First, the transition relation of the whole system is just to take an arbitrary possible transition from either thread:

- $\next_1 \triangleq \langle cas\_fail_1 \rangle \lor \langle cas\_succ_1 \rangle \lor \langle unlock_1 \rangle$
- $\next_2 \triangleq \langle cas\_fail_2 \rangle \lor \langle cas\_succ_2 \rangle \lor \langle unlock_2 \rangle$
- $\next \triangleq N_1 \lor N_2$

The initial state is this one:

$$\init(s) \triangleq s.t1 = pc_0 \land s.t2 = pc_0 \land s.locked = \false$$

Putting it together, a valid execution of the spinlock is one satisfying:

$$\lift{\init} \land \always \next$$

Think about what $\always \next$ means.

::: info Stutter steps

For technical reasons, it's necessary to actually include _stutter steps_ where the state machine does nothing as part of the $\next$ predicate:

$\mathit{stutter}(s, s') \triangleq s' = s$

$\next \triangleq N_1 \lor N_2 \lor \langle \mathit{stutter} \rangle$

If we didn't do this, consider what happens once the program terminated and $N_1$ and $N_2$ were both impossible. Then $\next(s, s')$ would be always false, and there would be _no_ infinite traces such that $\always \next$ holds! Stutter steps solve this problem by allowing repeating the final state forever.

:::

## Fairness

For an action $a$, define a state predicate $\enabled(a) \triangleq \fun{s} \exists s'.\, a(s, s')$. Intuitively, $\enabled(a)$ holds in a state $a$ if the action can run in that state. We'll commit a minor abuse of notation and use $\enabled(a)$ as a temporal formula, rather than the technically correct $\lift{\enabled(a)}$ which is cumbersome to read.

For example, when is $cas\_succ_2$ enabled? That is, what is a simplified expression for $\enabled(cas\_succ_2)$? Looking at the definition, it's possible for this transition to run in $s$ if $s.t2 = pc_0 \land s.locked = \false$ (this is the guard of this transition).

Define a notion called _weak fairness_ (of an action $a$): $\WF(a) \triangleq \always (\always \enabled(a) \Rightarrow \eventually \action{a})$.

Weak fairness is equivalent to the following: $\always \eventually (\lnot \enabled(a) \lor \action{a})$.

We will generally assume that a transition of the state machine runs fairly. In the spinlock example, we might assume $\WF(\next_1) \land \WF(\next_2)$; that is, the scheduler runs each thread, as long as it stays ready to run.

**TODO:** examples and exercises

## Specifying liveness properties

Recall we described system behavior for the spinlock example: we choose some $\State$ for our state machine, wrote a transition relation $\next = a_1 \lor a_2 \lor ...$ (one action for each transition) and a predicate $\init$ to describe initial states. Then a valid trace of executing this transition system is $\lift{\init} \land \always \langle \next \rangle$.

Need _fair_ traces for liveness to be achievable. Use assumptions of the form $\WF(a_i)$ or $\WF(a_i \lor a_j)$ (they're not the same!).

Generally want to say $P \leadsto Q \triangleq \always (P \Rightarrow \eventually Q)$.

Putting it together: $\lift{\init} \land \always \langle N \rangle \land \WF(a_1) \land \WF(a_2) \entails P \leadsto Q$.

## Further reading

See [The Temporal Logic of Actions](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf) by Leslie Lamport.
