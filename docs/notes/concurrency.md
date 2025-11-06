---
category: lecture-note
order: 16
shortTitle: "Concurrency intro"
pageInfo: ["Date", "Category", "Tag", "Word"]
date: 2025-11-06 08:00:00 -5
---

# Concurrency introduction

We will now introduce concurrency to our programs and GooseLang model of programs, and shortly we'll start proving properties of concurrent programs.

<!-- @include: ../notes/macros.snippet.md -->

## Learning outcomes

At the end of this lecture, you should be able to

1. Formalize what a concurrent program does.
2. Understand why reasoning about concurrency is challenging.

## Motivation

Modern CPUs have many cores. Concurrency is important to get good performance from the machine. Systems software often needs to be concurrent so that applications can get good performance.

Concurrency is challenging due to the number of interleavings of a concurrent program: a small amount of code can now execute in many ways. How do we make sure every interleaving works correctly? Testing every interleaving isn't feasible, which makes verification more attractive in this setting.

In this lecture, we won't focus on proof techniques, but instead on describing _what concurrency is_ and motivating _why reasoning is challenging_.

## Programming with concurrency

When we program a computer, we can access concurrency in a number of ways:

- Linux has a notion of a process and the operating system runs processes concurrently. Processes have their own memory (implemented using virtual memory), but can interact via the file system, network, and shared memory.
- A process can have multiple threads that share the same memory, but have distinct stacks.
- A Go program has multiple "goroutines" that share memory and are managed by the Go runtime.
- A browser page can spawn Web Workers that run in the background and communicate with the page via messages.
- A hypervisor can run multiple virtual machines simultaneously. In the extreme case, these machines would be completely isolated and have no shared state.

In each of these examples, there are multiple units of execution. Exactly how these units are spawned and what state is shared is slightly different in each example, but once there are multiple threads there are similar issues when those threads interact with shared state.

The terminology around concurrency (and the related concept of parallelism) is a bit fraught with confusions due to differences in what the words mean in different contexts, so let's establish a little terminology to be clear what we're talking about.

We will use _thread_ generically for an independent unit of execution. Multiple threads can be running at any given time. It's not necessary to have _parallelism_, which is sometimes used to mean threads that run truly simultaneously, on different CPU cores. A fairly common situation is to have slightly more threads than physical cores, and some runtime system multiplexing those threads onto the physical cores, but we can also have a one-to-one mapping, or systems where thousands of threads can run on a handful of cores.

When we consider threads to run "simultaneously" it's sufficient to instead consider each thread as having atomic actions (for the sake of intuition you can imagine these are individual CPU instructions) which interleave in some single global order. When two actions happen truly simultaneously (say, because they happen on separate cores), this will produce two interleavings, one for each order. If the actions would conflict then they aren't truly atomic, and should be split into smaller and logically atomic steps.

### goroutines

In Go, there is an easy way to run something concurrently: the `go` statement. (See the [tour](https://go.dev/tour/concurrency/1) for more details.)

```go
go f()
```

The syntax is `go f()` - the argument to `go` must be a function call.

The effect is to run `f()` in another "goroutine" - a separate thread of execution (the program starts out with one goroutine). The spawned goroutine gets its own stack but otherwise all goroutines share access to the same variables.

```go
go func() {
  fmt.Println("hello 1")
}()
fmt.Println("hello 2")
```

Could print "hello 1" then "hello 2" or the reverse. In reality, if this is in `main` then the background goroutine might not get to finish and we could easily see "hello 2".

**Exercise**: what else do you think could happen?

::: details Solution

What about this?

```txt title=" "
hehello 1
llo 2
```

The possibly executions depends on what the system guarantees to be _atomic_. In this case, ultimately printing is a `write(2)` system call to the stdout file of the process, and these writes are turned into output on the terminal device - it is expected that the system calls are atomic, and also expected that Go will issue one for each `fmt.Println` (unless it is too large).

:::

## Modeling concurrent programs

We will add a new language construct $\spawn \, e$ which creates a new thread running $e$ and which evaluates to $()$ (the "unit value" or empty tuple).

Remember the semantics of heap programs $(e, h) \leadsto (e', h')$.

At any given time, we're no longer running _one expression_ $e$ but a whole list, which we'll call a _thread pool_ $T$ - it will simply be a list of expressions in our model. The semantics will now have the form $(T, h) \leadsto_{tp} (T', h')$. Notice that we have a single global heap and the only state within one thread is the expression itself - there's no additional thread metadata or thread-local storage, and everything in the heap is in principle accessible to any thread.

The threadpool semantics is closely related to the semantics of individual expressions. In fact for the most part the transitions of a threadpool are to pick some thread, execute it for a bit, and then possibly switch to another thread:

$$
\dfrac{(e, h) \leadsto (e', h')}
{(T_1 \listapp [e] \listapp T_2, h) \leadsto_{tp} (T_1 \listapp [e'] \listapp T_2, h')}
$$

The rule looks more complicated than it is. If a threadpool is running some thread in the middle being $e$, it has the shape $T_1 \listapp [e] \listapp T_2$. The transition taken only changes the one expression $e$ to $e'$, and the heap goes from $h$ to $h'$. This transition models the thread $e$ being chosen to run next, and the semantics only ever runs one thread at a time.

We haven't said what the new $\spawn \, e$ primitive does, but it will be the one construct that expands the threadpool:

$$(T_1 \listapp [K[\spawn \, e]] \listapp T_2, h) \leadsto_{tp} (T_1 \listapp [K[()]] \listapp T_2 \listapp [e], h)$$

This time the heap is uninvolved, and the only effect is to create a new thread. Recall that $K[\spawn \, e]$ refers to an evaluation context $K$ surrounding $\spawn \, e$, meaning the spawn is the next thing to run. Concretely the simplest such evaluation context would be if the expression to be evaluated was $\spawn \, e;\, e_2$, in which case the program would continue as $(); e_2$, which will quickly evaluate to $e_2$. The semantics of spawn say to launch a new thread, then continue running the rest of the program with $\spawn \, e$ having returned $()$.

::: important Exercise: add thread id to semantics

To check your understanding of this rule, modify it so that $\spawn \, e$ returns a "thread id" instead of nothing interesting. A natural choice of which thread id to return is the index of the thread in the threadpool.

:::

Recall that we defined the soundness of separation logic in terms of whether an expression got stuck: if $(e, h)$ cannot step to anything and $e$ is not a value, then we called it stuck. Soundness was partly about expressions not getting stuck (and partly about the postcondition being true if they did terminate in a value). We have to decide what to do with those definitions now that there are multiple threads.

The decision we'll take is that the _concurrent separation logic_ we develop will show that after an expression has run for a while, _none of the spawned threads are stuck_, and the postcondition will need to hold on the final value of the "main thread", the first element of the threadpool - background threads can go be in infinite loops or terminate in any value when the main thread terminates.

::: info Exercise

Is this the right model? Think about whether it is a good idea in the context of a few different runtime environments (e.g., a single Go program vs processes in Linux).

:::

## Synchronizing programs

Since threads interleave with each other, to write correct programs we will need programming mechanisms to control interleavings. First, let's see one example of a bug due to interleavings. Then, we'll see two core synchronization primitives: mutexes provide mutual exclusion (e.g., to make more than one assembly instruction run atomically) and barriers provide waiting (e.g., to efficiently implementing waiting for several threads to finish).

### Bugs: race condition

Imagine we have the following code:

```go
var counter uint64 // global
// ...
go func() {
  counter = counter + 1
}()
go func() {
  counter = counter + 1
}()
```

Imagine `counter = counter + 1` compiles to the following assembly, where 0x80a1c is the address of the global counter variable:

```asm
mov 0x80a1c, %eax
add $0x1, %eax
mov %eax, 0x80a1c
```

What happens when we run this program?

Here's one interleaving:

```asm
# counter = 10
mov 0x80a1c, %eax
add $0x1, %eax
mov %eax, 0x80a1c
                         mov %eax, 0x80a1c
                         mov 0x80a1c, %eax
                         add $0x1, %eax
# counter = 12
```

```asm
# counter = 10
mov 0x80a1c, %eax
                         mov 0x80a1c, %eax
                         add $0x1, %eax
add $0x1, %eax
                         mov %eax, 0x80a1c
mov %eax, 0x80a1c
# counter = 11 (bug!)
```

What went wrong? The two accesses to `counter` in the Go program form a race condition: two simultaneous operations on the same memory, where at least one is a write.

We can more simply think of the problem as being that `counter = counter + 1` didn't run atomically, as desired, and the effect is to cause two simultaneous writes to have the effect of only one.

Here's a puzzle for you.

Consider a similar example, but incrementing in a loop:

```go
var counter = 0
go func() {
  for i := 0; i < 10; i++ {
    counter = counter + 1
  }
}()
go func() {
  for i := 0; i < 10; i++ {
    counter = counter + 1
  }
}()
```

As before, `counter = counter + 1` runs as three separate steps (load, add, store).

What is the maximum value of the counter after both loops terminate? (Answer: 20). **What is the minimum value?** This is harder than it might look, so think about it before expanding the solution.

::: details Solution

The answer is 2.

Before getting to the explanation it helps to make one observation. We can safely think of the loop body as being two steps rather than three: $\lete{x}{\load{ctr}} \store{ctr}{x + 1}$. This is because the other thread can't affect anything between the local increment and the final store; that operation only touches local state.

It's relatively easy to show that there's an interleaving that leaves the counter at 10. We already saw how one iteration of `counter = counter + 1` could interleave with another iteration to produce an overall increment of 1; this could happen 10 times. But this execution has the two threads synchronizing after every iteration; perhaps we could do better by overlapping one iteration of one thread with _multiple_ of the other.

Here's the trace that produces 2:

| thread 1           | thread 2           |
| :----------------- | :----------------- |
| x := !ctr (0)      | x := !ctr (0)      |
|                    | ... (9 iterations) |
| ctr ← x + 1 (1)    |                    |
|                    | x := !ctr (1)      |
| ... (9 iterations) |                    |
| ctr ← x + 1 (?)    |                    |
| (done)             |                    |
|                    | ctr ← x + 1 (2)    |
|                    | (done)             |

:::

### Mutexes

Mutexes or locks provide mutual exclusion: if threads (goroutines in this cae) call `m.Lock()` and `m.Unlock()` around a _critical section_, only one thread can be inside the critical section at any time.

```go
var m sync.Mutex
go func() {
  m.Lock()
  fmt.Println("hello...")
  fmt.Println("world")
  m.Unlock()
}()
m.Lock()
fmt.Println("bye...")
fmt.Println("there")
m.Unlock()
```

There's no longer any doubt about what interleavings are possible: each critical section must run atomically, so even with multiple calls to `fmt.Println` we expect only the two possible interleavings (plus the possibility that the goroutine never runs and we only see "bye... there").

### WaitGroup (barrier)

Go's `sync` package also provides `sync.WaitGroup`, a particular form of barrier used to wait for threads to finish:

```go
func printTwo() {
  var wg sync.WaitGroup
  wg.Add(2)
  go func() {
    fmt.Println("hello 1")
    wg.Done()
  }()
  go func() {
    fmt.Println("hello 2")
    wg.Done()
  }()
  wg.Wait()
}
```

Always prints "hello 1" and "hello 2" (in either order), and then returns. If we call this in `main` both print statements are guaranteed to run.

Not the same feature as locks! There's no mutual exclusion here, the fundamental primitive is waiting for something to happen.
