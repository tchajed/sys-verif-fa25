---
category: lecture
order: 16
shortTitle: "Lecture 16: Concurrency intro"
pageInfo: ["Date", "Category", "Tag", "Word"]
---

# Lecture 16: Concurrency introduction

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

Depends on what is atomic. In this case, ultimately printing is a `write(2)` system call to the stdout file of the process, and these writes are turned into output on the terminal device - there's no real guarantee but most likely the write system calls are each atomic, and Go will issue one for each `fmt.Println`.

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

$$(T_1 \listapp [\spawn \, e] \listapp T_2, h) \leadsto_{tp} (T_1 \listapp [()] \listapp T_2 \listapp [e], h)$$

This time the heap is uninvolved, and the only effect is to create a new thread. This rule may look strange on its own, since $\spawn \, e$ immediately seems to terminate in a value and thus no new threads are created. If $\spawn \, e$ were part of a larger program then the remainder would continue to run, so for example $(\spawn \, e); e'$ would become two threads, $e$ and $e'$.

Recall that we defined the soundness of separation logic in terms of whether an expression got stuck: if $(e, h)$ cannot step to anything and $e$ is not a value, then we called it stuck. Soundness was partly about expressions not getting stuck (and partly about the postcondition being true if they did terminate in a value). We have to decide what to do with those definitions now that there are multiple threads.

The decision we'll take is that the _concurrent separation logic_ we develop will show that after an expression has run for a while, _none of the spawned threads are stuck_, but the postcondition will only apply to the value of the "main thread", the first element of the threadpool - background threads can go into infinite loops or terminate in any value.

## Synchronizing programs

Since threads interleave with each other, we will need programming mechanisms to control how they interleave. First, let's see one example of a bug due to interleavings. Then, we'll see two core synchronization primitives: mutexes provide mutual exclusion (e.g., to make more than one assembly instruction run atomically) and barriers provide waiting (e.g., to efficiently implementing waiting for several threads to finish).

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
