---
icon: "circle-exclamation"
---

# Syllabus

This class is an introduction to _systems verification_. The core idea is understanding how to write a mathematical proof that a program is correct, a process called (program) _verification_. The class is called "_systems_ verification" because we will focus on techniques applicable to low-level systems software with features like pointers and concurrency (in some future version of this class I hope to also cover distributed systems, but the techniques aren't quite there yet).

::: important Read the syllabus!

This syllabus is a bit long. I suggest you skim it at the beginning of class so you know what's covered, and then refer back to it if something comes up.

:::

The class is divided into three sections:

**Functional programs**: We'll start by learning how to write and verify _functional_ programs, a style of programming which emphasizes functions and where we won't have complications like modifying variables. This is also where we'll introduce the Rocq Prover, which we'll use to do the proofs in this class.

**Imperative programs**: Next, we'll introduce the techniques to reason about imperative programs, which can modify heap-allocated variables. We'll also increase the realism by switching to reasoning about programs written in Go. The theoretical tool that allows us to reason about the heap is separation logic.

**Concurrent programs**: Finally, we'll introduce techniques to reason about concurrency. It turns out separation logic will help once again with this challenge.

## General identifying information

- **Institution name:** University of Wisconsin-Madison
- **Course number**: CS 839-002: Systems Verification
- **Credits**: 3 credit hours
- **Requisites**: mathematical maturity and programming experience (see [below](#prerequisites))
- **Meeting time and location**: Tuesday/Thursday 1-2:15pm, Morgridge Hall 2538
- **Instruction modality**: in-person
- **Instructor contact info**: \
  Prof. Tej Chajed &lsaquo;<chajed@wisc.edu>&rsaquo; \
  office hours: Wednesday/Thursday 3-4pm in Morgridge 7572

## Course learning outcomes

By the end of this class, you should be able to:

1. Prove theorems in the Rocq Prover
2. Verify imperative programs using separation logic
3. Verify (small) concurrent programs
4. Articulate the guarantees of formal verification

Hopefully you will also have fun along the way.

## Expected workload

This class is 3 credit hours. That means you can expect to spend 3 hours in lecture and 6 hours outside of lecture each week.

You'll spend most of the time on this class outside of lecture doing the assignments. There aren't many due dates, but you should still be putting in some time each week so you make steady progress and have time to ask questions, think about the material, re-read lecture notes, and get unstuck. If you start an assignment a day or two before it's due you're going to have a bad time.

## Prerequisites

The two main requirements are "mathematical maturity" and "programming experience." Mathematical maturity means you're comfortable with being precise and learning new math, which is required to understand program proofs. Programming experience is needed since the proofs will be programs written in the Rocq Prover (which you'll need to be able to learn efficiently).

You do not need to have any experience with the Rocq prover.

You do not need to have used Go before. We will verify code written in Go, but you won't be writing or modifying it (except optionally as part of the project). You should be able to get up-to-speed in reading Go quickly if you have some familiarity with C syntax.

## Assignments and grading

There will be two programming assignments in Rocq, one written theory assignment, and a final project in Rocq. See the [assignments page](./assignments/) for details.

Grading:

- Assignment 1: 20%
- Assignment 2 (theory): 15%
- Assignment 3: 25%
- Final project: 40%

Here's a grading scale to give you a rough idea, but cutoffs may be lower if the assigned points are unexpectedly low:

| grade | percentage |
| ----: | ---------- |
|     A | $\geq$ 93  |
|    AB | $\geq$ 86  |
|     B | $\geq$ 80  |
|    BC | $\geq$ 74  |

The idea behind grading is that if you make an earnest attempt at every assignment, and if you get stuck you're able to explain what you tried, you should get at least an AB.

Hand-in: submit to Canvas. See more details in the [assignment setup](./assignments/setup) page.

## Office hours

I'll hold office hours twice a week, using my office, Morgridge 7572. Office hours are time I've blocked off for you, so please use them! You can stop by and ask whatever you want, including but not limited to:

1. Help with a Rocq programming assignment
2. A conceptual question about the lecture material
3. A question about something beyond the lecture
4. Advice on anything communication related

I encourage all students to stop by office hours and introduce yourself (you can just say hi or stop and chat for a bit) during the first two weeks of the semester.

## Collaboration

You can work on assignments and the final project in groups of up to two. Both of you should submit, but it's okay if the submissions are identical. Please clearly state who you worked with by putting your partner's name in a comment at the top of each file you modify.

The first assignment is crucial to learning Rocq, so I would suggest that even if you have a partner you type out the solutions independently so you both get experience using Rocq as an interactive tool.

## Generative AI policy

If you use generative AI like ChatGPT or another LLM, you are required to explain how you used it. You may use GitHub CoPilot without an explanation.

I do not believe ChatGPT does well on Rocq proofs in general, and especially on the course material, but I would be happy to be proven wrong.

You will need to read and understand what ChatGPT says. Identifying its mistakes is likely to be good for your learning, which is why it's permitted in the first place, but it is important that you not blindly follow it.

## Late policy

For the programming exercises and theory assignment, you get 3 "late days" to use throughout the semester. You don't need to tell me to use them, just submit late. If you have extenuating circumstances and need more time, let me know as soon as possible.

## Student well-being

I realize this class isn't the only thing in your life. If this class ever feels overwhelming on top of whatever else you're responsible for, please let me know and we can work something out. Do this early! I don't want it to stress you out, I want you to learn something.

Students are encouraged to learn about and utilize UW-Madison's mental health services and/or other resources as needed. Visit [uhs.wisc.edu](https://www.uhs.wisc.edu/) or call University Health Services at (608) 265-5600 to learn more.

## Academic policies

See this list of [standard syllabus statements](https://teachlearn.wisc.edu/course-syllabi/#policies) with university policies, including academic integrity, diversity & inclusion, and accommodations for students with disabilities.

## Course communication

If you have any questions, you can either (a) post on Piazza (preferred), (b) come to office hours, or (c) (if office hours don't work for you) schedule a time by sending me an email with some suggested times.

## Asking questions

Asking questions is a skill, an extremely useful one. When you ask a question, you should:

1. Give sufficient context for your question. For this class, including your proof so far and current proof state (a screenshot often works for this) is helpful and often necessary for me to help. You can attach your code if I need to open it up and try something myself, by using `./etc/prepare-submit` and attaching `hw.tar.gz`.
2. Describe your understanding of the problem.
3. Describe what you're trying to do and what you've tried so far.
4. Aim to make your question easy to read.

Some questions will be about conceptual challenges and others will be about the mechanics of using Rocq. Both are fine to ask. If it's a conceptual difficulty, try to ask something that isn't too specific to the Rocq code. If it's a mechanical question about Rocq, try to explain your informal proof argument or how you want to manipulate the proof state - for example, if you say you have a theorem that says `∀ n, P n ∨ Q` and in a proof you want to consider the two cases `P 3` and `Q`, then I know this is a purely mechanical question about using Rocq and can give you a direct answer.
