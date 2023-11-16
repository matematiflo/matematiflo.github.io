---
marp: true
#size: 4:3
theme : default
#class: invert
math: mathjax

---

# An informal introduction to formal mathematics

> 早稲田大学
> 2023/11/29

Florent Schaffhauser
Heidelberg University

---

<!--paginate: true -->
<!-- footer: Waseda University, Geometry Seminar -->
<!--
_backgroundColor: cyan
_color: black
-->
## Goal: introductory talk on Proof Assistants and Formal Mathematics

![bg right:50% w:600](NNG4.png)

![width:400 sepia:50%](NNG4.png)

---
<!--
_backgroundColor: cyan
_color: black
-->
## Introduction (2 mins)

- Briefly introduce yourself and set the stage for the talk.
- Pose a concise thought-provoking question related to formal mathematics.

---

## Formalised mathematics

- Formalisation of mathematics is not a new idea: Leibniz, Frege, ...
- Neither is the notion of a *computer* (person or machine).
- What is relatively recent is the *use of computers to formalise proofs* (1960s onward).
- The formalisation of mathematics poses a number of challenges and difficulties.
- It also offers a lot of opportunities in a digital age (e.g. in teaching).

What is the current state of affairs and what can we hope to achieve?

---

## From Leibniz to the *Principiae Mathematicae*

-

---

## Formal proofs

- Two aspects: correctness checking and automation.
-

---
<!--
_backgroundColor: cyan
_color: black
-->
## Historical context and recent advances (15 mins)

- Provide a swift overview of the historical development of proof assistants.
- Connect historical milestones to the challenges faced by mathematicians.
- Discuss key recent advancements in proof assistants and their impact on contemporary mathematics.

---
<!--
_backgroundColor: cyan
_color: black
-->
## A primer on type theory for mathematicians (15 mins)

- An introduction to type-theoretic mathematics.

---

## Type-theoretic mathematics

*Claim:* It is possible to build a large amount of modern mathematics using type-theoretic foundations. The following three concepts play a central role in this.

- Inductive types.
- The `Prop` type.
- The type of dependent functions (a.k.a. `Pi` types).

To go further, one can also incorporate concepts from *Homotopy type theory* (`HoTT`).

But first, *what is a type*?

---

## Types and terms

A *type* is specified by its *terms*. For instance, most programming languages contain an implementation of the type of natural numbers `ℕ`, whose terms are `0, 1, 2, ...`.

```haskell
#check ℕ                              -- ℕ : Type

def n0 := (42 : ℕ)

#check n0                             -- n0 : ℕ

#eval n0                              -- 42
```

The example above uses the syntax of the **Lean programming language**, created by Leanardo De Moura in 2013. Basic computations are natively supported in Lean.

```haskell
#eval 2 * n0                          -- 84
```

---

## Functions between types

If `X` and `Y` are types, there is a type `X → Y`. Its terms are the functions from `X` to `Y`.

```haskell
#check (ℕ → ℕ)                       -- ℕ → ℕ : Type

def f := fun (n : ℕ) => 2 * n

#check @f                            -- f : ℕ → ℕ
```

`def f := λ (n : ℕ), 2 * n` would also be recognised by the compiler.

```haskell
#check f                             -- f (n : ℕ) : ℕ
```

Functions can be evaluated on terms. The syntax `#eval f(n0)` would not compile.

```haskell
#eval f n0                           -- 84
```

---

## Inductive types

For instance, the type of natural numbers `ℕ`.

```haskell
inductive ℕ :=
| 0 : ℕ
| succ (n : ℕ) : ℕ
```

> **SAY MORE ON THIS** (with `#check ℕ.succ`, `#check @ℕ.succ` *etc*). Then mention Lists and proofs by induction (or even just pattern matching and cases by case check).

---

## The `Prop` type

`Prop` is the type whose terms are the formulas from first-order logic.

One starts from a language, with basic symbols such as `+` or `` , and defines formulas inductively, following a set of rules. Terms of type `Prop` are defined by such formulas.

```haskell
def Example1 := ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k

#check Example1                       -- Example1 : Prop
```

Up to here, we are working in *simple type theory*, and we can already do some mathematics in it, for example prove the above proposition.

---

## Propositions as types

And proofs as terms (Curry-Howard isomorphism). Requires a *hierarchy* of types.

---

## The type of dependent functions

---
<!--
_backgroundColor: cyan
_color: black
-->
## Motivation, Purpose, and Engaging Examples (20 mins)

- Share your personal motivation for working in this field.
- Clearly articulate the purposes and benefits of proof assistants in modern mathematics.
- Present interactive examples or mini-problems related to formal mathematics, inviting audience participation.

---
<!--
_backgroundColor: cyan
_color: black
-->
## Challenges and Limitations (5 mins)

- Address the intrinsic difficulties and limitations in the field.
- Acknowledge ongoing challenges and areas for improvement.

---
<!--
_backgroundColor: cyan
_color: black
-->
## Reflection and Closing Discussion (3 mins)

- Summarize key points and insights from the talk.
- Open the floor for a brief discussion or reflections from the audience.

---
