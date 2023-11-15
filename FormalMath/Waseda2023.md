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

## Goal: introductory talk on Proof Assistants and Formal Mathematics

![bg right:50% w:600](NNG4.png)

![width:400 sepia:50%](NNG4.png)

---

## Introduction (2 mins)

- Briefly introduce yourself and set the stage for the talk.
- Pose a concise thought-provoking question related to formal mathematics.

---

## Formalised mathematics

- Formalisation of mathematics is not a new idea: Leibniz, Frege, ...
- Neither is the notion of a *computer* (person or machine).
- What is relatively recent is the use of computers to formalise *proofs* (1960s onward).
- The formalisation of mathematics poses a number of challenges and difficulties.
- It also offers a lot of opportunities in this digital age (e.g. in teaching).

What is the current state of affairs and what can we hope to achieve?

---

## From Leibniz to the *Principiae Mathematicae*

-

---

## Formal proofs

- Two aspects: correctness checking and automation.
-

---

## Historical context and recent advances (15 mins)

- Provide a swift overview of the historical development of proof assistants.
- Connect historical milestones to the challenges faced by mathematicians.
- Discuss key recent advancements in proof assistants and their impact on contemporary mathematics.

---

## A primer on type theory for mathematicians (15 mins)

- An introduction to type-theoretic mathematics.

---

## Type-theoretic mathematics

*Claim:* It is possible to build a large amount of modern mathematics using type-theoretic foundations. The following three concepts play a central role in this.

- Inductive types.
- The `Prop` type.
- The type of dependent functions (`Pi` types).

To go further, one can also incorporate concepts from *Homotopy type theory* (`HoTT`).

---

## Types and terms

A *type* is specified by its *terms*. Most programming languages contain an implementation of the natural numbers.

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

If `X` and `Y` are types, there is a type `X → Y`: its terms are the functions from `X` to `Y`.

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

> **SAY MORE ON THIS** (with `#check ℕ.succ`, `#check @ℕ.succ` *etc*).

---

## The `Prop` type

`Prop` is the type whose terms are the formulas from first-order logic.

You start from a language, with basic symbols such as `+` or `` , and you define formulas inductively, following a set of rules.

```haskell
def Example1 := ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k

#check Example1                       -- Example1 : Prop
```

---

## The type of dependent functions

---

## Propositions as types

And proofs as terms (Curry-Howard isomorphism). Requires a *hierarchy* of types.

---

## Motivation, Purpose, and Engaging Examples (20 mins)

- Share your personal motivation for working in this field.
- Clearly articulate the purposes and benefits of proof assistants in modern mathematics.
- Present interactive examples or mini-problems related to formal mathematics, inviting audience participation.

---

## Challenges and Limitations (5 mins)

- Address the intrinsic difficulties and limitations in the field.
- Acknowledge ongoing challenges and areas for improvement.

---

## Reflection and Closing Discussion (3 mins)

- Summarize key points and insights from the talk.
- Open the floor for a brief discussion or reflections from the audience.

---

## Real algebra

1. [Sums of squares](https://github.com/matematiflo/Real_Algebraic_Geometry/blob/main/Sums_of_squares/Sums_of_squares.md)
2. Formally real fields
3. Artin-Schreier theory
4. Real-closed fields
5. The real closure of an ordered field

---

### Sums of squares

Sums of squares are defined inductively, on terms of type `List R` where `R` is a semiring.

```python
def sum_of_squares {R : Type} [Semiring R] : List R → R
| [] => 0
| (a :: L) => (a ^ 2) + (sum_of_squares L)
```

Recall that lists are defined inductively themselves:  

> A list `L` is either the empty list `[]` or of the form `a :: l`, where `l` is an already defined list.

---

## Concatenated lists

The sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2`

```haskell
@[simp]
def sum_of_squares_concat {R : Type} [Semiring R] 
  (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
    := by
      induction L1 with 
      | nil => simp [sum_of_squares] 
      | cons a L ih =>
        simp [sum_of_squares]
        rw [ih]
        rw [add_assoc]
      done
```
