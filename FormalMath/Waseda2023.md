---
marp: true
#size: 4:3
theme : default
#class: invert
math: mathjax

---

# An informal introduction to formal mathematics

> 早稲田大学 Geometry Seminar
> 2023/11/29

Florent Schaffhauser
Heidelberg University

---
<!--
paginate: true
footer: Waseda University, Geometry Seminar 
header: Introductory words and outline of the talk
-->

## Formalised mathematics

- Formalisation of mathematics is not a new idea (think of Leibniz, Peano, Russell and Whitehead, Bourbaki, ... ).
- Neither is the notion of a *computer* (person or machine: think of Pascal, Euler, ... ).
- What is relatively recent is the *use of computers to formalise proofs* (1960s onward).
- The formalisation of mathematics poses a number of challenges and difficulties (not only technical).
- It also offers a lot of opportunities in a digital age (e.g. [in teaching][HTPIWL]).

*Is checking correctness the main goal of formalised mathematics?* If not, what is it?

---

## Formal proofs and mathematical libraries

- We should distinguish between the development of proof assistants, which is a research area at the intersection of mathematics, logic and computer science, and the formalisation of known mathematical results, which is about building mathematical libraries usable by a proof assistant.
- As far as libraries are concerned, the two basic goals of formalisation are *checking correctness* and *automating certain proofs*.
- A challenging question is whether this can help mathematicians do research and transfer knowledge.
- A related one is whether it can make mathematics more widely usable in other fields, or even more accessible in general.

---

## Outline of the talk

1. A brief overview of computer-assisted mathematics
1. A primer on type theory for mathematicians
1. Learning the basics of Lean: The Natural Number Game
1. Challenges and opportunities of the use of proof assistants

---
<!--
_header: ""
-->

## A brief overview of computer-assisted mathematics

---
<!--
header: A brief overview of computer-assisted mathematics
-->
## Foundations of mathematics

- Mathematics uses the rules of logic for deductive reasoning.
- *Classical logic* assumes the Law of Excluded Middle.
- Proofs by contraposition or by contradiction are commonly used in mathematics.
- Following Cantor, Hilbert, Zermelo, Fraenkel and Bourbaki, *set theory* serves as foundations of mathematics: numbers, functions, equivalence relations, *etc*, are all sets.
- Some proof assistants use this same (set-theoretic) framework (e.g. [Mizar][Mizar]).
- For the purpose of computer programming, type-theoretic foundations might be more convenient ("everything is a function").

---

## Mathematics in the age of computers

- Why and how to use computers to do mathematics?
- First and foremost: because they can *compute* for us.
- They can also help *verifying* a mathematical proof.
- A famous example is the [Four-colour theorem][4colour] (K. Appel and W. Haken, $1976$). The proof shows that the theorem holds except perhaps in a finite number of cases.
- Those $1834$ cases were then shown to be 4-colourable using various computer programs and algorithms, some of them written by J. Koch. Part of the proof was checked manually by Haken's daughter Dorothea Blohstein (born Haken).
- A formal proof of the four-colour theoren was written in 2005 by G. Gonthier, *using only the proof assistant Coq* (no other program necessary).

---

## Beyond computations

- Nowadays, computers can also be used to write abstract proofs, or to handle particularly complex ones.
- Proofs of the [prime number theorem][PNT] have been formalised in Isabelle.
- The [Feit-Thompson theorem][OddOrder], stating that a finite group of odd order is solvable, has been [formalised in Coq][MathComp.OddOrder].
- This has stimulated a lot of *research and progress on proof assistants themselves*.
- A recent example of the use of computers in mathematical research is provided by the [Liquid Tensor Experiment][LTE], which says that certain $Ext$ groups of the set of measures on a profinite set vanish.
- This is part of D. Clausen and  P. Scholze's approach to a general theory of analytic spaces, which is *currently being developed*.

---

## Formalising mathematics

- Is about *representing* mathematical concepts in a *formal language*.
- We want to be able to define objects, state theorems and write proofs on which we can rely and that we can "unwrap".
- There is a mechanical aspect (the compilation of the program) and a conceptual one (the writing of said program).
- The readability of the code may vary, but the result can be trusted with a high degree of confidence.
- We can implement routine procedures to help us write proofs or compute quantities.

---

## Formal languages and verifications

- In linguistics, a formal language consists of words created from an alphabet and put together according to a set of rules called a grammar.
- Computer programs are written in formal languages.
- Formal languages developed *for the purposes of representing mathematical objects* started to emerge in the 1960s:
  - The pioneers were Automath (1967), Thm (1972), [LCF][LCF] (1972) and Mizar (1973).
  - The following generation used Higher Order Logic: HOL, Isabelle (1986), HOL-Light, *etc*.
  - Nowadays, many proof assistants use [Dependent Type Theory][DTT]: Coq (1989), Agda (1999), Lean (2013), *etc*.

---

## Structure of an interactive theorem prover

![bg right:50% width:500 sepia:10%](ITP.png)

- While different proof assistants are not compatible between one another, the basic structure is always the same.
- They are used by communities with different interests and preoccupations, both for program certification and proof verification.

*Image credits:* [Assia Mahboubi][Assia].

---
<!--
_header: ""
-->

## A primer on type theory for mathematicians

---
<!-- 
header: A primer on type theory 
-->

## Type-theoretic mathematics

*Claim:* It is possible to build a large amount of modern mathematics using type-theoretic foundations.

The general framework is built on top of the [Calculus Of Constructions][COC], and is called [Dependent Type Theory][DTT]. It includes:

- Inductive types.
- The `Prop` type.
- The type of dependent functions (a.k.a. `Pi` types).

To go further, one can also incorporate concepts from [Homotopy type theory][HoTT] (`HoTT`).

But first, *what is a type*?

---

## Types and terms

A *type* is specified by its *terms*. For instance, most programming languages contain an implementation of the type of natural numbers `ℕ`, whose terms are `0, 1, 2, ...`.

```haskell
#check ℕ                              -- ℕ : Type

def n0 := (42 : ℕ)

#check n0                             -- n0 : ℕ
#reduce n0                              -- 42
```

The example above uses the syntax of the [Lean programming language][Lean], created by Leonardo de Moura in 2013. Basic computations are natively supported in Lean.

```haskell
#reduce 2 * n0                          -- 84
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

Functions can be evaluated on terms. The syntax `#reduce f(n0)` would not compile.

```haskell
#reduce f n0                           -- 84
```

---

## Inductive types

Natural numbers can be implemented as an inductive type using [Peano's axiomatization][Peano].

```haskell
inductive Nat :=
| zero : Nat
| succ (n : Nat) : Nat
```

So `zero` is a term of type `Nat`. And for all term `n` of type `Nat`, there is a term `succ n`.

```haskell
#check Nat.zero                      -- Nat.zero : Nat
#check @Nat.succ                     -- Nat.succ : Nat → Nat
```

The terms `zero` and `succ` are functions whose return type has not yet been declared (these are called *constructors*). The notation `ℕ` and `0` is introduced a posteriori.

---

## Principle of induction

Because `Nat` is declared as an inductive type, the compiler *automatically* generates a principle of induction. Note the occurence of the `Prop` type, which requires further explanation (on the next slide!).

```haskell
#check Nat.rec
  -- Nat.rec {P : ℕ → Prop} 
  --  (zero : P 0)
  --  (succ : ∀ (n : ℕ), P n → P (n + 1)) : 
  --  ∀ (t : ℕ), P t
```

In the code above, `Nat.rec` is seen as a function that, in the presence of a *predicate* `P : ℕ → Prop`, sends a proof of `P 0` and a proof of the fact that, for all `n : ℕ`, `P n` implies `P (n + 1)`, to a proof of `P t` for all `t : ℕ`.

---

## The `Prop` type

`Prop` is the type whose terms are the formulas from [first-order logic][FOL].

One starts from a language, with basic symbols such as `+` or `` , and defines formulas inductively, following a set of rules. Terms of type `Prop` are defined by such formulas.

```haskell
def Example1 := ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k

#check Example1                       -- Example1 : Prop
```

This is a well-defined mathematical statement, but we have not proved it yet.

---

## Propositions as types

Mathematically erroneous statements will type-check if they are syntactically correct.

```haskell
def Example2 := ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k + 1

#check Example2                       -- Example2 : Prop
```

To start doing mathematics, the idea is to *view propositions as types*, whose terms are *proofs of that proposition*. In proof theory, this is known as the [Curry-Howard correspondence][CurryHoward].

```haskell
def MyFirstProof : ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k := sorry
```

Here, `MyFirstProof` is a term of type `∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k`.

---

## Multiples of `4` are divisible by `2`

To formalise a proof, one works backwards, reducing the *goal* to a known statement.

```haskell
def MyFirstProof : ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k := by
  intro n      -- we introduce a natural number `n` in our local context
  use (2 * n)  -- we claim that we can use `k = 2 * n` to solve the goal
  ring_nf      -- we finish the proof by computation
```

Evolution of the *tactic state*:

```lean
∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k  -- goal at the beginning
∃ k : ℕ, 4 * n = 2 * k           -- after intro n
4 * n = 2 * (2 * n)              -- after use (2 * n)
No goals                         -- ring_nf closes the goal
```

---

## The type of dependent functions

Our term `MyFirstProof` is recognised as a *dependent function*: it sends a natural number `n` to a proof of a statement *that depends on* `n`.

```haskell
#check @MyFirstProof  -- MyFirstProof : ∀ (n : ℕ), ∃ k, 4 * n = 2 * k

#check MyFirstProof   -- MyFirstProof (n : ℕ) : ∃ k, 4 * n = 2 * k
```

The term `MyFirstProof 2` is recognised as a proof of the proposition `∃ k, 4 * 2 = 2 * k` and we can use it as such.

```haskell
#check MyFirstProof 2  -- MyFirstProof 2 : ∃ k, 4 * 2 = 2 * k

def EightIsEven : ∃ m : ℕ, 8 = 2 * m := MyFirstProof 2
```

---
<!-- 
_header: ""
-->

## Learning the basics of Lean: the Natural Number Game

---
<!-- 
header: "The Natural Number Game"
-->

## The Natural Number Game

- The [Natural Number Game][NNG4] is the classical introduction game for Lean.
- In it, one recreates the natural numbers $\mathbb{N}$ from the Peano axioms, learning the basics of theorem proving in the process.
- The [original version][NNG3] was created for Lean 3 by Kevin Buzzard and Mohammad Pedramfar.
- The current version, written in Lean 4, is currently hosted on the [Lean Game Server][LeanGame], created and maintained by Alexander Bentkamp and Jon Eugster at the University of Düsseldorf.

---

## Let us play it together

![bg right:50% width:700](NNG.png)

Can we prove that addition of natural numbers is commutative?

```haskell
theorem add_comm : 
  ∀ (a b : ℕ), a + b = b + a
```

This is [Level 3][Level3Boss] of the Addition World in NNG 4.

<!--
induction a with k ih
rw [add_zero]
rw [zero_add]
rfl
rw [succ_add]
rw [ih]
rw [add_succ]
rfl
-->
---
<!-- 
_header: ""
-->

## Challenges and opportunities of the use of proof assistants

---
<!--
header: Challenges and opportunities
-->

## Using proof assistants to do mathematics

Beyond technical difficulties (software installation and update), the use of proof assistants to do mathematics poses a number of challenges.

- The learning curve starts off steep: basic tactics such as induction can be difficult to handle, due to syntactic and type-theoretic difficulties.
- Navigating the libraries can be equally difficult. There is a need for better documentation.
- Basic mathematics are not written in type-theoretic language (for now?), which can make formalisation convoluted if we insist on stating the result set-theoretically.

---

## Recursive definitions and proofs by induction

Let us define a sequence recursively in Lean (by pattern matching).

```haskell
def u : ℕ → ℕ := fun n =>
  match n with
  | 0 => 2
  | k + 1 => 2 * u k
```

And then we can prove simple results using the induction tactic.

```haskell
example (n : ℕ) : u n = 2 ^ (n + 1) := by
  induction n with
  | zero => rw [u, pow_one]
  | succ k ih => rw [succ_eq_add_one, u, ih]; ring_nf
```

However, type-theoretic difficulties can arise inadvertently (for instance with `v` defined by `v 0 = 1` and `v (k + 1) = 2 * v k + 1`).

---

## Equality and substitution

In Lean, equality is an inductive type. The declaration below means that, for all `a : X`, `refl a` is a proof of `a = a`. Two terms are equal if and only if they are *definitionally* so.

```haskell
inductive Eq {X : Type} : X → X → Prop
| refl (a : X) : Eq a a
```

We can then use the asociated induction principle to prove the symmetry and transitivity of the relation `Eq`. Similarly, given a function `f`, we can prove that `a = b → f a = f b`.

```haskell
example {X Y : Type} {f : X → Y} (a b : X) : (a = b) → f a = f b := by
  intro h           -- We introduce a term for the assumption that a = b
  induction h       -- We start a proof by induction on a term of type Eq
  exact Eq.refl (f a)
```

Note that the induction lays on the term of inductive type `h`, which is a *proof* that `a = b`.

---

## The equality relation is symmetric and transitive

Note that a relation on a type `X` is by definition a function `Rel : X → X → Prop` as opposed to a subset of `X × X` in set-theoretic mathematics.

```haskell
theorem EqSymm {X : Type} (a b : X) : (a = b) → b = a := by
  intro h
  induction h
  exact Eq.refl a

theorem EqTrans {X : Type} (a b c : X) : a = b → b = c → a = c := by
  intro h1 h2
  induction h1
  exact h2
```

It is a good exercise to formalise what it means for a relation `Rel` on a type `X` to be reflexive, symmetric and transitive.

---
<!--
header: "Concluding remarks"
-->

## Thinking about mathematics differently

- Using a proof assistant is a good opportunity to renew our approach to mathematics and consolidate our knowledge, at all levels.
- While challenging, it opens a world of possibilities in research and teaching.
- We can use computers to engage students and make mathematics accessible to wider audiences.
- How this tool is shaped now might play a big role in the way humans will do mathematics in the future, including research.

So, why not *Lean into it*? (^_^)/

[FOL]: https://en.wikipedia.org/wiki/First-order_logic
[HTPIWL]: https://djvelleman.github.io/HTPIwL/
[Level3Boss]: https://adam.math.hhu.de/#/g/hhu-adam/NNG4/world/Addition/level/3
[4colour]: https://en.wikipedia.org/wiki/Four_color_theorem
[PNT]: https://en.wikipedia.org/wiki/Prime_number_theorem
[OddOrder]: https://en.wikipedia.org/wiki/Feit–Thompson_theorem
[MathComp.OddOrder]: https://github.com/math-comp/odd-order
[LTE]: https://leanprover-community.github.io/blog/posts/lte-final/
[Assia]: http://people.rennes.inria.fr/Assia.Mahboubi/
[COC]: https://en.wikipedia.org/wiki/Calculus_of_constructions
[HoTT]: https://homotopytypetheory.org/book/
[Lean]: https://en.wikipedia.org/wiki/Lean_(proof_assistant)
[Peano]: https://en.wikipedia.org/wiki/Peano_axioms
[NNG4]: https://adam.math.hhu.de/#/g/hhu-adam/NNG4
[NNG3]: https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/index2.html
[LeanGame]: https://adam.math.hhu.de
[CurryHoward]: https://en.wikipedia.org/wiki/Curry–Howard_correspondence
[LCF]: https://en.wikipedia.org/wiki/Logic_for_Computable_Functions
[DTT]: https://en.wikipedia.org/wiki/Dependent_type
[Mizar]: https://en.wikipedia.org/wiki/Mizar_system
