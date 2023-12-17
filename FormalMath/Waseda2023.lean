import Mathlib.Tactic.Ring

-- #check ℕ  -- ℕ : Type

def n0 := (42 : ℕ)

-- #check n0  -- n0 : ℕ
-- #eval n0  -- 42

-- #eval 2 * n0  -- 84

-- #check (ℕ → ℕ)  -- ℕ → ℕ : Type

def f := fun n => 2 * n

-- #check @f  -- f : ℕ → ℕ

-- #check f  -- f (n: ℕ) : ℕ
-- #print f

-- #eval f n0  -- 84

-- #check Nat

-- #check Nat.zero  -- Nat.zero : Nat
-- #check @Nat.succ  -- Nat.succ : Nat → Nat

-- #check Nat.rec

-- #check ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k  -- ∀ (n : ℕ), ∃ k, 4 * n = 2 * k : Prop

-- def Example1 := ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k

-- #check Example1  -- Example1 : Prop

def Example2 :Prop := ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k + 1

-- #check Example2  -- Example2 : Prop

/-
def CannotProve : Example2 := by
  rw [Example2]
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  specialize hn 0
  apply hn
  ring_nf
  rw [mul_comm]
  sorry
-/

-- def MyFirstProof' : ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k := sorry  -- declaration uses 'sorry'

def MyFirstProof : ∀ n : ℕ, ∃ k : ℕ, 4 * n = 2 * k := by
  intro n      -- we introduce a natural number `n` in our local context
  use (2 * n)  -- we claim that we can use `k = 2 * n` to solve the goal
  ring_nf      -- we finish the proof by computation

-- #check @MyFirstProof  -- MyFirstProof : ∀ (n : ℕ), ∃ k, 4 * n = 2 * k

-- #check MyFirstProof  -- MyFirstProof (n : ℕ) : ∃ k, 4 * n = 2 * k

-- #check MyFirstProof 2  -- MyFirstProof 2 : ∃ k, 4 * 2 = 2 * k

def EightIsEven : ∃ m : ℕ, 8 = 2 * m := MyFirstProof 2

def u : ℕ → ℕ := fun n =>
  match n with
  | 0 => 2
  | k + 1 => 2 * u k

open Nat

example (n : ℕ) : u n = 2 ^ (n + 1) := by
  induction n with
  | zero => simp [u, pow_one]
  | succ k ih => simp [succ_eq_add_one, u, ih]; ring_nf

def v : ℕ → ℕ := fun n =>
  match n with
  | 0 => 1
  | k + 1 => 2 * v k + 1

example (n : ℕ) : v n = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [v, pow_one];
  | succ k ih => simp [succ_eq_add_one, v, ih]; ring_nf; sorry  -- hint: change the return type of v

example {X Y : Type} {f : X → Y} (a b : X) : (a = b) → f a = f b := by
  intro h
  induction h
  exact Eq.refl (f a)

-- #check @Eq.rec  -- the induction principle for the Eq type says that if a = b, we can substitute a for b everywhere

theorem EqSymm {X : Type} (a b : X) : (a = b) → b = a := by
  intro h
  induction h
  exact Eq.refl a

theorem EqTrans {X : Type} (a b c : X) : a = b → b = c → a = c := by
  intro h1 h2
  induction h1
  exact h2

-- #printaxioms EqSymm  -- 'EqSymm' does not depend on any axioms
-- #printaxioms EqTrans  -- 'EqTrans' does not depend on any axioms

-- #printaxioms MyFirstProof  -- 'MyFirstProof' depends on axioms: [propext]

-- #check @propext  -- @propext : ∀ {a b : Prop}, (a ↔ b) → a = b

theorem propextTest {a b : Prop} {P : Prop → Prop} : (a ↔ b) → (P a ↔ P b) := by
  intro h
  rw [h]

-- #printaxioms propextTest  -- 'propextTest' depends on axioms: [propext]

-- Universes: the type `Prop` is actually `Sort 0`, i.e. types of level 0. And the type `Type` is `Sort 1`, i.e. types of level 1.

-- #check Prop  -- Prop : Type
-- #check Type  -- Type : Type 1

-- #check Sort 0  -- Prop : Type
-- #check Sort 1  -- Type : Type 1

-- This goes on until Type 32 (that limit can be increased if necessary).

-- #check Sort 2  -- Type 1 : Type 2

-- #check Sort 32  -- Type 31 : Type 32
-- #check Sort 33  -- maximum universe level offset threshold has been reached (32)

-- The following types are terms of type `Sort 1` (denoted here by Type).
-- #check ℕ  -- ℕ : Type
-- #check ℕ → ℕ  -- ℕ → ℕ : Type
-- #check Prop  -- Prop : Type
-- #check Prop → Prop  -- Prop → Prop : Type

-- `Sort 1` itself (which is the same as 'Type 0', or just 'Type') is a term of type `Sort 2` (denoted here by `Type 1`).

-- #check Type  -- Type : Type 1

-- A type of `Sort n` is automatically seen as a type of `Sort p` for all `p ≥ n`. The type of functions between a type of `Sort n` and a Type of `Sort m` is a term of type `Sort max(n, m)`

-- #check Prop → Type  -- Prop → Type : Type 1
-- #check Type → Prop  -- Type → Prop : Type 1

-- The point of having universe level is to be able to quantify over types of a certain level. For example, the following type checks.

-- #check ∀ X : Type, ∀ x : X, x = x  -- ∀ (X : Type) (x : X), x = x : Prop

-- In fact, we can do more, because Equality is defined on all levels.

-- #check @Eq  -- @Eq : {α : Sort u_1} → α → α → Prop
-- #check @Eq.{0}  -- @Eq : {α : Prop} → α → α → Prop
-- #check @Eq.{1}  -- @Eq : {α : Type} → α → α → Prop
-- #check @Eq.{2}  -- @Eq : {α : Type 1} → α → α → Prop

-- Again, the following type checks. However, equality of types of level 1 or more is rarely used.

-- #check ∀ X : Type, X = X  -- ∀ (X : Type), X = X : Prop

universe n

-- #check ∀ X : Type n, X = X  -- ∀ (X : Type n), X = X : Prop

-- The Fibonacci sequence

def Fib : ℕ → ℕ := fun n =>
  match n with
  | 0 => 0
  | 1 => 1
  | succ (succ k) => Fib k + Fib (succ k)

-- #check Fib -- Fib : ℕ → ℕ
-- #eval Fib 32  -- It takes time to compute!
