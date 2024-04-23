/-
# A Lean Introduction to Formal Methods for Mathematicians

Copyright (c) 2023 Matematiflo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser.
-/

namespace Tutorial

/- ## Simply-typed functions and curried functions -/

/- ### The square function -/

def square : Nat → Nat := fun (n : Nat) => n ^ 2

#check @square  -- square : Nat → Nat

def square' := fun (n : Nat) => n ^ 2

#check @square'  -- square' : Nat → Nat

def square'' (n : Nat) : Nat := n ^ 2

#check @square''  -- square'' : Nat → Nat
#check square''   -- square'' (n : Nat) : Nat

#check square 3  -- square 3 : Nat
#eval  square 3  -- 9

/- ## The factorial of an integer -/

def fact (n : Nat) : Nat := match n with
| 0     =>  1
| k + 1 => (k + 1) * fact k

#check @fact   -- fact : Nat → Nat
#eval  fact 5  -- 120

def fact' (n : Nat) : Nat := match n with
| Nat.zero   =>  1
| Nat.succ k => (Nat.succ k) * fact' k

/- ### The Fibonacci sequence -/

def Fib (n : Nat) : Nat := match n with
| 0     => 0
| 1     => 1
| k + 2 => Fib (k + 1) + Fib k

#check @Fib      -- Fib : Nat → Nat
#eval Fib  6     -- 8
#eval Fib 10     -- 55
#eval Fib 20     -- 6765

def Fib' (n : Nat) : Nat := match n with
| Nat.zero   => 0
| Nat.succ k => match k with
  | Nat.zero   => 1
  | Nat.succ m => Fib' m + Fib' (Nat.succ m)

#check [Fib 3, Fib 4, Fib 5]  -- [Fib 3, Fib 4, Fib 5] : List Nat
#eval  [Fib 3, Fib 4, Fib 5]  -- [2, 3, 5]

def Fib_up_to (n : Nat) : List Nat := match n with
| 0     => [Fib 0]
| k + 1 => List.concat (Fib_up_to k) (Fib (k + 1))

#eval Fib_up_to 10  -- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]

/- ### Higher functions -/

def f (n : Int) (m : Int) : Int := n * m ^ 2 - n * m + 3

#check f                            -- f (n m : Int) : Int
#check @f                           -- f : Int → Int → Int
#check f 2                          -- f 2 : Int → Int
#check f 2 (-3)                     -- f 2 (-3) : Int
#eval  f 2 (-3)                     -- 27

example : f 2 = fun (m : Int) => 2 * m ^ 2 - 2 * m + 3 := by rfl

example (m : Int) : f 2 m = 2 * m ^ 2 - 2 * m + 3 := by rfl

def const_fun {X Y : Type} (y : Y) : X → Y := fun (_ : X) => y

#check @const_fun  -- @const_fun : {X Y : Type} → Y → X → Y

/- ### Currying and composition of functions -/

def u : Int → Int → Int → Int :=
fun x1 x2 x3 => x1 + x2 ^ 2 + x1 * x3 - x3 ^ 3

#check u 2          -- u 2 : Int → Int → Int
#check u 2 (-1)     -- u 2 (-1) : Int → Int
#check u 2 (-1) 3   -- u 2 (-1) 3 : Int

example : u 2 (-1)   = (u 2) (-1)   := by rfl  -- No goals
example : u 2 (-1) 3 = (u 2) (-1) 3 := by rfl  -- No goals

/- ## Inductive types -/

/- ### Products -/

structure Prod (X Y : Type) : Type :=
mk :: (fst : X) (snd : Y)
deriving Repr

#check @Prod     -- Prod : Type → Type → Type
#check @Prod.mk  -- @Prod.mk : {X Y : Type} → X → Y → Prod X Y

#check Nat             -- Nat : Type
#check Int             -- Int: Type
#check Prod Nat Int    -- Prod Nat Int : Type
#check  1              --  1 : Nat
#check -1              -- -1 : Int
#check Prod.mk 1 (-1)  -- { fst := 1, snd := -1 } : Prod Nat Int

#check (⟨1, -1⟩ : Prod Nat Int)
-- { fst := 1, snd := -1 } : Prod Nat Int

def pair := Prod.mk 1 (-1)

#check pair      -- Tutorial.pair : Prod Nat Int
#check pair.1    -- pair.fst : Nat
#check pair.2    -- pair.snd : Int
#check pair.fst  -- pair.fst : Nat
#check pair.snd  -- pair.snd : Int

#eval pair      --  { fst := 1, snd := -1 }
#eval pair.fst  --  1
#eval pair.snd  -- -1

#check @Prod.fst       -- @Prod.snd : {X Y : Type} → Prod X Y → X
#check Prod.fst pair   -- pair.fst
#eval  Prod.fst pair   -- 1
#eval  pair.fst        -- 1

def v (t : Prod Int Int) : Int := t.fst + t.snd

#check @v         -- v : Int × Int → Int
#eval  v ⟨1, -2⟩  -- -1

def F : Int → Int → Int := fun n => fun m => n + m

example (n m : Int) : v ⟨n, m⟩ = F n m := by rfl  -- No goals

def G : Int → Int → Int := fun n m => n + m

theorem F_equal_G : F = G := by rfl

/- ### Sums -/

inductive Sum (X Y : Type) : Type :=
| from_left (x : X) : Sum X Y
| from_right (y : Y) : Sum X Y
deriving Repr

#check @Sum            -- Sum : Type → Type → Type
#check Sum.from_left   -- Sum.from_left {X Y : Type} (x : X) : Sum X Y
#check Sum.from_right  -- Sum.from_right {X Y : Type} (y : Y) : Sum X Y

#check Sum.from_left (X := Nat) (Y := String) 37           -- Sum.from_left 37 : Sum Nat String
#check Sum.from_right (X := Nat) (Y := String) "a string"  -- Sum.from_right "a string" : Sum Nat String

def g (t : Sum Int Int) : Int := match t with
| Sum.from_left  n => (-2) * n
| Sum.from_right n =>   n  - 1

#check @g  -- g : Sum Int Int → Int

#check g (Sum.from_left 37)   --   g (Sum.from_left 3) : Int
#eval  g (Sum.from_left 37)   -- -74
#check g (Sum.from_right 37)  --  g (Sum.from_right 3) : Int
#eval  g (Sum.from_right 37)  -- 36

/- ## Propositions-as-types and proofs-as-programs -/

def modus_ponens {P Q : Prop} (f : P → Q) (p : P) : Q := f p

/- ### Conjunction -/

structure And (P Q : Prop) : Prop :=
intro :: (left : P) (right : Q)

def mp (P Q : Prop) : (P → Q) → P → Q :=
fun f p => f p

inductive Or (P Q : Prop) : Prop :=
| from_left (p : P) : Or P Q
| from_right (y : Q) : Or P Q

theorem tauto1 (P Q : Prop) : P → Or P Q := Or.from_left

theorem tauto2 (P Q : Prop) : Q → Or P Q := Or.from_right

theorem symmOr (P Q : Prop) : Or P Q → Or Q P :=
fun t => match t with
| Or.from_left p => Or.from_right p
| Or.from_right q => Or.from_left q

/- ### Falsity and negation -/

def ExFalsoQuodLibet (P : Prop) : False → P :=
fun (p : False) => nomatch p

theorem tauto3 (P : Prop) : ¬P ∧ P → False :=
fun ⟨f, p⟩ => modus_ponens f p

/- ### Equivalence -/

structure Iff (P Q : Prop) : Prop :=
intro :: (imp : P → Q) (conv : Q → P)

theorem BasicEquivalence : Iff (¬¬False) False :=
Iff.intro imp conv where
imp : ¬¬False → False := fun (f : ¬False → False) => f id
conv : False → ¬¬False := (ExFalsoQuodLibet ¬¬False)

end Tutorial