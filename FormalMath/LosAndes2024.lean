import Mathlib.Tactic.Cases
import Mathlib.Tactic.Use

def Nat.isEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

theorem Coloquio2024 : ∀ (n m : Nat),
  n.isEven ∨ m.isEven → (n * m).isEven
    := by {
      intro n m t
      cases' t with h1 h2
      · cases' h1 with k1 p1
        unfold isEven
        use (k1 * m)
        rw [p1, Nat.mul_assoc]
      · cases' h2 with k2 p2
        unfold isEven
        use (n * k2)
        rw [p2, ← Nat.mul_assoc, Nat.mul_comm n 2, Nat.mul_assoc]
    }

#print Coloquio2024
