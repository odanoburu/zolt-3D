#check Prod

namespace ZpInd

structure P : Type

inductive S : Type where
| s₁ : (n : P) → (m : P) → n ≠ m → S
| s₂ : (p : S)
     → (q : S)
     -- -- ¬ Colinear p q → (p ∩ q : P)
     -- → ∃ x : P, (x ∈ p ∧ x ∈ q ∧ ¬ (∃ y : P, y ≠ x ∧ y ∈ p ∧ y ∈ q))
     -- -- → ¬ (∃ x, ∃ y, x ∈ p ∧ x ∈ q ∧ y ∈ p ∧ y ∈ q ∧ x ≠ y)
     → S

inductive F : Type where
| f₁ : (p : S)
     → (q : S)
     -- → Jordan(p∪q)
     → F
| f₂ : (p : F)
     → (q : F)
     -- → p ∩ q : F
     → F

inductive V : Type where
| v₁ : (p : F)
     → (q : F)
     -- Closed(p∪q)
     → V
| v₂ : (p : V)
     → (q : V)
     -- → (p ∩ q)
     → V

-- inductive le : Nat → Nat → Prop
-- | refl : ∀ {m}, le m m
-- | step : ∀ {m n}, le m n → le m (succ n)
-- inductive Nat.le (n : Nat) : Nat → Prop
--   /-- Less-equal is reflexive: `n ≤ n` -/
--   | refl     : Nat.le n n
--   /-- If `n ≤ m`, then `n ≤ m + 1`. -/
--   | step {m} : Nat.le n m → Nat.le n (succ m)

end ZpInd
