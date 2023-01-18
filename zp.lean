#check Prod

namespace Zp

structure P : Type

structure S : Type where
  p1 : P
  p2 : P
  neq : p1 ≠ p2

-- inductive S : Type where
-- | s₁ : (n : P) → (m : P) → n ≠ m → S
-- | s₂ : (p : S)
--      → (q : S)
--      -- ¬ Colinear p q → (p ∩ q : P)
--      → ∃ x : P, (x ∈ p ∧ x ∈ q ∧ ¬ (∃ y : P, y ≠ x ∧ y ∈ p ∧ y ∈ q))
--      -- → ¬ (∃ x, ∃ y, x ∈ p ∧ x ∈ q ∧ y ∈ p ∧ y ∈ q ∧ x ≠ y)
--      → S

inductive F : Type where
| f₁ : (p : S)
     → (q : S)
     -- → Jordan(p∪q)
     → F
