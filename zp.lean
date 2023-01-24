#check set

section pairwise
variable (R : α → α → Prop)

/-- `pairwise R l` means that all the elements with earlier indexes are
  `R`-related to all the elements with later indexes.
     pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
  For example if `R = (≠)` then it asserts `l` has no duplicates,
  and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
inductive pairwise : List α → Prop
| nil : pairwise []
| cons : ∀ {a : α} {l : List α}, (a' ∈ l → R a a') → pairwise l → pairwise (a :: l)

end pairwise

namespace ZpInd

structure Point : Type

structure Segment : Type where
  p1 : Point
  p2 : Point
  neq : p1 ≠ p2

def segmentHasPointIntersection : Segment → Segment → Prop := sorry

-- something strange in the definition is that if weird s is a
-- polyline, then what's the definition of colinear for polylines?
-- and if it's just a regular line, then s₂ doesn't make much sense…
structure PolySegment : Type where
  init : Segment × Segment
  more : List Segment
  joint : ∀ {s : Segment}, s ∈ (init.fst :: init.snd :: segments) → r ∈ (init.fst :: init.snd :: segments) → segmentHasPointIntersection s r

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

namespace ZpAx



end ZpAx
