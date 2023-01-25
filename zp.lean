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

structure Segment (p1 p2 : Point) : Type where
  p1 : Point
  p2 : Point
  neq : p1 ≠ p2

theorem segment_comm : (s : Segment p1 p2) → Segment p2 p1
  | {p1, p2, neq} => { p1 := p2, p2 := p1, neq := neq}

opaque NotCollinear : Segment p q → Segment r s → Prop

axiom NotCollinear_comm {p₁ q₁ p₂ q₂ : Point} {s₁ : Segment p₁ q₁} {s₂ : Segment p₂ q₂}
  : NotCollinear s₁ s₂ → NotCollinear s₂ s₁

opaque HasPointIntersection : Segment p q → Segment r s → Prop

axiom HasPointIntersection_comm : ∀ {p₁ q₁ p₂ q₂ : Point} {s₁ : Segment p₁ q₁} {s₂ : Segment p₂ q₂}
  , HasPointIntersection s₁ s₂ → HasPointIntersection s₂ s₁

-- structure PolySegment : Type where
--   init : Segment × Segment
--   more : List Segment
--   joint : ∀ {s : Segment}, s ∈ (init.fst :: init.snd :: segments)
--         → ∃ r : Segment, r ∈ (init.fst :: init.snd :: segments)
--           → HasPointIntersection s r ∧ NonCollinear s r

inductive PolySegment : Segment p q → Type where
| s₁ : (s : Segment _ _) → (r : Segment _ _) → NotCollinear s r → HasPointIntersection s r → PolySegment r
| s₂ : (s : Segment _ _) → (ps : PolySegment r) → NotCollinear s r → HasPointIntersection s r → PolySegment s

-- theorem s₁_comm {s : Segment p₁ p₂ } {r : Segment q₁ q₂}
--   : (PolySegment.s₁ s r s_notcoll_r s_pointinter_r : PolySegment _) → PolySegment.s₁ r s _ _ := _
-- --   | {p1, p2, neq} => { p1 := p2, p2 := p1, neq := neq}


opaque IsJordan : PolySegment s → PolySegment r → Prop

-- couldn't a face just be a single polysegment that is
-- a jordan curve?
structure Face : Type where
  s1 : PolySegment s
  s2 : PolySegment r
  jordan : @IsJordan _ _ s _ _ r s1 s2

opaque HasLineIntersection : Face → Face → Prop

inductive PolyFace : Face → Type where
| f₁ : (f : Face)
     → (g : Face)
     → HasLineIntersection f q
     → PolyFace g
| f₂ : (pf : PolyFace f)
     → (pg : PolyFace g)
     → HasLineIntersection f g
     → PolyFace g

opaque IsClosed : PolyFace f → PolyFace g → Prop

structure Volume : Type where
  vol1 : PolyFace f
  vol2 : PolyFace g
  closed : @IsClosed f g vol1 vol2

opaque HasFaceIntersection : Volume → Volume → Prop

inductive PolyVolume : Volume → Type where
| v₁ : (p : Volume)
     → (q : Volume)
     → HasFaceIntersection p q
     → PolyVolume q
| v₂ : (pv : PolyVolume v)
     → (pw : PolyVolume w)
     → HasFaceIntersection v w
     → PolyVolume w

-- inductive le : Nat → Nat → Prop
-- | refl : ∀ {m}, le m m
-- | step : ∀ {m n}, le m n → le m (succ n)
-- inductive Nat.le (n : Nat) : Nat → Prop
--   /-- Less-equal is reflexive: `n ≤ n` -/
--   | refl     : Nat.le n n
--   /-- If `n ≤ m`, then `n ≤ m + 1`. -/
--   | step {m} : Nat.le n m → Nat.le n (succ m)

end ZpInd
