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

theorem segment_comm : Segment p1 p2 → Segment p2 p1
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

inductive PolySegment : Segment p₁ q₁ → Segment p₂ q₂ → Type where
| s₁ : (s : Segment _ _) → PolySegment r r
| s₂ : (ps₁ : PolySegment t s) → (ps₂ : PolySegment u r) → NotCollinear s r → HasPointIntersection s r
     → PolySegment s r

theorem polysegment_comm : PolySegment s r → PolySegment r s
  | PolySegment.s₁ s => PolySegment.s₁ s
  | PolySegment.s₂ ps₁ ps₂ notcoll pointInter
    => PolySegment.s₂ ps₂ ps₁ (NotCollinear_comm notcoll) (HasPointIntersection_comm pointInter)


opaque IsJordan : PolySegment t s → PolySegment u r → Prop

axiom IsJordan_comm
  : ∀ {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : Point}
      {t : Segment p₁ q₁} {s : Segment p₂ q₂}
      {u : Segment p₃ q₃} {r : Segment p₄ q₄}
      {ps₁ : PolySegment t s} {ps₂ : PolySegment u r}
  , IsJordan ps₁ ps₂ → IsJordan ps₂ ps₁

-- couldn't a face just be a single polysegment that is a jordan
-- curve?
structure Face : Type where
  s1 : PolySegment t s
  s2 : PolySegment u r
  jordan : @IsJordan _ _ t _ _ s _ _ u _ _ r s1 s2

opaque HasLineIntersection : Face → Face → Prop

axiom HasLineIntersection_comm {f g : Face} :
  HasLineIntersection f g → HasLineIntersection g f

inductive PolyFace : Face → Face → Type where
| f₁ : (f : Face) → PolyFace f f
| f₂ : (pf : PolyFace h f)
     → (pg : PolyFace i g)
     → HasLineIntersection f g
     → PolyFace f g

theorem polyface_comm : PolyFace f g → PolyFace g f
  | PolyFace.f₁ f => PolyFace.f₁ f
  | PolyFace.f₂ pf₁ pf₂ lineInter
    => PolyFace.f₂ pf₂ pf₁ (HasLineIntersection_comm lineInter)

opaque IsClosed : PolyFace h f → PolyFace i g → Prop

axiom IsClosed_comm {h f i g : Face}
  {pf₁ : PolyFace h f} {pf₂ : PolyFace g i}
  : IsClosed pf₁ pf₂  →  IsClosed pf₂ pf₁

structure Volume : Type where
  vol1 : PolyFace h f
  vol2 : PolyFace i g
  closed : @IsClosed h f i g vol1 vol2

opaque HasFaceIntersection : Volume → Volume → Prop

axiom HasFaceIntersection_comm {v u : Volume} :
  HasFaceIntersection v u → HasFaceIntersection u v

inductive PolyVolume : Volume → Volume → Type where
| v₁ : (v : Volume) → PolyVolume v v
| v₂ : (pv : PolyVolume w v)
     → (pw : PolyVolume x u)
     → HasFaceIntersection v u
     → PolyVolume v u

theorem polyvolume_comm : PolyVolume v u → PolyVolume u v
  | PolyVolume.v₁ v => PolyVolume.v₁ v
  | PolyVolume.v₂ pv₁ pv₂ faceInter
    => PolyVolume.v₂ pv₂ pv₁ (HasFaceIntersection_comm faceInter)

-- inductive le : Nat → Nat → Prop
-- | refl : ∀ {m}, le m m
-- | step : ∀ {m n}, le m n → le m (succ n)
-- inductive Nat.le (n : Nat) : Nat → Prop
--   /-- Less-equal is reflexive: `n ≤ n` -/
--   | refl     : Nat.le n n
--   /-- If `n ≤ m`, then `n ≤ m + 1`. -/
--   | step {m} : Nat.le n m → Nat.le n (succ m)

end ZpInd
