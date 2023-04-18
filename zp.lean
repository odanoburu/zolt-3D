namespace ZpInd

class Zₚ (a : Type u) where
  ε : a
  cmp : a → a → Prop
  NonEmpty : a → Prop
  Composite : a → Prop
  left : a → a
  right : a → a
  join : (p : a) → (q : a) → cmp p q → a

opaque Zₚ.WellFormed [Zₚ t] : t → Prop

axiom Zₚ.WellFormed_left {t} [Zₚ t] {a : t} : WellFormed a → WellFormed (left a)
axiom Zₚ.WellFormed_right {t} [Zₚ t] {a : t} : WellFormed a → WellFormed (right a)
axiom Zₚ.WellFormed_join {t} [Zₚ t] {a : t} : WellFormed a → Composite a → cmp (left a) (right a)

axiom Zₚ.left_join {t} [Zₚ t] {p q : t} {cpq : cmp p q}
  : left (join p q cpq) = p
axiom Zₚ.right_join {t} [Zₚ t] {p q : t} {cpq : cmp p q}
  : right (join p q cpq) = q

axiom Zₚ.empty_left_join {t} [Zₚ t] {p : t} {εp : cmp ε p} : join ε p εp = p
axiom Zₚ.empty_right_join {t} [Zₚ t] {p : t} {pε : cmp p ε} : join p ε pε = p

structure Point : Type

structure Segment : Type where
  p1 : Point
  p2 : Point
  neq : p1 ≠ p2

-- def Segment.invert : Segment → Segment
-- | s => {p1 := s.p2, p2 := s.p1, neq := s.neq}

-- theorem Segment.invert_symm {s : Segment}
--   : invert (invert s) = s
--   := rfl

inductive PolySegment : Type where
| s₀ : PolySegment
| s₁ : Segment → PolySegment
| s₂ : (s₁ s₂ : PolySegment)
     → PolySegment

opaque NotCollinear : PolySegment → PolySegment → Prop

axiom NotCollinear_comm {ps₁ ps₂ : PolySegment}
  : NotCollinear ps₁ ps₂ → NotCollinear ps₂ ps₁

opaque PolySegment.HasPointIntersection : PolySegment → PolySegment → Prop

-- axiom PolySegment.HasPointIntersection_comm : ∀ {ps₁ ps₂ : PolySegment}
--   , HasPointIntersection ps₁ ps₂ → HasPointIntersection ps₂ ps₁

def PolySegment.left : PolySegment → PolySegment
| s₀ => s₀
| s₁ ps => s₁ ps
| s₂ ps _ => ps

def PolySegment.right : PolySegment → PolySegment
| s₀ => s₀
| s₁ ps => s₁ ps
| s₂ _ ps => ps

def PolySegment.NonEmpty : PolySegment → Prop
| s₀ => False
| s₁ _ => True
| s₂ _ _ => True

def PolySegment.IsComposite : PolySegment → Prop
| s₀ => False
| s₁ _ => False
| s₂ _ _ => True

-- def PolySegment.invert : PolySegment → PolySegment
-- | s₀ => s₀
-- | PolySegment.s₁ s => PolySegment.s₁ s
-- | PolySegment.s₂ ps₁ ps₂ => PolySegment.s₂ ps₂ ps₁

def PolySegment.cmp : PolySegment → PolySegment → Prop
| ps₁, ps₂ => NotCollinear ps₁ ps₂ ∧ HasPointIntersection ps₁ ps₂

def PolySegment.join : (p v : PolySegment) → PolySegment.cmp p v
  → PolySegment
| ps₁, ps₂, _ => s₂ ps₁ ps₂

instance : Zₚ PolySegment where
  ε := PolySegment.s₀
  cmp := PolySegment.cmp
  NonEmpty := PolySegment.NonEmpty
  Composite := PolySegment.IsComposite
  left := PolySegment.left
  right := PolySegment.right
  join := PolySegment.join

opaque IsJordan : PolySegment → PolySegment → Prop

-- axiom IsJordan_comm
--   : ∀ {ps₁ ps₂ : PolySegment}
--   , IsJordan ps₁ ps₂ → IsJordan ps₂ ps₁

-- couldn't a face just be a single polysegment that is a jordan
-- curve?
structure Face : Type where
  s1 : PolySegment
  s2 : PolySegment
  jordan : IsJordan s1 s2

inductive PolyFace : Type where
| f₀ : PolyFace
| f₁ : (f : Face) → PolyFace
| f₂ : (pf pg : PolyFace) → PolyFace

opaque HasLineIntersection : PolyFace → PolyFace → Prop

axiom HasLineIntersection_comm {f g : PolyFace} :
  HasLineIntersection f g → HasLineIntersection g f

def PolyFace.left : PolyFace → PolyFace
| f₀ => f₀
| f₁ f => f₁ f
| PolyFace.f₂ ps _ => ps

def PolyFace.right : PolyFace → PolyFace
| f₀ => f₀
| f₁ f => f₁ f
| PolyFace.f₂ _ ps => ps

opaque IsClosed : PolyFace → PolyFace → Prop

axiom IsClosed_comm {pf₁ pf₂ : PolyFace}
  : IsClosed pf₁ pf₂  →  IsClosed pf₂ pf₁

structure Volume : Type where
  vol1 : PolyFace
  vol2 : PolyFace
  closed : IsClosed vol1 vol2

inductive PolyVolume where
| v₀ : PolyVolume
| v₁ : (v : Volume) → PolyVolume
| v₂ : (pv pw : PolyVolume) → PolyVolume

opaque PolyVolume.HasFaceIntersection : PolyVolume → PolyVolume → Prop

axiom PolyVolume.EmptyAlwaysHasFaceIntersection {v : PolyVolume} :
  HasFaceIntersection v₀ v

axiom PolyVolume.HasFaceIntersection_comm {v u : PolyVolume} :
  HasFaceIntersection v u → HasFaceIntersection u v

def PolyVolume.IsComposite : PolyVolume → Prop
| v₀ => False
| v₁ _ => False
| v₂ _ _ => True

def PolyVolume.NonEmpty : PolyVolume → Prop
| v₀ => False
| v₁ _ => True
| v₂ _ _ => True

-- instance : DecidablePred PolyVolume.IsComposite := λ v =>
--   match v with
--   | PolyVolume.v₀ => isFalse (λ hc => by trivial)
--   | PolyVolume.v₁ u => isFalse (λ hc => by trivial)
--   | PolyVolume.v₂ _ _ => isTrue trivial

-- def PolyVolume.left {pv : PolyVolume} (_ : IsComposite pv) : PolyVolume
--   := match pv with
--   | v₂ pv₁ _ => pv₁

def PolyVolume.left' : PolyVolume → PolyVolume
| v₀ => v₀
| v₁ v => v₁ v
| v₂ v _ => v

-- def PolyVolume.right {pv : PolyVolume} (_ : IsComposite pv) : PolyVolume
--   := match pv with
--   | v₂ _ pv₁ => pv₁

def PolyVolume.right' : PolyVolume → PolyVolume
| v₀ => v₀
| v₁ v => v₁ v
| v₂ _ v => v

def PolyVolume.join : (p v : PolyVolume) → HasFaceIntersection p v
  → PolyVolume
| p, v, _ => v₂ p v

instance : Zₚ PolyVolume where
  ε := PolyVolume.v₀
  cmp := PolyVolume.HasFaceIntersection
  NonEmpty := PolyVolume.NonEmpty
  Composite := PolyVolume.IsComposite
  left := PolyVolume.left'
  right := PolyVolume.right'
  join := PolyVolume.join

section Truncation
variable {t} [Zₚ t]

inductive Zₚ.TruncationOf : t → t → Prop where
| t₀ {p : t} : NonEmpty p → TruncationOf ε p
| t₁ {r : t} : (pr : cmp p r) → (qr : cmp q r) → TruncationOf p q → TruncationOf (join p r pr) (join q r qr)

end Truncation

mutual
variable {t} [Zₚ t]
inductive Zₚ.le : t → t → Prop where
| refl {p : t} : le p p
| le₁ : ∀ {p₁ q₁ p₂ q₂ : t}, le p₁ q₁ → le p₂ q₂
      → (pc : cmp p₁ p₂) → (qc : cmp q₁ q₂)
      → le (join p₁ p₂ pc) (join q₁ q₂ qc)

inductive Zₚ.lt : t → t → Prop
| ε₁ : ∀ {p q : t}, (pqc : cmp p q) → lt p (join p q pqc)
| ε₂ : ∀ {p q : t}, (pqc : cmp p q) → lt q (join p q pqc)
| lt₁ : ∀ {p₁ q₁ p₂ q₂ : t}, lt p₁ q₁ → le p₂ q₂
      → (pc : cmp p₁ p₂) → (qc : cmp q₁ q₂)
      → lt (join p₁ p₂ pc) (join q₁ q₂ qc)
| lt₂ : ∀ {p₁ q₁ p₂ q₂ : t}, le p₁ q₁ → lt p₂ q₂
      → (pc : cmp p₁ p₂) → (qc : cmp q₁ q₂)
      → lt (join p₁ p₂ pc) (join q₁ q₂ qc)
end

theorem PolyVolume.zolt {q p : PolyVolume}
  (isTrunc : Zₚ.TruncationOf q p)
  : Zₚ.lt q p :=
  match isTrunc with
  | Zₚ.TruncationOf.t₀ _ =>
      have pεcmp : Zₚ.cmp p v₀
        := HasFaceIntersection_comm EmptyAlwaysHasFaceIntersection
      (Eq.subst Zₚ.empty_right_join <| Zₚ.lt.ε₂ pεcmp)
  | Zₚ.TruncationOf.t₁ (p := w) (q := u) (r := r) wrcmp urcmp qIsTruncOfp =>
    have w_lt_u : Zₚ.lt w u := zolt qIsTruncOfp
    have r_le_r : Zₚ.le r r := Zₚ.le.refl
    Zₚ.lt.lt₁ w_lt_u r_le_r wrcmp urcmp

end ZpInd
