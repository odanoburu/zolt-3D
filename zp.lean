structure Point : Type

structure Segment : Type where
  p1 : Point
  p2 : Point
  neq : p1 ≠ p2

inductive PolySegment : Type where
| s₀ : PolySegment
| s₁ : Segment → PolySegment
| s₂ : PolySegment → PolySegment → PolySegment

opaque IsJordan : PolySegment → PolySegment → Prop

structure Face : Type where
  s1 : PolySegment
  s2 : PolySegment
  jordan : IsJordan s1 s2

inductive PolyFace : Type where
| f₀ : PolyFace
| f₁ : Face → PolyFace
| f₂ : PolyFace → PolyFace → PolyFace

opaque IsClosed : PolyFace → PolyFace → Prop

structure Volume : Type where
  vol1 : PolyFace
  vol2 : PolyFace
  closed : IsClosed vol1 vol2

inductive PolyVolume where
| v₀ : PolyVolume
| v₁ : Volume → PolyVolume
| v₂ : PolyVolume → PolyVolume → PolyVolume

opaque PolyVolume.HasFaceIntersection
  : PolyVolume → PolyVolume → Prop

axiom PolyVolume.EmptyAlwaysHasFaceIntersection {v : PolyVolume} :
  HasFaceIntersection v₀ v

axiom PolyVolume.HasFaceIntersection_comm {v u : PolyVolume} :
  HasFaceIntersection v u → HasFaceIntersection u v

def PolyVolume.NonEmpty : PolyVolume → Prop
| v₀ => False
| v₁ _ => True
| v₂ _ _ => True

class Zₚ (a : Type u) where
  ε : a
  cmp : a → a → Prop
  join : (p : a) → (q : a) → cmp p q → a
  NonEmpty : a → Prop

axiom Zₚ.empty_left_join {t} [Zₚ t] {p : t} {εp : cmp ε p} : join ε p εp = p
axiom Zₚ.empty_right_join {t} [Zₚ t] {p : t} {pε : cmp p ε} : join p ε pε = p

instance : Zₚ PolyVolume where
  ε := PolyVolume.v₀
  cmp := PolyVolume.HasFaceIntersection
  join := λ p v _cmp => PolyVolume.v₂ p v
  NonEmpty := PolyVolume.NonEmpty

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

section Truncation

  variable {t} [Zₚ t]

  inductive Zₚ.TruncationOf : t → t → Prop where
  | t₀ {p : t} : NonEmpty p → TruncationOf ε p
  | t₁ {p q r : t} : (pr : cmp p r) → (qr : cmp q r)
      → TruncationOf p q
      → TruncationOf (join p r pr) (join q r qr)

end Truncation

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
