section sandbox

inductive AccTree : Nat → Type where
| leaf : (n : Nat) → AccTree n
| node : AccTree n → AccTree m → AccTree (Nat.add n m)

def notLeaf : AccTree x → Bool
| AccTree.leaf _ => False
| AccTree.node _ _ => True

def Nat.nonZero : Nat → Prop
| 0 => False
| _ => True

instance : DecidablePred Nat.nonZero :=
  λ n => match n with
  | Nat.zero => isFalse (λ hnz => by trivial)
  | Nat.succ _ => isTrue trivial

end sandbox

namespace ZpInd

class Zₚ (a : Type u) where
  cmp : a → a → Prop
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

structure Point : Type

structure Segment : Type where
  p1 : Point
  p2 : Point
  neq : p1 ≠ p2

def Segment.invert : Segment → Segment
| s => {p1 := s.p2, p2 := s.p1, neq := s.neq}

theorem Segment.invert_symm {s : Segment}
  : invert (invert s) = s
  := rfl

-- NOTE: I have already pointed this out, but do we really need
-- NotCollinear? HasPointIntersection seems like it's enough for me…
inductive PolySegment : Type where
| s₁ : Segment → PolySegment
| s₂ : (s₁ s₂ : PolySegment)
     → PolySegment

opaque NotCollinear : PolySegment → PolySegment → Prop

axiom NotCollinear_comm {ps₁ ps₂ : PolySegment}
  : NotCollinear ps₁ ps₂ → NotCollinear ps₂ ps₁

opaque PolySegment.HasPointIntersection : PolySegment → PolySegment → Prop

axiom PolySegment.HasPointIntersection_comm : ∀ {ps₁ ps₂ : PolySegment}
  , HasPointIntersection ps₁ ps₂ → HasPointIntersection ps₂ ps₁

-- def PolySegment.components
-- : PolySegment si
-- → Option (PolySegment (SegmentInfo.left si)
--          × PolySegment (SegmentInfo.right si))
-- | PolySegment.s₁ __ => none
-- | PolySegment.s₂ ps₁ ps₂ _ _ => some (ps₁, ps₂)

def PolySegment.left : PolySegment → PolySegment
| s₁ ps => s₁ ps
| s₂ ps _ => ps

def PolySegment.right : PolySegment → PolySegment
| s₁ ps => s₁ ps
| s₂ _ ps => ps

def PolySegment.IsComposite : PolySegment → Prop
| s₁ _ => False
| s₂ _ _ => True

def PolySegment.invert : PolySegment → PolySegment
| PolySegment.s₁ s => PolySegment.s₁ s
| PolySegment.s₂ ps₁ ps₂ => PolySegment.s₂ ps₂ ps₁

theorem PolySegment.invert_symm {ps : PolySegment}
  : invert (invert ps) = ps
  := _

def PolySegment.cmp : PolySegment → PolySegment → Prop
| ps₁, ps₂ => NotCollinear ps₁ ps₂ ∧ HasPointIntersection ps₁ ps₂

def PolySegment.join : (p v : PolySegment) → PolySegment.cmp p v
  → PolySegment
| ps₁, ps₂, _ => s₂ ps₁ ps₂

instance : Zₚ PolySegment where
  cmp := PolySegment.cmp
  Composite := PolySegment.IsComposite
  left := PolySegment.left
  right := PolySegment.right
  join := PolySegment.join

opaque IsJordan : PolySegment → PolySegment → Prop

axiom IsJordan_comm
  : ∀ {ps₁ ps₂ : PolySegment}
  , IsJordan ps₁ ps₂ → IsJordan ps₂ ps₁

-- couldn't a face just be a single polysegment that is a jordan
-- curve?
structure Face : Type where
  s1 : PolySegment
  s2 : PolySegment
  jordan : IsJordan s1 s2

inductive PolyFace : Type where
| f₁ : (f : Face) → PolyFace
| f₂ : (pf pg : PolyFace) → PolyFace

opaque HasLineIntersection : PolyFace → PolyFace → Prop

axiom HasLineIntersection_comm {f g : PolyFace} :
  HasLineIntersection f g → HasLineIntersection g f

def PolyFace.left : PolyFace → PolyFace
| f₁ f => f₁ f
| PolyFace.f₂ ps _ => ps

def PolyFace.right : PolyFace → PolyFace
| f₁ f => f₁ f
| PolyFace.f₂ _ ps => ps

-- theorem polyface_comm : PolyFace fi → PolyFace g f
--   | PolyFace.f₁ f => PolyFace.f₁ f
--   | PolyFace.f₂ pf₁ pf₂ lineInter
--     => PolyFace.f₂ pf₂ pf₁ (HasLineIntersection_comm lineInter)

opaque IsClosed : PolyFace → PolyFace → Prop

axiom IsClosed_comm {pf₁ pf₂ : PolyFace}
  : IsClosed pf₁ pf₂  →  IsClosed pf₂ pf₁

structure Volume : Type where
  vol1 : PolyFace
  vol2 : PolyFace
  closed : IsClosed vol1 vol2

inductive PolyVolume where
| v₁ : (v : Volume) → PolyVolume
| v₂ : (pv pw : PolyVolume) → PolyVolume

opaque PolyVolume.HasFaceIntersection : PolyVolume → PolyVolume → Prop

axiom PolyVolume.HasFaceIntersection_comm {v u : PolyVolume} :
  HasFaceIntersection v u → HasFaceIntersection u v

def PolyVolume.IsComposite : PolyVolume → Prop
| v₁ _ => False
| v₂ _ _ => True

instance : DecidablePred PolyVolume.IsComposite := λ v =>
  match v with
  | PolyVolume.v₁ u => isFalse (λ hc => by trivial)
  | PolyVolume.v₂ _ _ => isTrue trivial

def PolyVolume.left {pv : PolyVolume} (_ : IsComposite pv) : PolyVolume
  := match pv with
  | v₂ pv₁ _ => pv₁

def PolyVolume.left' : PolyVolume → PolyVolume
| v₁ v => v₁ v
| v₂ v _ => v

def PolyVolume.right {pv : PolyVolume} (_ : IsComposite pv) : PolyVolume
  := match pv with
  | v₂ _ pv₁ => pv₁

def PolyVolume.right' : PolyVolume → PolyVolume
| v₁ v => v₁ v
| v₂ _ v => v

def PolyVolume.join : (p v : PolyVolume) → HasFaceIntersection p v
  → PolyVolume
| p, v, _ => v₂ p v

def PolyVolume.IsTruncationOf : PolyVolume → PolyVolume → Prop
| v₁ _, _ => False
| v₂ v u, v₁ w => v = v₁ w ∨ u = v₁ w
-- xor??
| v₂ v u, v₂ w x => (v = w ∧ IsTruncationOf u x)
                 ∨ (u = x ∧ IsTruncationOf v w)

instance : Zₚ PolyVolume where
  cmp := PolyVolume.HasFaceIntersection
  Composite := PolyVolume.IsComposite
  left := PolyVolume.left'
  right := PolyVolume.right'
  join := PolyVolume.join

inductive T : Type where
| ε : T
| P : Point → T
| S : PolySegment → T
| F : PolyFace → T
| V : PolyVolume → T
| join : T → T → T


mutual
variable {t} [Zₚ t]
inductive Zₚ.le : t → t → Prop where
| ε₀ {p : t} : le p p
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

theorem PolyVolume.zolt {p q : PolyVolume} {wfp : Zₚ.WellFormed p} {wfq : Zₚ.WellFormed q}
  (isTrunc : IsTruncationOf p q)
  : Zₚ.lt q p :=
  match p with
  | v₁ _ => False.elim isTrunc
  | v₂ u v =>
    have uvC : Zₚ.Composite (v₂ u v) := trivial
    have uvc : Zₚ.cmp u v := Zₚ.WellFormed_join wfp uvC
    match q with
    | v₁ w =>
      Or.elim isTrunc
        (λ he : u = v₁ w =>
          have z : Zₚ.lt u (Zₚ.join u v uvc) := Zₚ.lt.ε₁ (p := u) uvc
          have z' : Zₚ.lt u (v₂ u v) := Eq.subst rfl z
          show Zₚ.lt (v₁ w) (v₂ u v) from Eq.subst (motive := λ α => Zₚ.lt α (v₂ u v)) he z')
        (λ he : v = v₁ w =>
           have z := Eq.subst rfl <| Zₚ.lt.ε₂ (q := v) uvc
           Eq.subst (motive := λ α => Zₚ.lt α (v₂ u v)) he z)
    | v₂ w x =>
      have wxC : Zₚ.Composite (v₂ w x) := trivial
      have wxc : Zₚ.cmp w x := Zₚ.WellFormed_join wfq wxC
      Or.elim isTrunc
        (λ h =>
          have hz :=
            zolt (wfp := Zₚ.WellFormed_right wfp)
                 (wfq := Zₚ.WellFormed_right wfq)
                 h.right
          have he : Zₚ.le w u := Eq.subst (Eq.symm h.left) Zₚ.le.ε₀
          Zₚ.lt.lt₂ he hz wxc uvc)
        (λ h =>
          have hz : Zₚ.lt w u :=
            zolt (wfp := Zₚ.WellFormed_left wfp)
                 (wfq := Zₚ.WellFormed_left wfq)
                 h.right
          have he : Zₚ.le x v := Eq.subst (Eq.symm h.left) Zₚ.le.ε₀
          Zₚ.lt.lt₁ hz he wxc uvc)

end ZpInd
