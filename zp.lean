section sandbox
-- variable (R : α → α → Prop)
-- /-- `pairwise R l` means that all the elements with earlier indexes are
--   `R`-related to all the elements with later indexes.
--      pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
--   For example if `R = (≠)` then it asserts `l` has no duplicates,
--   and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
-- inductive pairwise : List α → Prop
-- | nil : pairwise []
-- | cons : ∀ {a : α} {l : List α}, (a' ∈ l → R a a') → pairwise l → pairwise (a :: l)

inductive AccTree : Nat → Type where
| leaf : (n : Nat) → AccTree n
| node : AccTree n → AccTree m → AccTree (Nat.add n m)

def notLeaf : AccTree x → Bool
| AccTree.leaf _ => False
| AccTree.node _ _ => True

def Nat.nonZero : Nat → Prop
| 0 => False
| _ => True

instance : DecidablePred Nat.nonZero := --by intro x; unfold Nat.nonZero; cases _
  λ n => match n with
  | Nat.zero => isFalse (λ hnz => by trivial)
  | Nat.succ _ => isTrue trivial

--theorem Nat.predminus {n : Nat} : nonZero n → pred n = n - 1 := sorry

def Nat.n := 1
--def Nat.nNonZero : nonZero n := _
-- #check True
-- #eval Nat.predminus (n := 1) (Nat.nonZero 1)

-- theorem Nat.smth {m n : Nat} (nzn : nonZero n) : m + n ≠ m :=
--   match n with
--   | 0 => False.elim nzn
--   | n + 1 => _

-- def leftTree : (t : AccTree n + m) → notLeaf t = True  → AccTree n
-- | AccTree.leaf l, notLeaf => _
-- | AccTree.node l r, _ => l

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

structure Segment (p1 p2 : Point) : Type where
  p1 : Point
  p2 : Point
  neq : p1 ≠ p2

def Segment.invert : Segment p₁ p₂ → Segment p₂ p₁
| s => {p1 := s.p2, p2 := s.p1, neq := s.neq}

theorem Segment.invert_symm {s : Segment p q}
  : invert (invert s) = s
  := rfl

theorem segment_comm : Segment p1 p2 → Segment p2 p1
  | {p1, p2, neq} => { p1 := p2, p2 := p1, neq := neq}

opaque NotCollinear : Segment p q → Segment r s → Prop

axiom NotCollinear_comm {p₁ q₁ p₂ q₂ : Point} {s₁ : Segment p₁ q₁} {s₂ : Segment p₂ q₂}
  : NotCollinear s₁ s₂ → NotCollinear s₂ s₁

opaque HasPointIntersection : Segment p q → Segment r s → Prop

axiom HasPointIntersection_comm : ∀ {p₁ q₁ p₂ q₂ : Point} {s₁ : Segment p₁ q₁} {s₂ : Segment p₂ q₂}
  , HasPointIntersection s₁ s₂ → HasPointIntersection s₂ s₁

inductive SegmentInfo : Type where
| single : (s : Segment r s) → SegmentInfo
| composite : SegmentInfo → SegmentInfo → SegmentInfo

def SegmentInfo.invert : SegmentInfo → SegmentInfo
| SegmentInfo.single s => SegmentInfo.single s
| SegmentInfo.composite s1 s2 => SegmentInfo.composite s2 s1

def SegmentInfo.left : SegmentInfo → SegmentInfo
| SegmentInfo.single si => SegmentInfo.single si
| SegmentInfo.composite si _ => si

def SegmentInfo.right : SegmentInfo → SegmentInfo
| SegmentInfo.single si => SegmentInfo.single si
| SegmentInfo.composite _ si => si

def segmentTip : SegmentInfo → Segment r s
| SegmentInfo.single s => s
| SegmentInfo.composite _ si => segmentTip si

-- inductive SegmentInfo.IsComposite : SegmentInfo → Prop
-- | compound (si₁ si₂ : SegmentInfo) : SegmentInfo.IsComposite (SegmentInfo.composite si₁ si₂)

-- instance : DecidablePred SegmentInfo.IsComposite :=
--   λ si => isTrue (match si with
--                  | SegmentInfo.composite si₁ si₂ => SegmentInfo.IsComposite.compound si₁ si₂)


-- NOTE: I have already pointed this out, but do we really need
-- NotCollinear? HasPointIntersection seems like it's enough for me…
inductive PolySegment : SegmentInfo → Type where
| s₁ : (s : Segment _ _) → PolySegment (SegmentInfo.single s)
| s₂ : PolySegment si₁
     → PolySegment si₂
     → NotCollinear (segmentTip si₁) (segmentTip si₂)
     → HasPointIntersection (segmentTip si₁) (segmentTip si₂)
     → PolySegment (SegmentInfo.composite si₁ si₂)

def PolySegment.components
: PolySegment si
→ Option (PolySegment (SegmentInfo.left si)
         × PolySegment (SegmentInfo.right si))
| PolySegment.s₁ __ => none
| PolySegment.s₂ ps₁ ps₂ _ _ => some (ps₁, ps₂)

def PolySegment.left
: PolySegment si
→ PolySegment (SegmentInfo.left si)
| PolySegment.s₂ ps _ _ _ => ps

def PolySegment.right
: PolySegment si
→ PolySegment (SegmentInfo.right si)
| PolySegment.s₂ _ ps _ _ => ps

def PolySegment.invert {si : SegmentInfo} : PolySegment si → PolySegment (SegmentInfo.invert si)
| PolySegment.s₁ s => PolySegment.s₁ s
| PolySegment.s₂ ps₁ ps₂ notColl hasPointInter
  => PolySegment.s₂ ps₂ ps₁ (NotCollinear_comm notColl) (HasPointIntersection_comm hasPointInter)

@[simp] theorem SegmentInfo.invert_symm : invert (invert si) = si
  := match si with
  | single _ => rfl
  | composite _ _ => rfl

-- theorem PolySegment.invert_symm {ps : PolySegment si}
--   : @Eq.subst _ PolySegment _ _ SegmentInfo.invert_symm (invert (invert ps)) = ps
--   := rfl

opaque IsJordan : PolySegment si₁ → PolySegment si₂ → Prop

axiom IsJordan_comm
  : ∀ {si₁ : SegmentInfo} {si₂ : SegmentInfo}
      {ps₁ : PolySegment si₁} {ps₂ : PolySegment si₂}
  , IsJordan ps₁ ps₂ → IsJordan ps₂ ps₁

-- couldn't a face just be a single polysegment that is a jordan
-- curve?
structure Face : Type where
  s1 : PolySegment si₁
  s2 : PolySegment si₂
  jordan : @IsJordan si₁ si₂ s1 s2

opaque HasLineIntersection : Face → Face → Prop

axiom HasLineIntersection_comm {f g : Face} :
  HasLineIntersection f g → HasLineIntersection g f

inductive FaceInfo where
| single : Face → FaceInfo
| composite : FaceInfo → FaceInfo → FaceInfo

def FaceInfo.left : FaceInfo → FaceInfo
| single f => single f
| composite fi _ => fi

def FaceInfo.right : FaceInfo → FaceInfo
| single f => single f
| composite _ fi => fi

def FaceInfo.tip : FaceInfo → Face
| FaceInfo.single f => f
| FaceInfo.composite _ f => FaceInfo.tip f

inductive PolyFace : FaceInfo → Type where
| f₁ : (f : Face) → PolyFace (FaceInfo.single f)
| f₂ : (pf : PolyFace fi₁)
     → (pg : PolyFace fi₂)
     → HasLineIntersection (FaceInfo.tip fi₁) (FaceInfo.tip fi₂)
     → PolyFace (FaceInfo.composite fi₁ fi₂)

def PolyFace.left
: PolyFace fi
→ PolyFace (FaceInfo.left fi)
| f₁ f => f₁ f
| PolyFace.f₂ ps _ _ => ps

def PolyFace.right
: PolyFace fi
→ PolyFace (FaceInfo.right fi)
| f₁ f => f₁ f
| PolyFace.f₂ _ ps _ => ps

-- theorem polyface_comm : PolyFace fi → PolyFace g f
--   | PolyFace.f₁ f => PolyFace.f₁ f
--   | PolyFace.f₂ pf₁ pf₂ lineInter
--     => PolyFace.f₂ pf₂ pf₁ (HasLineIntersection_comm lineInter)

opaque IsClosed : PolyFace fi → PolyFace gi → Prop

axiom IsClosed_comm {fi₁ fi₂ : FaceInfo}
  {pf₁ : PolyFace fi₁} {pf₂ : PolyFace fi₂}
  : IsClosed pf₁ pf₂  →  IsClosed pf₂ pf₁

structure Volume : Type where
  vol1 : PolyFace fi₁
  vol2 : PolyFace fi₂
  closed : @IsClosed fi₁ fi₂ vol1 vol2

-- inductive VolumeInfo where
-- | single : Volume → VolumeInfo
-- | composite : VolumeInfo → VolumeInfo → VolumeInfo

-- def VolumeInfo.left : VolumeInfo → VolumeInfo
-- | single v => single v
-- | composite vi _ => vi

-- def VolumeInfo.right : VolumeInfo → VolumeInfo
-- | single v => single v
-- | composite _ vi => vi

-- def VolumeInfo.tip : VolumeInfo → Volume
-- | single v => v
-- | composite _ vi => tip vi

inductive PolyVolume where
| v₁ : (v : Volume) → PolyVolume
| v₂ : (pv pw : PolyVolume)
     → PolyVolume

opaque HasFaceIntersection : PolyVolume → PolyVolume → Prop

axiom HasFaceIntersection_comm {v u : PolyVolume} :
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
| v₂ v u, v₂ w x => (v = w ∧ IsTruncationOf u x)
                 ∨ (u = x ∧ IsTruncationOf v w)

instance : Zₚ PolyVolume where
  cmp := HasFaceIntersection
  Composite := PolyVolume.IsComposite
  left := PolyVolume.left'
  right := PolyVolume.right'
  join := PolyVolume.join

--opaque PolyVolume.WellFormed : PolyVolume → Prop

-- def PolyVolume.left
-- : PolyVolume
-- → PolyVolume
-- | v₁ v => v₁ v
-- | PolyVolume.v₂ pv _ => pv

-- def PolyVolume.right
-- : PolyVolume
-- → PolyVolume
-- | v₁ v => v₁ v
-- | PolyVolume.v₂ _ pv => pv

-- axiom PolyVolume.WellFormed_left {pv : PolyVolume}
--   : WellFormed pv → WellFormed (left pv)
-- axiom PolyVolume.WellFormed_right {pv : PolyVolume}
--   : WellFormed pv → WellFormed (right pv)

-- theorem polyvolume_comm : PolyVolume v u → PolyVolume u v
--   | PolyVolume.v₁ v => PolyVolume.v₁ v
--   | PolyVolume.v₂ pv₁ pv₂ faceInter
--     => PolyVolume.v₂ pv₂ pv₁ (HasFaceIntersection_comm faceInter)

inductive T : Type where
| ε : T
| P : Point → T
| S : PolySegment _ → T
| F : PolyFace _ → T
| V : PolyVolume → T
| join : T → T → T

-- inductive cmp : T → T → Prop
-- | cmp₀
--   : (s : Segment _ _) → cmp (T.P s.p1) (T.P s.p2)
-- | cmp₁
--   : (ps : PolySegment si)
--   → cmp (T.S (PolySegment.left ps)) (T.S (PolySegment.right ps))
-- | cmp₂
--   : (pf : PolyFace fi)
--   → cmp (T.F <| PolyFace.left pf) (T.F <| PolyFace.right pf)
-- | cmp₃
--   : (wfpv : PolyVolume.WellFormed pv)
--   → cmp (T.V <| PolyVolume.WellFormed_left wfpv) (T.V <| PolyVolume.WellFormed_right wfpv)
-- open cmp

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
