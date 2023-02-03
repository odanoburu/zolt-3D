section sandbox
variable (R : α → α → Prop)
/-- `pairwise R l` means that all the elements with earlier indexes are
  `R`-related to all the elements with later indexes.
     pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
  For example if `R = (≠)` then it asserts `l` has no duplicates,
  and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
inductive pairwise : List α → Prop
| nil : pairwise []
| cons : ∀ {a : α} {l : List α}, (a' ∈ l → R a a') → pairwise l → pairwise (a :: l)

inductive AccTree : Nat → Type where
| leaf : (n : Nat) → AccTree n
| node : AccTree n → AccTree m → AccTree (Nat.add n m)

def notLeaf : AccTree x → Bool
| AccTree.leaf _ => False
| AccTree.node _ _ => True

def Nat.nonZero : Nat → Prop
| 0 => False
| _ => True

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
  cmp : a → Prop
  --WellFormed : a → Prop
  left {x : a} : cmp x → a
  right {x : a} : cmp x → a
  join : a → a → a

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

opaque HasFaceIntersection : Volume → Volume → Prop

axiom HasFaceIntersection_comm {v u : Volume} :
  HasFaceIntersection v u → HasFaceIntersection u v

inductive VolumeInfo where
| single : Volume → VolumeInfo
| composite : VolumeInfo → VolumeInfo → VolumeInfo

def VolumeInfo.left : VolumeInfo → VolumeInfo
| single v => single v
| composite vi _ => vi

def VolumeInfo.right : VolumeInfo → VolumeInfo
| single v => single v
| composite _ vi => vi

def VolumeInfo.tip : VolumeInfo → Volume
| single v => v
| composite _ vi => tip vi

inductive PolyVolume where
| v₁ : (v : Volume) → PolyVolume
| v₂ : (pv pw : PolyVolume)
     → PolyVolume

def PolyVolume.IsComposite : PolyVolume → Prop
| v₁ _ => False
| v₂ _ _ => True

def PolyVolume.left {pv : PolyVolume} (_ : IsComposite pv) : PolyVolume
  := match pv with
  | v₂ pv₁ _ => pv₁

def PolyVolume.right {pv : PolyVolume} (_ : IsComposite pv) : PolyVolume
  := match pv with
  | v₂ _ pv₁ => pv₁

def PolyVolume.cmp {pv : PolyVolume} {_ : IsComposite pv} (l r : PolyVolume) : Prop
  := v₂ l r = pv

instance : Zₚ PolyVolume where
  cmp := PolyVolume.IsComposite
  left := PolyVolume.left
  right := PolyVolume.right
  join := PolyVolume.v₂

opaque PolyVolume.WellFormed : PolyVolume → Prop

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

-- def PolyVolume.IsTruncationOf {pv₁ pv₂ : PolyVolume} (wf₁ : WellFormed pv₁) (wf₂ : WellFormed pv₂) : Prop
--   := match pv₁ with
--      | v₁ _ => False
--      | v₂ v u =>
--        match pv₂ with
--        | v₁ w => v = v₁ w ∨ u = v₁ w
--        | v₂ w _ => v = w ∧ IsTruncationOf (WellFormed_right wf₁) (WellFormed_right wf₂)

-- theorem polyvolume_comm : PolyVolume v u → PolyVolume u v
--   | PolyVolume.v₁ v => PolyVolume.v₁ v
--   | PolyVolume.v₂ pv₁ pv₂ faceInter
--     => PolyVolume.v₂ pv₂ pv₁ (HasFaceIntersection_comm faceInter)

inductive T : Type where
| ε : T
| P : Point → T
| S : PolySegment _ → T
| F : PolyFace _ → T
| V : PolyVolume.WellFormed pv → T
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
inductive le : t → t → Prop where
| ε₀ {p : t} : le p p
| le₁ : ∀ {p₁ q₁ p₂ q₂ : t}, le p₁ q₁ → le p₂ q₂
      → le (Zₚ.join p₁ p₂) (Zₚ.join q₁ q₂)

inductive lt : t → t → Prop
| ε₁ : ∀ {o : t}, (co : Zₚ.cmp o) → lt (Zₚ.left co) o
| ε₂ : ∀ {c : t}, (co : Zₚ.cmp c) → lt (Zₚ.right co) c
| lt₁ : ∀ {p₁ q₁ p₂ q₂ : t}, lt p₁ q₁ → le p₂ q₂
      → lt (Zₚ.join p₁ p₂) (Zₚ.join q₁ q₂)
| lt₂ : ∀ {p₁ q₁ p₂ q₂ : t}, le p₁ q₁ → lt p₂ q₂
      → lt (Zₚ.join p₁ p₂) (Zₚ.join q₁ q₂)
end

-- theorem T.zolt {pv₁ pv₂ : PolyVolume}
--   (wf₁ : PolyVolume.WellFormed pv₁)
--   (wf₂ : PolyVolume.WellFormed pv₂)
--   (isTrunc : PolyVolume.IsTruncationOf wf₁ wf₂)
--   : lt (V wf₂) (V wf₁) :=
--   match pv₁ with
--   | PolyVolume.v₁ _ => False.elim isTrunc
--   | PolyVolume.v₂ _ _ =>
--     match pv₂ with
--     | PolyVolume.v₁ w =>
--       Or.elim isTrunc (λ h => lt.ε₂ _ _) _
--     | PolyVolume.v₂ w x => _


end ZpInd
