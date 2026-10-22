import Spec.Basic
import Spec.Geometry.AffinePlane
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Geometry.AdmissibleModels` used by the headline statements. -/

noncomputable section
namespace ParabolicRectifiability
/-- An affine spatial `k`-plane at the recorded fixed time, with `k ≥ 1`.
The affine-plane rank condition also forces `k ≤ n`. -/
structure HorizontalModel (n k : ℕ) where
  positive : 1 ≤ k
  spatial : AffineSpatialPlane n k
  time : ℝ

/-- An affine spatial plane times all time, with parabolic dimension `k`.
Its spatial rank is recorded with `spatialRank + 2 = k` and the guard `2 ≤ k`. -/
structure VerticalModel (n k : ℕ) where
  spatialRank : ℕ
  two_le : 2 ≤ k
  rank_eq : spatialRank + 2 = k
  spatial : AffineSpatialPlane n spatialRank

/-- Tagged union of horizontal and vertical models of the same parabolic dimension. -/
abbrev AdmissibleModel (n k : ℕ) := HorizontalModel n k ⊕ VerticalModel n k

/-- Choice of horizontal, vertical or mixed planes in a fitting problem. -/
inductive FamilyKind where
  | horizontal | vertical | mixed
  deriving DecidableEq

/-- The actual type of fitting models for the selected family; unavailable
dimensions give an empty type rather than a fictitious zero-rank model. -/
def Models (n k : ℕ) : FamilyKind → Type
  | .horizontal => HorizontalModel n k
  | .vertical => VerticalModel n k
  | .mixed => AdmissibleModel n k

namespace HorizontalModel
variable {n k : ℕ}
def toSet (L : HorizontalModel n k) : Set (Space n) :=
  {z | z.1 ∈ L.spatial.toSet ∧ z.2.val = L.time}

end HorizontalModel
namespace VerticalModel
variable {n k : ℕ}
def toSet (L : VerticalModel n k) : Set (Space n) :=
  {z | z.1 ∈ L.spatial.toSet}

end VerticalModel
namespace AdmissibleModel
variable {n k : ℕ}
def toSet : AdmissibleModel n k → Set (Space n)
  | .inl L => L.toSet
  | .inr L => L.toSet

end AdmissibleModel
/-- The represented set, uniformly across the three family choices. -/
def modelSet {n k : ℕ} {T : FamilyKind} : Models n k T → Set (Space n) :=
  match T with
  | .horizontal => HorizontalModel.toSet
  | .vertical => VerticalModel.toSet
  | .mixed => AdmissibleModel.toSet

end ParabolicRectifiability
