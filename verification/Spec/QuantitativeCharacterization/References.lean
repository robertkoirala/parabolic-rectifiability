import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Support
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Foundations.HalfTimeDerivative
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.SubspaceCoordinates
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.QuantitativeCharacterization.References` used by the headline statements. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.QuantitativeCharacterization
open ParabolicRectifiability.Foundations
/-- The closed cube of side `λ 2^j` of the dyadic grid with origin `c` and scale `λ`:
`{x : c_α + λ 2^j m_α ≤ x_α ≤ c_α + λ 2^j (m_α + 1) for every coordinate α}`. Translating and
dilating the standard dyadic grid of `ℝ^k` gives exactly these cubes
(every translation and dilation of this construction). -/
def dyadicCube {k : ℕ} (origin : Spatial k) (scale : ℝ) (level : ℤ) (corner : Fin k → ℤ) :
    Set (Spatial k) :=
  {x | ∀ α : Fin k,
    origin α + scale * (2 : ℝ) ^ level * (corner α : ℝ) ≤ x α ∧
      x α ≤ origin α + scale * (2 : ℝ) ^ level * ((corner α : ℝ) + 1)}

/-- The distance `dist(Q,D) = inf_{x ∈ Q} dist(x,D)` from a set `Q` to a set `D`. It is used
only for nonempty cubes `Q` and the nonempty compact domain `D`, where it is the genuine
infimum of a nonempty set bounded below by zero. -/
def setDist {k : ℕ} (Q D : Set (Spatial k)) : ℝ :=
  ⨅ x : Q, Metric.infDist (x : Spatial k) D

/-- A horizontal `L`-reference with all of its data. The field `height` is the plateau function `T`; its
restriction to `domain` is the trace `τ`. Because the faces partition `domainᶜ`, `height`
is determined by `τ`, the anchors and the face assignment. -/
structure HorizontalReference (n k : ℕ) (L : ℝ) where
  /-- Horizontal availability `1 ≤ k ≤ n`. -/
  available : 1 ≤ k ∧ k ≤ n
  /-- The global spatial embedding `F : ℝ^k → ℝ^n`. -/
  spatialMap : Spatial k → Spatial n
  /-- `L⁻¹ |u - v| ≤ |F(u) - F(v)| ≤ L |u - v|` for all `u, v`. -/
  spatialMap_bilipschitz : ∀ u v : Spatial k,
    dist u v ≤ L * dist (spatialMap u) (spatialMap v) ∧
      dist (spatialMap u) (spatialMap v) ≤ L * dist u v
  /-- The compact trace domain `D`. -/
  domain : Set (Spatial k)
  domain_nonempty : domain.Nonempty
  domain_compact : IsCompact domain
  /-- The plateau time function `T`; `τ = T|_D`. -/
  height : Spatial k → ℝ
  /-- `|τ(u) - τ(v)| ≤ L² |u - v|²` on `D`. -/
  height_trace : ∀ u ∈ domain, ∀ v ∈ domain,
    |height u - height v| ≤ L ^ 2 * dist u v ^ 2
  /-- The origin and scale of the single translated and dilated dyadic grid. -/
  gridOrigin : Spatial k
  gridScale : ℝ
  gridScale_pos : 0 < gridScale
  /-- The Whitney cubes, indexed by a subset of the naturals. -/
  cubeIndex : Set ℕ
  cube : cubeIndex → Set (Spatial k)
  cubeLevel : cubeIndex → ℤ
  cubeCorner : cubeIndex → Fin k → ℤ
  cube_eq : ∀ i, cube i = dyadicCube gridOrigin gridScale (cubeLevel i) (cubeCorner i)
  /-- The closed cubes have disjoint interiors and cover `Dᶜ`. -/
  cube_interior_disjoint : ∀ i j, i ≠ j → Disjoint (interior (cube i)) (interior (cube j))
  cubes_cover : (⋃ i, cube i) = domainᶜ
  /-- The Whitney inequalities `4 diam Q ≤ dist(Q,D) ≤ 10 diam Q`. -/
  whitney_lower : ∀ i, 4 * Metric.diam (cube i) ≤ setDist (cube i) domain
  whitney_upper : ∀ i, setDist (cube i) domain ≤ 10 * Metric.diam (cube i)
  /-- Nearest anchors `a_Q ∈ D`, realizing the distance from the closed cube to `D`. -/
  anchor : cubeIndex → Spatial k
  anchor_mem : ∀ i, anchor i ∈ domain
  anchor_nearest : ∀ i, ∃ x ∈ cube i, dist x (anchor i) = setDist (cube i) domain
  /-- The Borel face assignment: the piece assigned to each cube contains its interior, lies
  in the closed cube, and the pieces partition `Dᶜ`. -/
  face : cubeIndex → Set (Spatial k)
  face_measurable : ∀ i, MeasurableSet (face i)
  interior_subset_face : ∀ i, interior (cube i) ⊆ face i
  face_subset_cube : ∀ i, face i ⊆ cube i
  face_disjoint : ∀ i j, i ≠ j → Disjoint (face i) (face j)
  faces_cover : (⋃ i, face i) = domainᶜ
  /-- `T = τ(a_Q)` on each assigned piece. -/
  height_plateau : ∀ i, ∀ x ∈ face i, height x = height (anchor i)

namespace HorizontalReference
variable {n k : ℕ} {L : ℝ}
/-- The map `(F,T) : ℝ^k → X`, `u ↦ (F(u), T(u))`. -/
def map (H : HorizontalReference n k L) (u : Spatial k) : Space n :=
  point (H.spatialMap u) (H.height u)

/-- The reference measure `σ = (F,T)_# L^k`, with `L^k` the Lebesgue measure of `ℝ^k`. -/
def measure (H : HorizontalReference n k L) : Measure (Space n) :=
  Measure.map H.map volume

/-- The closed carrier `Γ = supp σ`. It contains the limiting plateau heights at faces and
no filled-in vertical interval. -/
def carrier (H : HorizontalReference n k L) : Set (Space n) :=
  H.measure.support

end HorizontalReference
/-- A vertical `L`-reference:
a spatial rank `m` with `m + 2 = k < n + 2`, and `F : ℝ^m × ℝ → ℝ^n` such that
`Φ(u,t) = (F(u,t),t)` is `L`-bi-Lipschitz for the max parabolic metrics of `Space m` and `X`,
and every Euclidean coordinate of `F` has a pure-time half-derivative representative with
real parabolic BMO seminorm at most `L`. -/
structure VerticalReference (n k : ℕ) (L : ℝ) where
  spatialRank : ℕ
  rank_eq : spatialRank + 2 = k
  /-- Vertical references are nonambient; at `k = n + 2` only the ambient reference is used. -/
  lt_ambient : k < n + 2
  /-- The spatial component `F` of `Φ(u,t) = (F(u,t),t)`. -/
  spatialMap : Space spatialRank → Spatial n
  /-- `L⁻¹ d_P(p,q) ≤ d_P(Φ p, Φ q) ≤ L d_P(p,q)`; `Φ` preserves the time coordinate. -/
  bilipschitz : ∀ p q : Space spatialRank,
    dist p q ≤ L * dist ((spatialMap p, p.2) : Space n) (spatialMap q, q.2) ∧
      dist ((spatialMap p, p.2) : Space n) (spatialMap q, q.2) ≤ L * dist p q
  /-- `max_α [|D_t|^{1/2} F^α]_{BMO_P} ≤ L`, coordinatewise. -/
  coordinate_bmo : HasCoordinateHalfTimeBMOBound spatialRank n spatialMap L

namespace VerticalReference
variable {n k : ℕ} {L : ℝ}
/-- The time-preserving embedding `Φ(u,t) = (F(u,t),t)`. -/
def map (V : VerticalReference n k L) (p : Space V.spatialRank) : Space n :=
  (V.spatialMap p, p.2)

/-- The carrier `Γ = im Φ`. -/
def carrier (V : VerticalReference n k L) : Set (Space n) :=
  Set.range V.map

end VerticalReference
/-- A typed `L`-reference: horizontal, vertical, or the ambient reference `(X, L^{n+1})` at
`k = n + 2`. -/
inductive Reference (n k : ℕ) (L : ℝ) where
  | horizontal (H : HorizontalReference n k L)
  | vertical (V : VerticalReference n k L)
  | ambient (h : k = n + 2)

namespace Reference
variable {n k : ℕ} {L : ℝ}
/-- The type of a reference. The ambient reference is of vertical type. -/
def kind : Reference n k L → FamilyKind
  | horizontal _ => .horizontal
  | vertical _ => .vertical
  | ambient _ => .vertical

/-- The reference carrier `Γ`. -/
def carrier : Reference n k L → Set (Space n)
  | horizontal H => H.carrier
  | vertical V => V.carrier
  | ambient _ => Set.univ

end Reference
end ParabolicRectifiability.QuantitativeCharacterization
