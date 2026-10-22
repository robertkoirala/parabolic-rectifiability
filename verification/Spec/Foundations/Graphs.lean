import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Foundations.HalfTimeDerivative
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.SubspaceCoordinates
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.Graphs` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace ParabolicRectifiability.Foundations
/-- A full general regular vertical graph `{(a + u + G(u,t), t) : (u,t) ∈ W × ℝ}` with
`dim W + 2 = k`. The normal-valued function has a parabolic Lipschitz
bound `L` and a homogeneous half-time derivative with vector parabolic BMO bound `B`,
with `L + B ≤ ε`; see `IsGeneralRegularVerticalFunction`.

The explicit guard `2 ≤ k` excludes a vertical type in dimension one; the rank equation
also forces `k ≤ n + 2`. Rank zero and full spatial rank are allowed. The domain is all
`W × ℝ`, with no compact-support or `L²` hypothesis. These are space-time graphs. -/
structure GeneralRegularVerticalGraph (n k : ℕ) (ε : ℝ) where
  vertical_dimension : 2 ≤ k
  direction : Submodule ℝ (Spatial n)
  rank_eq : Module.finrank ℝ direction + 2 = k
  offset : Spatial n
  function : SubspaceSpace direction → direction.orthogonal
  regular : IsGeneralRegularVerticalFunction direction function ε

namespace GeneralRegularVerticalGraph
variable {n k : ℕ} {ε : ℝ}
/-- The graph map `(u,t) ↦ (a + u + G(u,t), t)` on the whole base `W × ℝ`. -/
def map (G : GeneralRegularVerticalGraph n k ε) (p : SubspaceSpace G.direction) : Space n :=
  (G.offset + (p.1 : Spatial n) + (G.function p : Spatial n), p.2)

/-- The image of the full graph map. -/
def image (G : GeneralRegularVerticalGraph n k ε) : Set (Space n) :=
  Set.range G.map

end GeneralRegularVerticalGraph
/-- A countable cover of `K` by full general regular vertical graph images of total
seminorm at most `ε`, with a remainder of zero `H_P^k` outer measure. Indices form an
arbitrary subset of `ℕ`, permitting the empty cover. If the vertical type is unavailable,
only the empty family can occur, so the condition reduces to `H_P^k(K) = 0`.
A Hausdorff-null remainder need not have zero mass for an arbitrary source measure. -/
def HasGeneralRegularVerticalGraphCover {n : ℕ} (k : ℕ) (K : Set (Space n)) (ε : ℝ) : Prop :=
  ∃ (I : Set ℕ) (G : I → GeneralRegularVerticalGraph n k ε),
    hausdorffP n k (K \ ⋃ i, (G i).image) = 0

/-- An ordinary full vertical graph: the fields of a full vertical graph with only a parabolic Lipschitz bound at most `L`.
There is no half-derivative condition. -/
structure OrdinaryVerticalGraph (n k : ℕ) (L : ℝ) where
  vertical_dimension : 2 ≤ k
  direction : Submodule ℝ (Spatial n)
  rank_eq : Module.finrank ℝ direction + 2 = k
  offset : Spatial n
  function : SubspaceSpace direction → direction.orthogonal
  lipschitz : ∃ L' : ℝ≥0, LipschitzWith L' function ∧ (L' : ℝ) ≤ L

namespace OrdinaryVerticalGraph
variable {n k : ℕ} {L : ℝ}
/-- The graph map `(u,t) ↦ (a + u + G(u,t), t)` on the whole base `W × ℝ`. -/
def map (G : OrdinaryVerticalGraph n k L) (p : SubspaceSpace G.direction) : Space n :=
  (G.offset + (p.1 : Spatial n) + (G.function p : Spatial n), p.2)

/-- The image of the full graph map. -/
def image (G : OrdinaryVerticalGraph n k L) : Set (Space n) :=
  Set.range G.map

end OrdinaryVerticalGraph
/-- Typed set cover at tolerance `ε`, modulo Hausdorff outer measure. `horizontal`: horizontal subset
graphs of slope at most `ε`; `vertical`: full general regular vertical graphs of norm at
most `ε`; `mixed`: one family of each, with one common null remainder. An unavailable type
has no graphs, so it contributes only the empty family. -/
def HasTypedGraphCover {n : ℕ} (T : FamilyKind) (k : ℕ) (K : Set (Space n)) (ε : ℝ) : Prop :=
  match T with
  | .horizontal => HasHorizontalGraphCover k K ε
  | .vertical => HasGeneralRegularVerticalGraphCover k K ε
  | .mixed => ∃ (I J : Set ℕ) (H : I → HorizontalGraph n k ε)
      (V : J → GeneralRegularVerticalGraph n k ε),
      hausdorffP n k (K \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0

/-- Regular set rectifiability of type `T`: for every prescribed `ε > 0`, `E` has a
countable typed graph cover with bound `ε` modulo `H_P^k` outer measure. The graph families may depend on `ε`. This is a space-time set
property; it carries no source-measure absolute-continuity or time-slice assertion. -/
def IsRegularlyRectifiableSet {n : ℕ} (T : FamilyKind) (k : ℕ) (E : Set (Space n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasTypedGraphCover T k E ε

/-- Ordinary mixed parabolic set rectifiability: at every positive tolerance, horizontal graphs of slope
at most `ε` and ordinary full vertical graphs of Lipschitz bound at most `ε` cover `E`
modulo `H_P^k`. -/
def IsOrdinarilyRectifiableSet {n : ℕ} (k : ℕ) (E : Set (Space n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (I J : Set ℕ) (H : I → HorizontalGraph n k ε)
    (V : J → OrdinaryVerticalGraph n k ε),
    hausdorffP n k (E \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0

/-- `μ` is carried by countably many typed graphs of finite norm: every graph has its own
finite slope or regular norm `ε i`, and `μ` vanishes on the complement of the union of
their images. -/
def IsCarriedByFiniteNormGraphs {n : ℕ} (T : FamilyKind) (k : ℕ) (μ : Measure (Space n)) :
    Prop :=
  match T with
  | .horizontal => ∃ (I : Set ℕ) (ε : I → ℝ) (H : ∀ i, HorizontalGraph n k (ε i)),
      μ (⋃ i, (H i).image)ᶜ = 0
  | .vertical => ∃ (J : Set ℕ) (ε : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph n k (ε j)),
      μ (⋃ j, (V j).image)ᶜ = 0
  | .mixed => ∃ (I J : Set ℕ) (εH : I → ℝ) (H : ∀ i, HorizontalGraph n k (εH i))
      (εV : J → ℝ) (V : ∀ j, GeneralRegularVerticalGraph n k (εV j)),
      μ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)ᶜ = 0

/-- Regular measure rectifiability of type `T`: `μ ≪ H_P^k` and a countable typed graph carrier,
with each graph allowed its own finite slope or total regular seminorm.

The definition does not require local finiteness or one common graph bound. Under the
locally Radon hypotheses of `Characterization.qualitative_characterization`, refinement
to every positive graph tolerance is a proved conclusion. Set rectifiability instead uses
Hausdorff-null remainders and a cover at every positive tolerance from the outset. -/
def IsRegularlyRectifiableMeasure {n : ℕ} (T : FamilyKind) (k : ℕ) (μ : Measure (Space n)) :
    Prop :=
  μ ≪ hausdorffP n k ∧ IsCarriedByFiniteNormGraphs T k μ

/-- A countable typed graph carrier at a prescribed bound `ε`:
`μ((⋃ images)ᶜ) = 0`. Horizontal graphs have arbitrary subset domains; vertical graphs
are full general regular space-time graphs, with the mixed case allowing both types.
The union and its complement are evaluated by outer measure. This predicate imposes
no absolute continuity; `IsRegularlyRectifiableMeasure` supplies that additional clause,
and `qualitative_characterization` supplies covers for every positive `ε`. -/
def HasTypedMeasureCover {n : ℕ} (T : FamilyKind) (k : ℕ) (μ : Measure (Space n)) (ε : ℝ) :
    Prop :=
  match T with
  | .horizontal => ∃ (I : Set ℕ) (H : I → HorizontalGraph n k ε), μ (⋃ i, (H i).image)ᶜ = 0
  | .vertical => ∃ (J : Set ℕ) (V : J → GeneralRegularVerticalGraph n k ε),
      μ (⋃ j, (V j).image)ᶜ = 0
  | .mixed => ∃ (I J : Set ℕ) (H : I → HorizontalGraph n k ε)
      (V : J → GeneralRegularVerticalGraph n k ε),
      μ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)ᶜ = 0

end ParabolicRectifiability.Foundations
