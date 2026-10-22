import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.ModelDistance
import Spec.Geometry.SubspaceCoordinates
import Spec.Measure.Beta
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Specifications.Rectifiability` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace ParabolicRectifiability
/-- Retained Borel pieces of the original source inside the open unit ball. -/
structure RetainedSets (n : ℕ) where
  horizontal : Set (Space n)
  vertical : Set (Space n)
  measurable_horizontal : MeasurableSet horizontal
  measurable_vertical : MeasurableSet vertical
  disjoint : Disjoint horizontal vertical
  horizontal_subset : horizontal ⊆ Metric.ball (point 0 0) 1
  vertical_subset : vertical ⊆ Metric.ball (point 0 0) 1

namespace RetainedSets
variable {n : ℕ}
/-- Restriction of the original source to the retained horizontal Borel set. -/
def horizontalMeasure (D : RetainedSets n) (μ : Measure (Space n)) : Measure (Space n) :=
  μ.restrict D.horizontal

/-- Restriction of the original source to the retained vertical Borel set. -/
def verticalMeasure (D : RetainedSets n) (μ : Measure (Space n)) : Measure (Space n) :=
  μ.restrict D.vertical

/-- Restriction to the complement of both retained sets. This includes all
source mass outside the open unit ball; the theorem bounds its mass inside that ball. -/
def remainderMeasure (D : RetainedSets n) (μ : Measure (Space n)) : Measure (Space n) :=
  μ.restrict (D.horizontal ∪ D.vertical)ᶜ

/-- Actual topological support of the horizontal restricted measure. It
need not equal the retained Borel set; compactness is a conclusion of the decomposition. -/
def horizontalSupport (D : RetainedSets n) (μ : Measure (Space n)) : Set (Space n) :=
  (D.horizontalMeasure μ).support

/-- Actual topological support of the vertical restricted measure, with
compactness and graph coverage asserted separately in the decomposition. -/
def verticalSupport (D : RetainedSets n) (μ : Measure (Space n)) : Set (Space n) :=
  (D.verticalMeasure μ).support

/-- Union of the two actual supports on which the common content and
packing estimates are imposed. -/
def supportUnion (D : RetainedSets n) (μ : Measure (Space n)) : Set (Space n) :=
  D.horizontalSupport μ ∪ D.verticalSupport μ

end RetainedSets
/-- Five quantitative bounds with one constant `C`: local `k`-dimensional
Hausdorff measure, finite separated sets, ambient tubular volume, and finite
or countable disjoint-ball packing with individually varying radii. Local
parents have arbitrary centers and `0 < R ≤ 1`; packing radii lie in `(0,R]`.
The tubular estimate uses `0 < r ≤ 1` and exponent `n + 2 - k` (natural
subtraction; the main theorem separately imposes `k ≤ n + 2`). Extended
distance makes the neighborhood of the empty set empty. -/
structure HasRectifiabilityContentBounds {n : ℕ} (k : ℕ) (C : ℝ)
    (K : Set (Space n)) : Prop where
  hausdorff : ∀ q R, 0 < R → R ≤ 1 →
    hausdorffP n k (K ∩ Metric.ball q R) ≤ ENNReal.ofReal (C * R ^ k)
  separated : ∀ q R r, 0 < R → R ≤ 1 → 0 < r → r ≤ R →
    ∀ F : Finset (Space n), (↑F : Set (Space n)) ⊆ K ∩ Metric.ball q R →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) →
        (F.card : ℝ) ≤ C * (R / r) ^ k
  minkowski : ∀ r, 0 < r → r ≤ 1 →
    parabolicVolume n {z | Metric.infEDist z K < ENNReal.ofReal r} ≤
      ENNReal.ofReal (C * r ^ (n + 2 - k))
  finite_packing : ∀ q R, 0 < R → R ≤ 1 →
    ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
      (∀ i, z i ∈ K ∩ Metric.ball q R) →
      (∀ i, 0 < r i ∧ r i ≤ R) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * R ^ k)
  countable_packing : ∀ q R, 0 < R → R ≤ 1 →
    ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ),
      (∀ i, z i ∈ K ∩ Metric.ball q R) →
      (∀ i, 0 < r i ∧ r i ≤ R) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑' i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * R ^ k)

/-- The exact output attached to the chosen retained sets. No absolute
continuity or pure unrectifiability is asserted for these measures. -/
structure IsRectifiabilityDecomposition {n : ℕ} (k : ℕ) (C M Γ : ℝ)
    (μ : Measure (Space n)) (D : RetainedSets n) : Prop where
  measure_eq : μ = D.remainderMeasure μ + D.horizontalMeasure μ + D.verticalMeasure μ
  remainder_bound : D.remainderMeasure μ (Metric.ball (point 0 0) 1) ≤
    ENNReal.ofReal (C * M + Γ)
  horizontal_compact : IsCompact (D.horizontalSupport μ)
  vertical_compact : IsCompact (D.verticalSupport μ)
  horizontal_in_unit : D.horizontalSupport μ ⊆ Metric.closedBall (point 0 0) 1
  vertical_in_unit : D.verticalSupport μ ⊆ Metric.closedBall (point 0 0) 1
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) →
    D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) →
    D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅
  horizontal_graphs : ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k (D.horizontalSupport μ) ε
  vertical_graphs : ∀ ε : ℝ, 0 < ε → HasRegularVerticalGraphCover k (D.verticalSupport μ) ε
  content : HasRectifiabilityContentBounds k C (D.supportUnion μ)

/-- The mixed-family contract proved by `main_rectifiability`: a constant
depending only on `n` precedes `k`, the source and thresholds; retained sets
precede all graph tolerances in the output. The exceptional energy is that of
the original source, and the coefficient of `Γ` in the remainder is exactly one. -/
def MainRectifiabilityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
      μ (exceptionalSet μ k M) ≤ ENNReal.ofReal Γ →
      ∃ D : RetainedSets n, IsRectifiabilityDecomposition k C M Γ μ D

/-- The fixed-family contract proved by `fixed_family_rectifiability`.
Availability is the explicit hypothesis `Nonempty (Models n k T)`, in addition
to `1 ≤ k ≤ n + 2`. Horizontal testing yields zero vertical measure and support;
vertical testing yields zero horizontal measure and support. -/
def FixedFamilyRectifiabilityStatement (T : FamilyKind) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → Nonempty (Models n k T) →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      ∃ D : RetainedSets n, IsRectifiabilityDecomposition k C M Γ μ D ∧
        (T = .horizontal → D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅) ∧
        (T = .vertical → D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅)

/-- At ambient parabolic dimension the remainder in the unit ball is zero,
with no beta-energy hypothesis at all. -/
def AmbientRectifiabilityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∃ D : RetainedSets n, IsRectifiabilityDecomposition (n + 2) C 0 0 μ D ∧
        D.remainderMeasure μ (Metric.ball (point 0 0) 1) = 0

end ParabolicRectifiability
