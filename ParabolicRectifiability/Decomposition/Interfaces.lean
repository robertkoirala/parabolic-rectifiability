import ParabolicRectifiability.Specifications.Rectifiability
import ParabolicRectifiability.Measure.BetaLaws

/-! # Interfaces for the rectifiable Reifenberg proof

These are concrete intermediate objects, not additional hypotheses of the main
theorem. No graph-cover conclusion is built into a geometric core certificate.
The localized source is always an actual restriction of the original measure.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-- The natural square over every positive scale, with the same source. -/
def allScaleEnergy {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) : ℝ≥0∞ :=
  ∫⁻ r in Ioi 0, betaSq ν k T z r ∂scaleMeasure

/-- Family-specific good points in the original unit ball. -/
def thresholdGoodSet {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (M : ℝ) : Set (Space n) :=
  Metric.ball (point 0 0) 1 ∩ {z | squareEnergy μ k T 2 z ≤ ENNReal.ofReal M}

/-- The output assigned to the other testing type must vanish. -/
def RespectsFamily {n : ℕ} (T : FamilyKind) (H V : Set (Space n)) : Prop :=
  (T = .horizontal → V = ∅) ∧ (T = .vertical → H = ∅)

/-- Finite localization of the square-good part; the number of pieces is
bounded before choosing the source and the threshold. -/
structure GoodSourceLocalization {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (T : FamilyKind) (M : ℝ) (N : ℕ) where
  count : ℕ
  count_le : count ≤ N
  region : Fin count → Set (Space n)
  measurable : ∀ i, MeasurableSet (region i)
  disjoint : ∀ i j, i ≠ j → Disjoint (region i) (region j)
  cover : (⋃ i, region i) = thresholdGoodSet μ k T M
  center : Fin count → Space n
  support_small : ∀ i, (μ.restrict (region i)).support ⊆
    Metric.closedBall (center i) (1 / 64)
  finite : ∀ i, IsFiniteMeasure (μ.restrict (region i))
  innerRegular : ∀ i, (μ.restrict (region i)).InnerRegular
  energy : ∀ i, ∀ᵐ z ∂μ.restrict (region i),
    allScaleEnergy (μ.restrict (region i)) k T z ≤ ENNReal.ofReal (2 * M)

/-- An actual global spatial chart, restricted to a compact parameter set,
with its possibly nonconstant time function on that set. -/
structure HorizontalCoreChart (n k : ℕ) (K : Set (Space n)) where
  dimension : 1 ≤ k ∧ k ≤ n
  domain : Set (Spatial k)
  compact_domain : IsCompact domain
  spatial : Spatial k → Spatial n
  time : domain → ℝ
  constant : ℝ≥0
  spatial_lipschitz : LipschitzWith constant spatial
  spatial_antilipschitz : AntilipschitzWith constant spatial
  chart_lipschitz : LipschitzWith constant
    (fun u : domain => point (spatial u) (time u))
  chart_antilipschitz : AntilipschitzWith constant
    (fun u : domain => point (spatial u) (time u))
  image : Set.range (fun u : domain => point (spatial u) (time u)) = K

/-- The horizontal core: the input of the horizontal regularity theorem
`horizontal_core_graph_cover`. -/
def IsHorizontalCore {n : ℕ} (k : ℕ) (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Nonempty (HorizontalCoreChart n k K) ∧
    ∀ᵐ z ∂(hausdorffP n k).restrict K,
      squareEnergy ((hausdorffP n k).restrict K) k .horizontal 1 z < ⊤

/-- Positive lower density, expressed with explicit eventual radius bounds. -/
def HasPositiveLowerDensity {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (z : Space n) : Prop :=
  ∃ a r₀ : ℝ, 0 < a ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
    ENNReal.ofReal (a * r ^ k) ≤ ν (Metric.ball z r)

/-- The actual Hausdorff source and density/square hypotheses of the regular
vertical carrier `vertical_core_graph_cover`. This includes time-only bases and excludes the separately treated ambient endpoint. -/
def IsVerticalCore {n : ℕ} (k : ℕ) (K : Set (Space n)) : Prop :=
  2 ≤ k ∧ k < n + 2 ∧ IsCompact K ∧ hausdorffP n k K < ⊤ ∧
  ∃ U r₀ : ℝ, 0 ≤ U ∧ 0 < r₀ ∧
    (∀ q r, 0 < r → r ≤ r₀ →
      ((hausdorffP n k).restrict K) (Metric.ball q r) ≤ ENNReal.ofReal (U * r ^ k)) ∧
    (∀ᵐ z ∂(hausdorffP n k).restrict K,
      HasPositiveLowerDensity ((hausdorffP n k).restrict K) k z ∧
      squareEnergy ((hausdorffP n k).restrict K) k .vertical r₀ z < ⊤)

/-- The geometric extraction output. The cores carry chart/energy certificates,
not the regular graph covers, which are produced separately by
`horizontal_core_graph_cover` and `vertical_core_graph_cover`. -/
structure GeometricExtraction {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (M C : ℝ) where
  carrier : Set (Space n)
  compact : IsCompact carrier
  subset_support : carrier ⊆ ν.support
  loss : ν carrierᶜ ≤ ENNReal.ofReal (C * M)
  horizontalIndex : Set ℕ
  verticalIndex : Set ℕ
  horizontalCore : horizontalIndex → Set (Space n)
  verticalCore : verticalIndex → Set (Space n)
  horizontal_certificate : ∀ i, IsHorizontalCore k (horizontalCore i)
  vertical_certificate : ∀ i, IsVerticalCore k (verticalCore i)
  horizontal_subset : ∀ i, horizontalCore i ⊆ carrier
  vertical_subset : ∀ i, verticalCore i ⊆ carrier
  null_remainder : hausdorffP n k
    (carrier \ ((⋃ i, horizontalCore i) ∪ ⋃ i, verticalCore i)) = 0
  horizontal_unavailable : (T = .vertical ∨ ¬ (1 ≤ k ∧ k ≤ n)) → horizontalIndex = ∅
  vertical_unavailable : (T = .horizontal ∨ ¬ (2 ≤ k ∧ k ≤ n + 2)) → verticalIndex = ∅

/-- Equal-radius content bounds. Variable-radius packing is treated separately
(`HasFiniteBallPacking`). -/
structure HasMetricContentBounds {n : ℕ} (k : ℕ) (C : ℝ)
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

/-- A concrete all-radius lower bound for the unchanged restricted source. -/
def HasUniformLowerMass {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (a : ℝ) (K : Set (Space n)) : Prop :=
  ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1 →
    ENNReal.ofReal (a * r ^ k) ≤ ν (Metric.closedBall z r)

/-- Density refinement of the geometric carrier, with its own source loss.
The lower bound is for `ν` restricted to the geometric carrier, not to `set`. -/
structure DensityRefinement {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (M C : ℝ) (G : Set (Space n)) where
  set : Set (Space n)
  compact : IsCompact set
  subset : set ⊆ G
  loss : (ν.restrict G) setᶜ ≤ ENNReal.ofReal (C * M)
  lower_mass : HasUniformLowerMass (ν.restrict G) k M set
  content : HasMetricContentBounds k C set

/-- Actual compact approximants, selected using the source measure before
choosing any graph tolerance. They need not be source-null on graph exceptions. -/
structure CompactTypedPieces {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (M C : ℝ) (K : Set (Space n)) where
  horizontal : Set (Space n)
  vertical : Set (Space n)
  horizontal_compact : IsCompact horizontal
  vertical_compact : IsCompact vertical
  horizontal_subset : horizontal ⊆ K
  vertical_subset : vertical ⊆ K
  disjoint : Disjoint horizontal vertical
  loss : ν (horizontal ∪ vertical)ᶜ ≤ ENNReal.ofReal (C * M)
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) → horizontal = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) → vertical = ∅
  family : RespectsFamily T horizontal vertical
  horizontal_graphs : ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k horizontal ε
  vertical_graphs : ∀ ε : ℝ, 0 < ε → HasRegularVerticalGraphCover k vertical ε

/-- Finite packing retains every local center and radius quantifier. -/
def HasFiniteBallPacking {n : ℕ} (k : ℕ) (C : ℝ) (K : Set (Space n)) : Prop :=
  ∀ q R, 0 < R → R ≤ 1 →
    ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
      (∀ i, z i ∈ K ∩ Metric.ball q R) →
      (∀ i, 0 < r i ∧ r i ≤ R) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * R ^ k)

/-- Final family-specific output, with genuine measures and supports. -/
def HasFamilyDecomposition {n : ℕ} (k : ℕ) (T : FamilyKind) (C M Γ : ℝ)
    (μ : Measure (Space n)) : Prop :=
  ∃ D : RetainedSets n, IsRectifiabilityDecomposition k C M Γ μ D ∧
    (T = .horizontal → D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅) ∧
    (T = .vertical → D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅)

end ParabolicRectifiability
