import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Foundations.Carriers
import Spec.Foundations.Density
import Spec.Foundations.DensityConditions
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
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

/-! Specification: the definitions of `ParabolicRectifiability.IntegralCanonical.Defs` used by the headline statements. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ParabolicRectifiability.IntegralCanonical
open ParabolicRectifiability.Foundations
/-- The full-source finite-energy set `E_T = {z : S^R_{μ,T}(z) < ∞}`: horizontal, vertical, and mixed choices give `E_H`, `E_V`,
and `G`. For `R > 0` an unavailable family gives `E_T = ∅`. For `R ≤ 0` the scale
interval is empty, so the energy is zero and `E_T` is the whole space. Canonical
endpoint-independence results concern positive endpoints. -/
def finiteEnergySet {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ) :
    Set (Space n) :=
  {z | squareEnergy μ k T R z < ⊤}

/-- The infinite-mixed-energy set `E_+ = X \ G`, `G = {S^R_{μ,mix} < ∞}`. -/
def pureSet {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (R : ℝ) : Set (Space n) :=
  (finiteEnergySet μ k .mixed R)ᶜ

/-- The canonical horizontal restriction `μ_H = μ⌊{S^R_{μ,H} < ∞}`. The energy inside the defining set is computed from the
original `μ`, before restriction. Its rectifiability and compatibility with the other
parts are conclusions of `canonical_decomposition` under the stated source-class hypotheses. -/
def horizontalPart {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (R : ℝ) : Measure (Space n) :=
  μ.restrict (finiteEnergySet μ k .horizontal R)

/-- The canonical vertical restriction `μ_V = μ⌊{S^R_{μ,V} < ∞}`, selected using the full
original source. For `R > 0` an
unavailable vertical family gives the empty set and hence the zero restriction. -/
def verticalPart {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (R : ℝ) : Measure (Space n) :=
  μ.restrict (finiteEnergySet μ k .vertical R)

/-- The canonical pure part `μ_+ = μ⌊E_+`. -/
def purePart {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (R : ℝ) : Measure (Space n) :=
  μ.restrict (pureSet μ k R)

/-- Graph purity: outer measure zero on every horizontal graph of
finite slope and on every full general regular vertical graph of finite total seminorm.
The slope or seminorm bound `ε` is an arbitrary real number. -/
def IsGraphPure {n : ℕ} (k : ℕ) (μ : Measure (Space n)) : Prop :=
  (∀ (ε : ℝ) (H : HorizontalGraph n k ε), μ H.image = 0) ∧
    ∀ (ε : ℝ) (V : GeneralRegularVerticalGraph n k ε), μ V.image = 0

/-- The three structural conditions (a), (b), (c) of the integral criterion, indexed by
`Fin 3` in this order. They are the Foundations predicates
`HasPositiveUpperFiniteLowerDensity` (a), `HasPositiveFiniteUpperDensity` (b) and
`IsIntrinsicSource` (c). -/
def StructuralCondition {n : ℕ} (i : Fin 3) (k : ℕ) (μ : Measure (Space n)) : Prop :=
  match i with
  | 0 => HasPositiveUpperFiniteLowerDensity k μ
  | 1 => HasPositiveFiniteUpperDensity k μ
  | 2 => IsIntrinsicSource k μ

/-- The bounded cylinders `P(z,r)`, `z ∈ X`, `0 < r < ∞`: open parabolic balls of positive
real radius. Every bounded set lies in some `P(0,j)`. -/
def boundedCylinders (n : ℕ) : Set (Set (Space n)) :=
  {A | ∃ (z : Space n) (r : ℝ), 0 < r ∧ A = Metric.ball z r}

/-- The reduced testing family `P(0,j)`, `j ∈ ℕ`, `j ≥ 1`. -/
def originCylinders (n : ℕ) : Set (Set (Space n)) :=
  {A | ∃ j : ℕ, 1 ≤ j ∧ A = Metric.ball (point 0 0) (j : ℝ)}

/-- Test (1), the vanishing capped tail: on every tested set `A`,
`lim_{ρ↓0} ∫_A min{1, T_ρ} dμ = 0`, where `T_ρ = S^ρ_{μ,T}`. The limit is along positive
radii tending to zero (`𝓝[>] 0`); the restriction `ρ ≤ R` to radii below the endpoint does
not affect this limit, so the test has no endpoint parameter. -/
def CappedTailTest {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (𝒜 : Set (Set (Space n))) : Prop :=
  ∀ A ∈ 𝒜, Tendsto (fun ρ : ℝ => ∫⁻ z in A, min 1 (squareEnergy μ k T ρ z) ∂μ)
    (𝓝[>] 0) (𝓝 0)

/-- Test (2), the vanishing normalized capped energy: on every tested set
`A`, `lim_{L→∞} L^{-1} ∫_A min{S, L} dμ = 0`, where `S = S^R_{μ,T}`. The cap `L` is a
real number tending to `+∞`; the value `S = ⊤` is capped to `L`. -/
def CappedValueTest {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ)
    (𝒜 : Set (Set (Space n))) : Prop :=
  ∀ A ∈ 𝒜, Tendsto (fun L : ℝ =>
      (ENNReal.ofReal L)⁻¹ * ∫⁻ z in A, min (squareEnergy μ k T R z) (ENNReal.ofReal L) ∂μ)
    atTop (𝓝 0)

/-- Test (3), the compact integrable exhaustion: increasing compact sets
`K_j` with `μ(X \ ⋃_j K_j) = 0` and `∫_{K_j} S dμ < ∞` for every `j`, where
`S = S^R_{μ,T}`. The compact sets restrict only the testing points; the energy source
remains `μ`. -/
def CompactExhaustionTest {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (R : ℝ) : Prop :=
  ∃ K : ℕ → Set (Space n), (∀ j, IsCompact (K j)) ∧ Monotone K ∧
    μ (⋃ j, K j)ᶜ = 0 ∧ ∀ j, ∫⁻ z in K j, squareEnergy μ k T R z ∂μ < ⊤

/-- Test (4), the strictly positive weight: a Borel `w : X → (0,1]` with
`∫_A w S dμ < ∞` on every tested set `A`, where `S = S^R_{μ,T}`. The weight is real valued,
Borel, and strictly positive at every point; the product `w S` is formed in `ℝ≥0∞`. -/
def PositiveWeightTest {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ)
    (𝒜 : Set (Set (Space n))) : Prop :=
  ∃ w : Space n → ℝ, Measurable w ∧ (∀ z, 0 < w z ∧ w z ≤ 1) ∧
    ∀ A ∈ 𝒜, ∫⁻ z in A, ENNReal.ofReal (w z) * squareEnergy μ k T R z ∂μ < ⊤

/-- An admissible gauge `Φ : [0,∞) → [0,∞)` of test (5): continuous,
nondecreasing, concave and unbounded on `[0,∞)`, with `Φ(0) = 0` and nonnegative values.
The function is given on `ℝ`; only its values on `[0,∞)` are constrained or used. -/
def IsAdmissibleGauge (Φ : ℝ → ℝ) : Prop :=
  ContinuousOn Φ (Ici 0) ∧ MonotoneOn Φ (Ici 0) ∧ ConcaveOn ℝ (Ici 0) Φ ∧
    ¬ BddAbove (Φ '' Ici 0) ∧ Φ 0 = 0 ∧ ∀ u : ℝ, 0 ≤ u → 0 ≤ Φ u

/-- The extension of a gauge to `[0,∞]` with `Φ(∞) = ∞`: a finite value `x` is sent
to `Φ(x)` and `⊤` to `⊤`. -/
def extendedGauge (Φ : ℝ → ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ENNReal.ofReal (Φ x.toReal)

/-- Test (5), the adaptive concave gauge: for every tested set `A` there is
an admissible gauge `Φ_A` with `∫_A Φ_A(S) dμ < ∞`, where `S = S^R_{μ,T}` and
`Φ_A(∞) = ∞`. The gauge may depend on `μ` and on `A`. -/
def AdaptiveGaugeTest {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (R : ℝ)
    (𝒜 : Set (Set (Space n))) : Prop :=
  ∀ A ∈ 𝒜, ∃ Φ : ℝ → ℝ, IsAdmissibleGauge Φ ∧
    ∫⁻ z in A, extendedGauge Φ (squareEnergy μ k T R z) ∂μ < ⊤

/-- The five integral tests (1)–(5) of the integral equivalences, indexed by `Fin 5` in this order (index `j` is test `(j+1)`), for the family `T`, the
endpoint `R` of `S = S^R_{μ,T}`, and the family `𝒜` of tested sets. Test (3) uses no
tested sets. -/
def IntegralTest {n : ℕ} (j : Fin 5) (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (R : ℝ) (𝒜 : Set (Set (Space n))) : Prop :=
  match j with
  | 0 => CappedTailTest μ k T 𝒜
  | 1 => CappedValueTest μ k T R 𝒜
  | 2 => CompactExhaustionTest μ k T R
  | 3 => PositiveWeightTest μ k T R 𝒜
  | 4 => AdaptiveGaugeTest μ k T R 𝒜

end ParabolicRectifiability.IntegralCanonical
