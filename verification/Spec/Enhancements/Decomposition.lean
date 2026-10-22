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
import Spec.Foundations.Density
import Spec.Foundations.GraphDomainCover
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Foundations.SupportBounds
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
import Spec.Specifications.Rectifiability

/-! Specification: the definitions of `ParabolicRectifiability.Enhancements.Decomposition` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Enhancements
open ParabolicRectifiability.Foundations
/-- The conclusions of the parabolic rectifiable Reifenberg theorem for the
retained sets `D`, with constant `C`, threshold `M` and allowance `Γ`:
the restriction decomposition `μ = μ⁺ + μ_H + μ_V`; the loss `μ⁺(P(0,1)) ≤ C M + Γ`
(coefficient one on `Γ`); zero measure and empty support for an unavailable type; and all
support conclusions of the actual supports `K_H`, `K_V` at centre `0` and scale `1`
(compact in `P̄(0,1)`, every-tolerance horizontal and general regular vertical covers,
`H_P^k(K) ≤ C`, local Hausdorff, separated-set, finite and countable packing, tube).
Compared with `IsRectifiabilityDecomposition`, the vertical covers are in the
general regular class and the global Hausdorff bound is added. -/
structure IsRectifiableReifenbergDecomposition {n : ℕ} (k : ℕ) (C M Γ : ℝ)
    (μ : Measure (Space n)) (D : RetainedSets n) : Prop where
  measure_eq : μ = D.remainderMeasure μ + D.horizontalMeasure μ + D.verticalMeasure μ
  remainder_bound : D.remainderMeasure μ (Metric.ball (point 0 0) 1) ≤
    ENNReal.ofReal (C * M + Γ)
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) →
    D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) →
    D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅
  supports : HasRegularSupportBounds k C (point 0 0) 1
    (D.horizontalSupport μ) (D.verticalSupport μ)

/-- Graph-domain covers with absolute charge bounds at scale `R` (used at `R = 1` in the
graph-domain enhancement and at general `R` in the scaled theorem): a graph-domain cover of `(K_H, K_V)`
with bound `C`, tolerance `ε` and mesh `δ` (`Foundations.GraphDomainCover`: patch radii
in `(0, δ]`, relative trace, global and local bounds), whose patch charges also satisfy
`Σ_α c_α ≤ C R^k` and `Σ_{α ∈ I(q,s)} c_α ≤ C s^k` for every centre `q` and
`0 < s ≤ R`, for the union and for each typed subfamily.

The standing assumptions of a graph-domain cover (compact carriers,
`H_P^k(K) < ∞`, empty carriers for unavailable types) are not repeated here: every
statement using this predicate obtains them from its decomposition conjunct. -/
def HasScaledGraphDomainCover {n : ℕ} (k : ℕ) (KH KV : Set (Space n)) (C ε δ R : ℝ) :
    Prop :=
  ∃ G : GraphDomainCover n k C ε δ KH KV,
    G.horizontal.totalCharge + G.vertical.totalCharge ≤ ENNReal.ofReal (C * R ^ k) ∧
    G.horizontal.totalCharge ≤ ENNReal.ofReal (C * R ^ k) ∧
    G.vertical.totalCharge ≤ ENNReal.ofReal (C * R ^ k) ∧
    ∀ (q : Space n) (s : ℝ), 0 < s → s ≤ R →
      G.horizontal.localCharge q s + G.vertical.localCharge q s ≤
          ENNReal.ofReal (C * s ^ k) ∧
        G.horizontal.localCharge q s ≤ ENNReal.ofReal (C * s ^ k) ∧
        G.vertical.localCharge q s ≤ ENNReal.ofReal (C * s ^ k)

/-- The enhanced restriction decomposition on the cylinder `P(a,R)` for the family `T`,
without its loss:
disjoint Borel sets `E_H, E_V ⊂ P(a,R)`; the restriction decomposition
`μ = μ⌊(E_H ∪ E_V)ᶜ + μ⌊E_H + μ⌊E_V`; zero measure and empty support for an
unavailable type; for a fixed family `T`, zero measure and empty support of the other
type (vacuous for `T = mixed`); all support conclusions of the actual supports
`K_T = supp(μ⌊E_T)` at centre `a` and scale `R`; and, for every tolerance `ε > 0` and
absolute mesh `δ > 0`, graph-domain covers of `(K_H, K_V)` with bound `C` and the
absolute charge bounds at scale `R`. The supports are fixed before `ε` and `δ`. -/
structure IsLocalEnhancedDecomposition {n : ℕ} (k : ℕ) (T : FamilyKind) (C : ℝ)
    (a : Space n) (R : ℝ) (μ : Measure (Space n)) (EH EV : Set (Space n)) : Prop where
  measurable_horizontal : MeasurableSet EH
  measurable_vertical : MeasurableSet EV
  disjoint : Disjoint EH EV
  horizontal_subset : EH ⊆ Metric.ball a R
  vertical_subset : EV ⊆ Metric.ball a R
  measure_eq : μ = μ.restrict (EH ∪ EV)ᶜ + μ.restrict EH + μ.restrict EV
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) →
    μ.restrict EH = 0 ∧ (μ.restrict EH).support = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) →
    μ.restrict EV = 0 ∧ (μ.restrict EV).support = ∅
  horizontal_only : T = .horizontal →
    μ.restrict EV = 0 ∧ (μ.restrict EV).support = ∅
  vertical_only : T = .vertical →
    μ.restrict EH = 0 ∧ (μ.restrict EH).support = ∅
  supports : HasRegularSupportBounds k C a R (μ.restrict EH).support (μ.restrict EV).support
  graph_domains : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
    HasScaledGraphDomainCover k (μ.restrict EH).support (μ.restrict EV).support C ε δ R

/-- `Λ_q = ∫_{P(a,R)} (S^{2R}_{μ,T})^q dμ`, an extended nonnegative integral of the `ℝ≥0∞` real power of
the full-source square energy with endpoint `2R`. -/
def powerEnergy {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (q : ℝ)
    (a : Space n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.ball a R, squareEnergy μ k T (2 * R) z ^ q ∂μ

/-- `Λ_Φ = ∫_{P(a,R)} Φ(S^{2R}_{μ,T}) dμ`, for a gauge `Φ : [0,∞] → [0,∞]`. -/
def gaugeEnergy {n : ℕ} (Φ : ℝ≥0∞ → ℝ≥0∞) (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (a : Space n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.ball a R, Φ (squareEnergy μ k T (2 * R) z) ∂μ

/-- `𝓔 = ∫_U S²_{μ,T} dμ` with `U = P(0,1)` and the whole original `μ` in the
energy. -/
def unitSquareEnergy {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) : ℝ≥0∞ :=
  ∫⁻ z in Metric.ball (point 0 0) 1, squareEnergy μ k T 2 z ∂μ

/-- `𝓔_{q,R} = ∫_{P(q,R)} S^{2R}_{μ,T} dμ`, the local integrated energy. -/
def localSquareEnergy {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (q : Space n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Metric.ball q R, squareEnergy μ k T (2 * R) z ∂μ

/-- The upper-density level set `O ∩ {z : Θ^{k,*}(μ,z) ≥ a}`, with the density of the
original measure `μ`. -/
def upperDensityLevelSet {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (O : Set (Space n))
    (a : ℝ) : Set (Space n) :=
  O ∩ {z | ENNReal.ofReal a ≤ upperDensity μ k z}

end ParabolicRectifiability.Enhancements
