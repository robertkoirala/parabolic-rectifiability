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
import Spec.Enhancements.Decomposition
import Spec.Enhancements.Statements.ScalingRates
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
import Spec.Measure.BetaLaws
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Similarity
import Spec.Metric.Space
import Spec.Specifications.Rectifiability

/-! Specification: the definitions of `ParabolicRectifiability.Enhancements.Statements.ScaledCore` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Enhancements
open ParabolicRectifiability.Foundations
/-- The restriction decomposition on the cylinder `P(a,R)` for the family `T`,
without its loss and **without graph-domain covers**.

Its fields are exactly the fields of `IsLocalEnhancedDecomposition` except
`graph_domains`: disjoint
Borel sets `E_H, E_V ⊂ P(a,R)`; the restriction decomposition
`μ = μ⌊(E_H ∪ E_V)ᶜ + μ⌊E_H + μ⌊E_V`; zero measure and empty support for an unavailable
type; for a fixed family `T`, zero measure and empty support of the other type (vacuous for
`T = mixed`); and all support conclusions of the actual supports `K_T = supp(μ⌊E_T)` at
centre `a` and scale `R` (`HasRegularSupportBounds`: compact in `P̄(a,R)`, every-tolerance
horizontal and general regular vertical covers, `H_P^k(K) ≤ C R^k`, local Hausdorff,
separated-set, finite and countable packing, tube). The supports are fixed before every
cover tolerance, which is quantified inside `HasRegularSupportBounds`. -/
structure IsLocalCoreDecomposition {n : ℕ} (k : ℕ) (T : FamilyKind) (C : ℝ)
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

/-- The scaled threshold decomposition without graph-domain covers, with constant `C` in
dimension `n`. It is `ScaledThresholdProperty n C` with
`IsLocalEnhancedDecomposition` replaced by `IsLocalCoreDecomposition`: for `1 ≤ k ≤ n+2`,
locally Radon `μ`, `a ∈ X`, `R > 0`, the mixed family or an available fixed family `T`, and
real `M, Γ ≥ 0` with `μ(P(a,R) ∩ {S^{2R}_{μ,T} > M}) ≤ Γ`, there are retained sets
`E_H, E_V` forming the restriction decomposition on `P(a,R)` with constant `C` and loss
`μ⁺(P(a,R)) ≤ C M R^k + Γ`.

Helper proposition parameterized by the constant; the theorem statement is
`ScaledRectifiableReifenbergCoreStatement`. -/
def ScaledThresholdCoreProperty (n : ℕ) (C : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ (a : Space n) (R : ℝ), 0 < R →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
    μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z}) ≤
      ENNReal.ofReal Γ →
    ∃ EH EV : Set (Space n), IsLocalCoreDecomposition k T C a R μ EH EV ∧
      μ.restrict (EH ∪ EV)ᶜ (Metric.ball a R) ≤ ENNReal.ofReal (C * M * R ^ k + Γ)

/-- **Scaling contract without graph-domain covers**: the scaling identities, and, for
each `n ≥ 1`, one constant `C > 0` (chosen before `k`, `μ`, `a`, `R`, `T`, `M`, `Γ` and
every cover tolerance) for the scaled threshold decomposition with every support
conclusion.

Omitted clause: the graph-domain covers (the field
`IsLocalEnhancedDecomposition.graph_domains` of `ScaledRectifiableReifenbergStatement`). Nothing else
differs from `ScaledRectifiableReifenbergStatement`. -/
def ScaledRectifiableReifenbergCoreStatement : Prop :=
  ScalingIdentitiesStatement ∧
    ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ScaledThresholdCoreProperty n C

end ParabolicRectifiability.Enhancements
