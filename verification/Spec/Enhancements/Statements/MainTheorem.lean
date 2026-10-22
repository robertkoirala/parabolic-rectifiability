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

/-! Specification: the definitions of `ParabolicRectifiability.Enhancements.Statements.MainTheorem` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Enhancements
open ParabolicRectifiability.Foundations
/-- **The parabolic rectifiable Reifenberg theorem.**

For each `n ≥ 1` there is one constant `C > 0` such that:

* **mixed**: for every integer `1 ≤ k ≤ n+2`, every locally Radon `μ` and
  all real `M, Γ ≥ 0` with `μ(P(0,1) ∩ {S²_{μ,A_k} > M}) ≤ Γ`, there are retained
  sets `D` with all conclusions `IsRectifiableReifenbergDecomposition k C M Γ μ D`;
* **fixed family**: for every available fixed family `T` (horizontal or
  vertical, `Nonempty (Models n k T)`), the fixed-energy threshold
  `μ(P(0,1) ∩ {S²_{μ,T} > M}) ≤ Γ` gives the same conclusions, with zero measure and
  empty support of the other type;
* **ambient**: at `k = n+2`, with no energy hypothesis, the same
  conclusions hold with `M = Γ = 0` and remainder exactly `0` on `P(0,1)`.

The retained sets and actual supports are chosen before every graph tolerance (the
covers are quantified inside the decomposition). `C` is chosen before `k`, `T`, `μ`, `M`,
`Γ` and every tolerance. -/
def RectifiableReifenbergTheoremStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (exceptionalSet μ k M) ≤ ENNReal.ofReal Γ →
        ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition k C M Γ μ D) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, T ≠ .mixed → Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (Metric.ball (point 0 0) 1 ∩
          {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
        ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition k C M Γ μ D ∧
          (T = .horizontal → D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅) ∧
          (T = .vertical → D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅)) ∧
    (∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition (n + 2) C 0 0 μ D ∧
        D.remainderMeasure μ (Metric.ball (point 0 0) 1) = 0)

end ParabolicRectifiability.Enhancements
