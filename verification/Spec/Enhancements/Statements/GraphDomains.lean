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

/-! Specification: the definitions of `ParabolicRectifiability.Enhancements.Statements.GraphDomains` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Enhancements
open ParabolicRectifiability.Foundations
/-- **Graph domains on a fixed carrier.**

For each `n ≥ 1` there is `C > 0` such that: for every `1 ≤ k ≤ n+2`, one available type
`T` (horizontal or vertical, `Nonempty (Models n k T)`), and every compact `K` with
`H_P^k(K) < ∞` that has a countable type-`T` cover modulo `H_P^k` at every tolerance
`η > 0`, the singleton family `(K)` admits, for every `ε, δ > 0`, a graph-domain cover
with bound `C`, tolerance `ε` and mesh `δ`. The same cover has the local-growth bound:
whenever `H_P^k(K ∩ P(q,s)) ≤ A s^k` for all `q` and `0 < s ≤ R_*` (with `A ≥ 0`,
`R_* > 0`), its local patch sum `Σ_{α ∈ I(q,R)} c_α`, `I(q,R) = {α : z_α ∈ P(q,R),
ρ_α ≤ R}`, is at most `C A R^k` for every `q` and `0 < 2R ≤ R_*` (the
constant is the enlarged one, so one `C` serves both clauses).

`C` is chosen before `k`, `T`, `K`, the graph directions, `ε` and `δ`. The
growth data `A, R_*` are quantified after the cover, since the cover does not depend on
them. -/
def FixedCarrierGraphDomainStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ T : FamilyKind, T ≠ .mixed → Nonempty (Models n k T) →
    ∀ K : Set (Space n), IsCompact K → hausdorffP n k K < ⊤ →
    (∀ η : ℝ, 0 < η → HasTypedGraphCover T k K η) →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ G : GraphDomainCover n k C ε δ
          (if T = .horizontal then K else ∅) (if T = .vertical then K else ∅),
        ∀ A Rs : ℝ, 0 ≤ A → 0 < Rs →
          (∀ (q : Space n) (s : ℝ), 0 < s → s ≤ Rs →
            hausdorffP n k (K ∩ Metric.ball q s) ≤ ENNReal.ofReal (A * s ^ k)) →
          ∀ (q : Space n) (R : ℝ), 0 < R → 2 * R ≤ Rs →
            G.horizontal.localCharge q R + G.vertical.localCharge q R ≤
              ENNReal.ofReal (C * A * R ^ k)

/-- **Graph-domain enhancement on the same supports.**

Quantifier order: `∃ C ∀ k, μ, M, Γ ∃ E_H, E_V (hence K_H, K_V)
∀ ε, δ > 0 ∃ cover`. For each `n ≥ 1` there is one `C > 0` such that each of the three
cases of the parabolic rectifiable Reifenberg theorem (mixed, available fixed family, ambient) produces retained sets
`D` satisfying every conclusion of the parabolic rectifiable Reifenberg theorem with the constant `C`
(`IsRectifiableReifenbergDecomposition`, so the remainder bound `C M + Γ` is unchanged), and, for
every `ε, δ > 0`, the actual supports `(K_H, K_V)` of `D` admit a graph-domain cover with
bound `C`, tolerance `ε` and mesh `δ` whose patch charges also satisfy
`Σ_α c_α ≤ C` and `Σ_{α ∈ I(q,R)} c_α ≤ C R^k` for all `q` and `0 < R ≤ 1`, for the union
and for each typed subfamily (`HasScaledGraphDomainCover … 1`). The zero-threshold case is
`M = 0`; unavailable types have empty supports, hence empty families. -/
def GraphEnhancedRectifiableReifenbergStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (exceptionalSet μ k M) ≤ ENNReal.ofReal Γ →
        ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition k C M Γ μ D ∧
          ∀ ε δ : ℝ, 0 < ε → 0 < δ →
            HasScaledGraphDomainCover k (D.horizontalSupport μ) (D.verticalSupport μ)
              C ε δ 1) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, T ≠ .mixed → Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (Metric.ball (point 0 0) 1 ∩
          {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
        ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition k C M Γ μ D ∧
          (T = .horizontal → D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅) ∧
          (T = .vertical → D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅) ∧
          ∀ ε δ : ℝ, 0 < ε → 0 < δ →
            HasScaledGraphDomainCover k (D.horizontalSupport μ) (D.verticalSupport μ)
              C ε δ 1) ∧
    (∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition (n + 2) C 0 0 μ D ∧
        D.remainderMeasure μ (Metric.ball (point 0 0) 1) = 0 ∧
        ∀ ε δ : ℝ, 0 < ε → 0 < δ →
          HasScaledGraphDomainCover (n + 2) (D.horizontalSupport μ) (D.verticalSupport μ)
            C ε δ 1)

end ParabolicRectifiability.Enhancements
