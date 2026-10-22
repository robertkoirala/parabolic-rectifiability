import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping
import ParabolicRectifiability.Measure.Neck.Selection.ModelFit

/-! # Exact family optimizers

Proof of `ExactModelStatement`.
The base `NeckSelection.exists_fit_minimizer` is applied to the finite measure
`ν = μ.restrict (closedBall z r)`; the fit of every model against `ν` on `ball z r` equals its fit
against the original source `μ`, so the minimizer transfers. The fitting source is never replaced
by `μ ⌞ S`. The horizontal case is covered by the same base lemma, whose `modelCost` is the joint
objective `max{dist(x, a + U)², |t - τ|}`. Helper prefix `d1bexact_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

/-- Localizing the source to the closed ball does not change the fit on the open ball. -/
theorem d1bexact_fit_restrict_closedBall {n k : ℕ} {F : FamilyKind} (μ : Measure (Space n))
    (L : Models n k F) (z : Space n) (r : ℝ) :
    fit (μ.restrict (Metric.closedBall z r)) L z r = fit μ L z r := by
  unfold fit
  rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
    Set.inter_eq_left.mpr Metric.ball_subset_closedBall]

/-- **Exact family optimizers** (`ExactModelStatement`). -/
theorem d1b_exactModel_proof : ExactModelStatement := by
  intro n k μ hμ T hT z r
  have : IsFiniteMeasure (μ.restrict (Metric.closedBall z r)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_closedBall z r).measure_lt_top⟩
  obtain ⟨M, hM⟩ := NeckSelection.exists_fit_minimizer (μ.restrict (Metric.closedBall z r))
    (NeckSelection.nonempty_models hT) z r
  refine ⟨M, fun L' => ?_⟩
  have h1 : fit (μ.restrict (Metric.closedBall z r)) M z r ≤
      fit (μ.restrict (Metric.closedBall z r)) L' z r :=
    hM.trans (iInf_le (fun L => fit (μ.restrict (Metric.closedBall z r)) L z r) L')
  simpa only [d1bexact_fit_restrict_closedBall] using h1

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
