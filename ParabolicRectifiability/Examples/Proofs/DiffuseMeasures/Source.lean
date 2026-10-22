import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements
import ParabolicRectifiability.Metric.Measure

/-! # Source-ball bounds for the diffuse measures (`e2_diffuse_source_proof`)

Route: `Measure.restrict_le_self`, `parabolicVolume_ball`, `omega_pos`, `omega_lt_top`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

private theorem e2d1_ball_lt_top (n : ℕ) (r : ℝ) (hr : 0 < r) :
    parabolicVolume n (Metric.ball (point 0 0) r) < ⊤ := by
  rw [parabolicVolume_ball _ _ hr]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (omega_lt_top n))
    (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

theorem e2_diffuse_source_proof : E2DiffuseSourceStatement := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact e2d1_ball_lt_top n _ (by norm_num)
  · have hsub : Metric.ball (point 0 0 : Space n) (1 / 16) ⊆ Metric.ball (point 0 0) (1 / 4) :=
      Metric.ball_subset_ball (by norm_num)
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_eq_left.2 hsub,
      parabolicVolume_ball _ _ (by norm_num)]
    refine pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos n).ne') ?_)
    exact pow_ne_zero _ (ENNReal.ofReal_pos.2 (by norm_num)).ne'
  · intro z r hr
    calc e2_diffuseBase n (Metric.ball z r)
        ≤ parabolicVolume n (Metric.ball z r) := Measure.restrict_le_self _
      _ = 2 * omega n * ENNReal.ofReal r ^ (n + 2) := parabolicVolume_ball z r hr

end ParabolicRectifiability.Examples
