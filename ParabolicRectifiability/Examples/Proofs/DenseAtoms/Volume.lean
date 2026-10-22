import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements

/-! The open cylinder inside the closed cylinder has positive ambient volume. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

theorem e2_dense_volume_proof : E2DenseVolumeStatement := by
  intro n
  have hpos : 0 < parabolicVolume n (Metric.ball (point 0 0) (1 / 4)) := by
    rw [parabolicVolume_ball _ _ (by norm_num)]
    refine pos_iff_ne_zero.2 (mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos n).ne') ?_)
    exact pow_ne_zero _ (ENNReal.ofReal_pos.2 (by norm_num)).ne'
  exact hpos.trans_le (measure_mono Metric.ball_subset_closedBall)

end ParabolicRectifiability.Examples
