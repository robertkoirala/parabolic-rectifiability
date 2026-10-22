import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Hausdorff measure of snowflaked time

Both coordinate maps have exact Hölder constant one. Applying mathlib's
Hausdorff image inequality with exponents `1 / 2` and `2` identifies the
unnormalized two-dimensional measure on `Time` with length on the real line.
The image inequality holds for arbitrary sets, including nonmeasurable ones.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

/-- The square-root time metric has two-dimensional Hausdorff measure equal
to Lebesgue outer measure, with no set measurability or finiteness assumption. -/
theorem e2_time_hausdorff_proof : E2TimeHausdorffStatement := by
  intro E
  have hf : HolderWith 1 (1 / 2)
      (Metric.Snowflaking.toSnowflaking : ℝ ≃ Time) := by
    intro x y
    simp [Metric.Snowflaking.edist_toSnowflaking_toSnowflaking]
  have hg : HolderWith 1 2
      (Metric.Snowflaking.ofSnowflaking : Time ≃ ℝ) := by
    intro x y
    simp [Metric.Snowflaking.edist_ofSnowflaking_ofSnowflaking]
  have hforward := (hf.holderOnWith E).hausdorffMeasure_image_le
    (by norm_num) (d := 2) (by norm_num)
  have hbackward := (hg.holderOnWith
      ((Metric.Snowflaking.toSnowflaking : ℝ ≃ Time) '' E)).hausdorffMeasure_image_le
    (by norm_num) (d := 1) (by norm_num)
  norm_num at hforward hbackward
  exact le_antisymm hforward hbackward

end ParabolicRectifiability.Examples
