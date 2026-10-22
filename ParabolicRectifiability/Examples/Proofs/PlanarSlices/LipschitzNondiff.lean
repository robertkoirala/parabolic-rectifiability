import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import Mathlib.Analysis.BoundedVariation

/-! # Hausdorff-null image of the exceptional parameters of a Lipschitz curve

Mathlib's real Rademacher theorem makes the exceptional set Lebesgue-null.
The normalization `hausdorffMeasure_real` identifies this with one-dimensional
Hausdorff nullity; the Lipschitz image estimate then preserves nullity.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane)

/-- A Lipschitz planar curve maps its nondifferentiability set to an H¹-null set. -/
theorem e2_sb_lipschitzNondiff_proof : E2sbLipschitzNondiff := by
  intro F K hF
  have hnull : volume {s | ¬ DifferentiableAt ℝ F s} = 0 := by
    exact ae_iff.mp hF.ae_differentiableAt_real
  have hH : μH[1] {s | ¬ DifferentiableAt ℝ F s} = 0 := by
    rw [hausdorffMeasure_real]
    exact hnull
  apply le_antisymm _ bot_le
  calc
    μH[1] (F '' {s | ¬ DifferentiableAt ℝ F s}) ≤
        (K : ℝ≥0∞) ^ (1 : ℝ) * μH[1] {s | ¬ DifferentiableAt ℝ F s} :=
      hF.hausdorffMeasure_image_le zero_le_one _
    _ = 0 := by rw [hH, mul_zero]

end ParabolicRectifiability.Examples
