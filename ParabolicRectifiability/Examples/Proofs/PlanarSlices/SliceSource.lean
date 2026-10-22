import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import Mathlib.MeasureTheory.Measure.Regular

/-! # The time-zero image of a finite planar measure

For every finite measure `ν` on `ℝ²`, the pushforward `ι_#ν` under the time-zero slice map is
finite on compacts and inner regular (`e2_sb_sliceSource_proof`). -/

noncomputable section
open MeasureTheory
namespace ParabolicRectifiability.Examples
open BetaP

/-- A finite planar source has a locally Radon time-zero pushforward. -/
theorem e2_sb_sliceSource_proof : E2sbSliceSource := by
  intro ν hν
  let : IsFiniteMeasure ν := hν
  let : IsFiniteMeasure (ν.map timeSlice) := ν.isFiniteMeasure_map timeSlice
  refine ⟨inferInstance, ?_⟩
  exact Measure.InnerRegular.map_of_continuous
    (continuous_point.comp (continuous_id.prodMk continuous_const))

end ParabolicRectifiability.Examples
