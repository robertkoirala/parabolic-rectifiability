import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.TimeSliceHausdorff

/-! # Hausdorff measure of the time-zero slice of a planar set

`H_P^1(ι(S)) = H¹(S)` for every `S ⊆ ℝ²`, where `ι` is the time-zero slice map
(`e2_sb_sliceHausdorff_proof`). -/

noncomputable section
open MeasureTheory Set
namespace ParabolicRectifiability.Examples

/-- The time-slice isometry `BetaP.c2_timeSlice_isometry` preserves Hausdorff measure on every set. -/
theorem e2_sb_sliceHausdorff_proof : E2sbSliceHausdorff := by
  intro S
  simpa only [hausdorffP, Nat.cast_one] using
    BetaP.c2_timeSlice_isometry.hausdorffMeasure_image (d := 1) (Or.inl (by norm_num)) S

end ParabolicRectifiability.Examples
