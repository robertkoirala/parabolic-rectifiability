import ParabolicRectifiability.BetaP.Proofs.Counterexamples.TimeSliceStatements
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.TimeSliceHausdorff

/-! # Hausdorff pushforward of the time slice

`c2_timeSlice_hausdorff` proves `C2TimeSliceHausdorffStatement`, by `c2_timeSlice_hausdorff_proof`.
-/

namespace ParabolicRectifiability.BetaP

/-- **Hausdorff pushforward of the slice.** Proof: `timeSlice` is an isometry
(`dist_point` at equal times); `Isometry.map_hausdorffMeasure` gives
`ι_# H¹ = H_P^1⌊range ι` with the **same** diameter-power normalization (`hausdorffP 2 1` is
`μH[1]` on `Space 2`); restrict to `ι(E)`, measurable by
`Isometry.isClosedEmbedding` → `IsClosedEmbedding.measurableEmbedding` →
`MeasurableEmbedding.measurableSet_image`; `Measure.restrict_map` (or
`MeasurableEmbedding.restrict_map`) and `ι⁻¹(ι E) = E` (injectivity) finish. -/
theorem c2_timeSlice_hausdorff : C2TimeSliceHausdorffStatement := by
  exact c2_timeSlice_hausdorff_proof

end ParabolicRectifiability.BetaP
