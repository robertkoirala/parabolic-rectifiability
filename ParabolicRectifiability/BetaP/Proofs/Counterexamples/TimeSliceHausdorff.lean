import ParabolicRectifiability.BetaP.Proofs.Counterexamples.TimeSliceStatements

/-! # Hausdorff pushforward of the time slice (`c2_timeSlice_hausdorff`)

Proof: `timeSlice` is an isometry (`dist_point` at equal times);
`Isometry.map_hausdorffMeasure`; the image of a measurable set is measurable
(closed embedding); `MeasurableEmbedding.restrict_map`; injectivity.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.BetaP

theorem c2_timeSlice_isometry : Isometry timeSlice := by
  refine Isometry.of_dist_eq fun x y => ?_
  simp [timeSlice, dist_point, dist_eq_norm]

theorem c2_timeSlice_hausdorff_proof : C2TimeSliceHausdorffStatement := by
  intro E hE
  have hι := c2_timeSlice_isometry
  have hme : MeasurableEmbedding timeSlice := hι.isClosedEmbedding.measurableEmbedding
  calc (μH[1].restrict E).map timeSlice
      = (μH[1].restrict (timeSlice ⁻¹' (timeSlice '' E))).map timeSlice := by
        rw [hι.injective.preimage_image]
    _ = ((μH[1] : Measure Plane).map timeSlice).restrict (timeSlice '' E) :=
        (hme.restrict_map _ _).symm
    _ = ((hausdorffP 2 1).restrict (range timeSlice)).restrict (timeSlice '' E) := by
        rw [hι.map_hausdorffMeasure (Or.inl (by norm_num))]
        simp [hausdorffP]
    _ = (hausdorffP 2 1).restrict (timeSlice '' E) := by
        rw [Measure.restrict_restrict (hme.measurableSet_image.2 hE),
          inter_eq_left.2 (image_subset_range _ _)]

end ParabolicRectifiability.BetaP
