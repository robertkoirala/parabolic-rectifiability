import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Arclength on a horizontal level

Arclength on a horizontal level is the pushforward of ordinary Lebesgue measure.
The parametrization has unit speed in the Euclidean metric; Hausdorff measure
therefore transfers without a multiplicative normalization factor. -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

/-- The horizontal parametrization preserves the actual Euclidean distance. -/
private theorem sapLevel_isometry (c : ℝ) : Isometry (fun s => e2_sapPt s c) := by
  apply Isometry.of_dist_eq
  intro s t
  simp [e2_sapPt, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sqrt_sq]

/-- Hausdorff arclength on every measurable part of a horizontal line agrees with
Lebesgue measure transported by its unit-speed parametrization. -/
theorem e2_sap_levelMeasure_proof : E2sapLevelMeasureStatement := by
  intro c A _hA
  have hf := sapLevel_isometry c
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply hf.continuous.measurable hB,
    Measure.restrict_apply (hf.continuous.measurable hB)]
  rw [← hausdorffMeasure_real,
    ← hf.hausdorffMeasure_image (Or.inl (zero_le_one : (0 : ℝ) ≤ 1))]
  congr 1
  ext w
  simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨hwB, s, hsA, rfl⟩
    exact ⟨s, ⟨hwB, hsA⟩, rfl⟩
  · rintro ⟨s, ⟨hsB, hsA⟩, rfl⟩
    exact ⟨hsB, s, hsA, rfl⟩

end ParabolicRectifiability.Examples
