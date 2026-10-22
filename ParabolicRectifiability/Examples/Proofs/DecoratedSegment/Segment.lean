import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Arclength of a horizontal segment

The length and the arclength integral formula of a horizontal segment, obtained from the
unit-speed parametrization of its horizontal level. -/

namespace ParabolicRectifiability.Examples

open MeasureTheory Set
open scoped ENNReal
open ParabolicRectifiability.BetaP (Plane horizontalSegment)

private theorem level_isometry (b : ℝ) : Isometry (fun s => e2_sapPt s b) := by
  apply isometry_iff_dist_eq.mpr
  intro s t
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, e2_sapPt, Real.dist_eq,
    Real.sqrt_sq_eq_abs]

private theorem segment_image (u v b : ℝ) :
    horizontalSegment u v b = (fun s => e2_sapPt s b) '' Icc u v := by
  ext w
  constructor
  · rintro ⟨hu, hv, hb⟩
    refine ⟨w 0, ⟨hu, hv⟩, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i <;> simp_all [e2_sapPt]
  · rintro ⟨s, hs, rfl⟩
    change u ≤ s ∧ s ≤ v ∧ b = b
    exact ⟨hs.1, hs.2, rfl⟩

/-- The level parametrization gives both length and the integral formula, including
zero-length segments and arbitrary nonnegative integrands. -/
theorem e2_sap_segment_proof (hL : E2sapLevelMeasureStatement) : E2sapSegment := by
  intro u v b huv
  have hι : MeasurableEmbedding (fun s => e2_sapPt s b) :=
    (level_isometry b).isClosedEmbedding.measurableEmbedding
  have hmeasure : μH[1].restrict (horizontalSegment u v b) =
      (volume.restrict (Icc u v)).map (fun s => e2_sapPt s b) := by
    rw [segment_image]
    exact hL b (Icc u v) measurableSet_Icc
  refine ⟨segment_image u v b, ?_, ?_⟩
  · have hmass := congrArg (fun μ : Measure Plane => μ univ) hmeasure
    simpa [Measure.map_apply hι.measurable MeasurableSet.univ, Real.volume_Icc] using hmass
  · intro f
    rw [hmeasure]
    exact hι.lintegral_map f

end ParabolicRectifiability.Examples
