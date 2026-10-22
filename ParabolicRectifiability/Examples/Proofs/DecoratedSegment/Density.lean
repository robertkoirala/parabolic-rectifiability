import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Exact density of a finite-length countable union of horizontal segments

The supplied level decomposition identifies its total mass with the sum of the
one-dimensional level masses. The supplied almost-everywhere and pointwise
level estimates then give density two on each level, and hence on their measure sum.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane horizontalSegment planarDensityRatio)

private theorem e2_sapPt_density_measurableEmbedding (c : ℝ) :
    MeasurableEmbedding (fun s : ℝ => e2_sapPt s c) := by
  apply Continuous.measurableEmbedding
  · unfold e2_sapPt
    fun_prop
  · intro s t h
    simpa only [e2_sapPt, Matrix.cons_val_zero] using congrArg (fun z : Plane => z 0) h

/-- The general finite-length density conclusion, from the level decomposition
and the pointwise and almost-everywhere level estimates. -/
theorem e2_sap_density_proof (hLv : E2sapLevels) (hP : E2sapLevelPoint)
    (hAE : E2sapLevelAE) : E2sapDensity := by
  intro I u v b hfin
  obtain ⟨c, A, hc, hA, hdecomp⟩ := hLv I u v b
  have htotal : e2_sapLevelMeasure c A Set.univ = ∑' k, volume (A k) := by
    rw [e2_sapLevelMeasure, Measure.sum_apply _ MeasurableSet.univ]
    apply tsum_congr
    intro k
    rw [Measure.map_apply (e2_sapPt_density_measurableEmbedding (c k)).measurable
      MeasurableSet.univ]
    simp only [Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hmass : ∑' k, volume (A k) ≠ ⊤ := by
    rw [← htotal, ← hdecomp]
    simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hfin
  rw [hdecomp]
  rw [e2_sapLevelMeasure, Measure.ae_sum_eq, Filter.eventually_iSup]
  intro m
  apply (e2_sapPt_density_measurableEmbedding (c m)).ae_map_iff.mpr
  filter_upwards [hAE A hA hmass m] with s hs
  exact hP c A hc hA m s hs.1 hs.2.1 hs.2.2

end ParabolicRectifiability.Examples
