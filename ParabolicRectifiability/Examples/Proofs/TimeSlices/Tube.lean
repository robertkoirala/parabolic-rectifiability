import ParabolicRectifiability.Examples.Statements.Reductions

/-! # The time-slice tube identity

The coordinate preimage of the parabolic tube
around `A × {t₀}` is the product `A_r × (t₀ - r², t₀ + r²)` (valid for every set `A`,
including `∅`); then `parabolicVolume_apply`, `Measure.prod_prod` and `Real.volume_Ioo`.
No measurability or finiteness of `A` is used. -/

noncomputable section

namespace ParabolicRectifiability.Examples

open MeasureTheory Set
open scoped ENNReal

/-- The tube identity `TimeSliceTubeStatement`. -/
theorem e2_timeSlice_tube_proof : TimeSliceTubeStatement := by
  intro n _ A t₀ r hr
  have hpre : (coordinatesMeasurableEquiv n).symm ⁻¹'
        {z : Space n | Metric.infEDist z ((fun y : Spatial n => point y t₀) '' A) <
          ENNReal.ofReal r} =
      {y : Spatial n | Metric.infEDist y A < ENNReal.ofReal r} ×ˢ
        Ioo (t₀ - r ^ 2) (t₀ + r ^ 2) := by
    ext ⟨x, t⟩
    simp only [mem_preimage, coordinatesMeasurableEquiv_symm_apply, mem_ofPred_eq, mem_prod,
      mem_Ioo]
    rw [Metric.infEDist_lt_iff, Metric.infEDist_lt_iff]
    have key : ∀ y : Spatial n, edist (point x t) (point y t₀) < ENNReal.ofReal r ↔
        ‖x - y‖ < r ∧ |t - t₀| < r ^ 2 := by
      intro y
      rw [edist_lt_ofReal, dist_point, max_lt_iff, Real.sqrt_lt (abs_nonneg _) hr.le]
    have hA : ∀ y : Spatial n, edist x y < ENNReal.ofReal r ↔ ‖x - y‖ < r := by
      intro y
      rw [edist_lt_ofReal, dist_eq_norm]
    simp only [mem_image, exists_exists_and_eq_and, key, hA, abs_lt]
    constructor
    · rintro ⟨y, hy, h1, h2, h3⟩
      exact ⟨⟨y, hy, h1⟩, by linarith, by linarith⟩
    · rintro ⟨⟨y, hy, h1⟩, h2, h3⟩
      exact ⟨y, hy, h1, by linarith, by linarith⟩
  rw [parabolicVolume_apply, hpre]
  change ((volume : Measure (Spatial n)).prod (volume : Measure ℝ)) _ = _
  rw [Measure.prod_prod, Real.volume_Ioo, mul_comm]
  congr 2
  ring

end ParabolicRectifiability.Examples
