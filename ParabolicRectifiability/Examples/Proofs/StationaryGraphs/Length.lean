import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements

/-! # Length of the stationary time window

For `t ∈ [-1,1]` and `0 < r ≤ 2`,
`r²/2 ≤ |(t-r², t+r²) ∩ [-1,1]| ≤ 2r²`. Upper bound: monotonicity and `Real.volume_Ioo`.
Lower bound: the open interval `(max (t-r²) (-1), min (t+r²) 1)` lies inside, and its length
is at least `r²/2` by cases on the two `min`/`max`. -/

noncomputable section

namespace ParabolicRectifiability.Examples

open MeasureTheory Set
open scoped ENNReal

theorem e2_stationary_length_proof : E2StationaryLengthStatement := by
  intro t r ht hr hr2
  obtain ⟨ht1, ht2⟩ := ht
  have hr4 : r ^ 2 ≤ 4 := by nlinarith
  have hr0 : 0 < r ^ 2 := by positivity
  constructor
  · have hsub : Ioo (max (t - r ^ 2) (-1)) (min (t + r ^ 2) 1) ⊆
        Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hx
      rw [max_lt_iff] at h1
      rw [lt_min_iff] at h2
      exact ⟨⟨h1.1, h2.1⟩, h1.2.le, h2.2.le⟩
    have hlen : r ^ 2 / 2 ≤ min (t + r ^ 2) 1 - max (t - r ^ 2) (-1) := by
      rw [min_def, max_def]
      split_ifs <;> linarith
    calc ENNReal.ofReal (r ^ 2 / 2)
        ≤ ENNReal.ofReal (min (t + r ^ 2) 1 - max (t - r ^ 2) (-1)) :=
          ENNReal.ofReal_le_ofReal hlen
      _ = volume (Ioo (max (t - r ^ 2) (-1)) (min (t + r ^ 2) 1)) := (Real.volume_Ioo).symm
      _ ≤ _ := measure_mono hsub
  · calc volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1)
        ≤ volume (Ioo (t - r ^ 2) (t + r ^ 2)) := measure_mono inter_subset_left
      _ = ENNReal.ofReal (2 * r ^ 2) := by
          rw [Real.volume_Ioo]; congr 1; ring

end ParabolicRectifiability.Examples
