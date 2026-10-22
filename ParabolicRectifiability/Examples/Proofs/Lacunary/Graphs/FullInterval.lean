import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements

/-! # Full-interval regularity of the lacunary source

The ball identity transfers the stationary interval-length bounds with constant two.
At an interior parameter, the full time window is eventually contained in the source
interval, so its length is exactly twice the squared radius.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The full-interval implication, using the length statement `E2StationaryLengthStatement`. -/
theorem e2_lacunary_fullInterval_proof :
    LacunaryBallMeasureStatement → E2StationaryLengthStatement →
      LacunaryFullIntervalStatement := by
  intro hball hlength ε a N hε hε' hd
  have hJ : NullMeasurableSet lacunaryInterval volume := measurableSet_Icc.nullMeasurableSet
  have hmass := hball ε a N hε hε' hd lacunaryInterval hJ (Subset.refl _)
  constructor
  · refine ⟨2, by norm_num, ?_⟩
    intro t ht r hr hr1
    rw [hmass t r hr]
    simpa only [lacunaryInterval, inter_comm] using
      hlength t r ht hr (by linarith)
  · intro t ht
    have hδ : 0 < min (1 + t) (1 - t) := lt_min (by linarith [ht.1]) (by linarith [ht.2])
    have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 < min (1 + t) (1 - t) :=
      (continuousAt_id.pow 2).eventually (gt_mem_nhds (by simpa using hδ))
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hrpos
    have hr0 : 0 < r := hrpos
    have hwindow : Ioo (t - r ^ 2) (t + r ^ 2) ⊆ lacunaryInterval := by
      intro s hs
      constructor
      · have := (lt_min_iff.mp hr).1
        linarith [hs.1]
      · have := (lt_min_iff.mp hr).2
        linarith [hs.2]
    rw [densityRatio, hmass t r hr0, inter_eq_right.mpr hwindow, Real.volume_Ioo]
    rw [show t + r ^ 2 - (t - r ^ 2) = 2 * r ^ 2 by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow hr0.le]
    norm_num only [ENNReal.ofReal_ofNat]
    exact ENNReal.mul_div_cancel_right
      (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hr0))) (by finiteness)

end ParabolicRectifiability.Examples
