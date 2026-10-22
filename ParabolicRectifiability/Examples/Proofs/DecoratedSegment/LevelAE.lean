import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Almost-everywhere differentiation on countably many levels

Finite summed level measure makes the full sum of indicators finite almost everywhere.
Its tails therefore tend to zero. Each tail is measurable with finite integral, so the
Besicovitch Vitali differentiation theorem applies; countability gives all tail limits
simultaneously. This is the one-dimensional input of the density computation
`e2_sap_density_proof`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- Lebesgue density and all tail differentiation limits hold almost everywhere on every
level, with the genuine closed-ball averages and the original finite-total-mass hypothesis. -/
theorem e2_sap_levelAE_proof : E2sapLevelAE := by
  intro A hA hmass m
  let f : ℕ → ℝ → ℝ≥0∞ := fun k => (A k).indicator (fun _ => 1)
  have hf (k : ℕ) : Measurable (f k) := measurable_const.indicator (hA k)
  have hsum_meas : Measurable (fun s => ∑' k, f k s) := .tsum hf
  have hsum_int : (∫⁻ s, ∑' k, f k s) = ∑' k, volume (A k) := by
    rw [lintegral_tsum (fun k => (hf k).aemeasurable)]
    apply tsum_congr
    intro k
    exact (lintegral_indicator_const (hA k) 1).trans (one_mul _)
  have hsum_fin : (∫⁻ s, ∑' k, f k s) ≠ ⊤ := by
    rw [hsum_int]
    exact hmass
  have htail_meas (N : ℕ) : Measurable (e2_sapTail A N) :=
    .tsum (fun k => hf (N + 1 + k))
  have htail_le (N : ℕ) (s : ℝ) : e2_sapTail A N s ≤ ∑' k, f k s :=
    ENNReal.tsum_comp_le_tsum_of_injective
      (show Function.Injective (fun k : ℕ => N + 1 + k) from
        fun _ _ h => Nat.add_left_cancel h) (fun k => f k s)
  have htail_fin (N : ℕ) : (∫⁻ s, e2_sapTail A N s) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum_fin (lintegral_mono (htail_le N))
  have hdiff (N : ℕ) : ∀ᵐ s ∂(volume : Measure ℝ),
      Tendsto (fun r => (∫⁻ u in Metric.closedBall s r, e2_sapTail A N u) /
        volume (Metric.closedBall s r)) (𝓝[>] 0) (𝓝 (e2_sapTail A N s)) := by
    filter_upwards [(Besicovitch.vitaliFamily (volume : Measure ℝ)).ae_tendsto_lintegral_div
      (htail_meas N).aemeasurable (htail_fin N)] with s hs
    exact hs.comp (Besicovitch.tendsto_filterAt volume s)
  have hall := ae_all_iff.mpr hdiff
  have hzero : ∀ᵐ s ∂(volume : Measure ℝ),
      Tendsto (fun N => e2_sapTail A N s) atTop (𝓝 0) := by
    filter_upwards [ae_lt_top hsum_meas hsum_fin] with s hs
    have h := (ENNReal.tendsto_sum_nat_add (fun k => f k s) hs.ne).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, e2_sapTail, f, Nat.add_comm] using h
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume (A m),
    ae_restrict_of_ae hall, ae_restrict_of_ae hzero] with s hd hl hz
  exact ⟨hd, hl, hz⟩

end ParabolicRectifiability.Examples
