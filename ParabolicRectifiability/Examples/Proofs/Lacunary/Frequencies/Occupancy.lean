import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Eventual occupancy of lacunary period windows

A density point has density ratio tending to one along every positive sequence
of radii tending to zero. Frequency growth makes the period half-lengths such
a sequence. The null boundary of each interval permits arbitrary sets `E`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

/-- At every density point the shrinking period windows eventually have the
required occupancy and fit inside any prescribed positive scale. -/
theorem e2_lacunary_occupancy_proof : E2OccupancyStatement := by
  intro a N hd E t ht R hR
  have hN : StrictMono N := strictMono_nat_of_lt_succ fun j => by
    have hp := hd.frequency_pos j
    have hg := hd.frequency_growth j
    omega
  let ρ : ℕ → ℝ := fun j => Real.pi / N j
  have hρpos (j : ℕ) : 0 < ρ j :=
    div_pos Real.pi_pos (by exact_mod_cast hd.frequency_pos j)
  have hρ : Tendsto ρ atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat Real.pi).comp hN.tendsto_atTop
  have hρright : Tendsto ρ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hρ
      (Eventually.of_forall hρpos)
  have hratio := ht.comp hρright
  have hocc : ∀ᶠ j in atTop,
      ENNReal.ofReal (11 / 12 : ℝ) ≤
        volume (E ∩ Metric.closedBall t (ρ j)) / volume (Metric.closedBall t (ρ j)) := by
    apply (hratio.eventually (eventually_gt_nhds (show ENNReal.ofReal (11 / 12 : ℝ) < 1 by
      norm_num))).mono
    exact fun _ h => h.le
  have hradius : Tendsto (fun j => 2 * e2_plateauRadius N j) atTop (𝓝 0) := by
    simpa [e2_plateauRadius, ρ] using
      (tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp hρ) :
        Tendsto (fun j => (2 : ℝ) * Real.sqrt (ρ j)) atTop (𝓝 (2 * Real.sqrt 0)))
  have hsmall : ∀ᶠ j in atTop, 2 * e2_plateauRadius N j < R :=
    hradius.eventually (eventually_lt_nhds hR)
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hocc.and hsmall)
  refine ⟨j₀, fun j hj => ?_⟩
  obtain ⟨ho, hs⟩ := hj₀ j hj
  refine ⟨?_, hs⟩
  have hv : volume (Metric.closedBall t (ρ j)) = ENNReal.ofReal (2 * ρ j) := by
    rw [Real.volume_closedBall]
  have hv0 : volume (Metric.closedBall t (ρ j)) ≠ 0 := by
    rw [hv]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (mul_pos (by norm_num) (hρpos j)))
  have hvtop : volume (Metric.closedBall t (ρ j)) ≠ ⊤ := by
    rw [hv]
    exact ENNReal.ofReal_ne_top
  have hm := mul_le_mul' ho (le_refl (volume (Metric.closedBall t (ρ j))))
  rw [ENNReal.div_mul_cancel hv0 hvtop, hv, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 11 / 12)] at hm
  have hae : E ∩ Ioo (t - ρ j) (t + ρ j) =ᵐ[volume]
      E ∩ Metric.closedBall t (ρ j) := by
    rw [Real.closedBall_eq_Icc]
    exact ae_eq_set_inter Filter.EventuallyEq.rfl Ioo_ae_eq_Icc
  have heq := measure_congr hae
  rw [← heq] at hm
  simpa [e2_periodWindow, ρ, mul_div_assoc] using hm

end ParabolicRectifiability.Examples
