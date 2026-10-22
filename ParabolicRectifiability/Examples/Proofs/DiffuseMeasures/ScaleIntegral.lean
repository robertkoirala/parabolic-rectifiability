import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements
import ParabolicRectifiability.Measure.ScaleIntegrals
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Positive-power scale integral and positive band -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability

theorem e2d6_power_integral {γ : ℝ} (hγ : 0 < γ) :
    ∫⁻ r in Ioo (0 : ℝ) 2, ENNReal.ofReal r ^ γ ∂scaleMeasure =
      ENNReal.ofReal ((2 : ℝ) ^ γ / γ) := by
  have hg : Measurable (fun r : ℝ => ENNReal.ofReal r ^ γ) := by fun_prop
  rw [setLIntegral_scaleMeasure measurableSet_Ioo (fun r hr => hr.1) _ hg]
  have h1 : ∀ r ∈ Ioo (0 : ℝ) 2, ENNReal.ofReal (1 / r) * ENNReal.ofReal r ^ γ =
      ENNReal.ofReal (r ^ (γ - 1)) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have e : ENNReal.ofReal r ^ γ = ENNReal.ofReal (r ^ γ) :=
      ENNReal.ofReal_rpow_of_pos hr0
    rw [e, ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub_one hr0.ne']
    congr 1
    rw [one_div, inv_mul_eq_div]
  rw [setLIntegral_congr_fun measurableSet_Ioo h1]
  have hint : IntervalIntegrable (fun r : ℝ => r ^ (γ - 1)) volume 0 2 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hI : ∫ r in Ioo (0 : ℝ) 2, r ^ (γ - 1) = (2 : ℝ) ^ γ / γ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
      integral_rpow (Or.inl (by linarith))]
    have : γ - 1 + 1 = γ := by ring
    rw [this, Real.zero_rpow hγ.ne']
    simp
  rw [← hI, ofReal_integral_eq_lintegral_ofReal]
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hint).mono_set
      Ioo_subset_Ioc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (Real.rpow_pos_of_pos hr.1 _).le

theorem e2d6_band :
    0 < scaleMeasure e2_diffuseBand ∧ scaleMeasure e2_diffuseBand < ⊤ := by
  refine ⟨?_, scaleMeasure_Icc_lt_top (by norm_num)⟩
  rw [scaleMeasure_apply _ measurableSet_Icc,
    inter_eq_left.mpr (show e2_diffuseBand ⊆ Ioi 0 from fun _ hx =>
      lt_of_lt_of_le (by norm_num) hx.1)]
  calc (0 : ℝ≥0∞) < ∫⁻ _r in e2_diffuseBand, ENNReal.ofReal (1 / 2) ∂volume := by
        simp [Real.volume_Icc]
        norm_num
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc fun r hr =>
        ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by linarith [hr.1]) (by linarith [hr.2]))

theorem e2_scaleIntegral_proof : E2ScaleIntegralStatement :=
  ⟨fun _ hγ => e2d6_power_integral hγ, e2d6_band⟩

end ParabolicRectifiability.Examples
