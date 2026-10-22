import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-! # Density of the lacunary graph source

The exact ball identity reduces the parabolic density to ordinary Lebesgue
density on the parameter line, at radius `r ^ 2`. The two endpoints have
Lebesgue measure zero, and the interval length contributes the factor `2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- Lebesgue differentiation and the exact ball mass give density `2` at almost
every parameter of an arbitrary null-measurable restriction. -/
theorem e2_lacunary_densityLimit_proof :
    LacunaryBallMeasureStatement → LacunaryDensityLimitStatement := by
  intro hball ε a N hε hεsmall hd E hE hEJ
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume E] with t ht
  have hsquare : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (tendsto_id.pow 2 : Tendsto (fun r : ℝ => r ^ 2) (𝓝 0) (𝓝 (0 ^ 2))).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change (0 : ℝ) < r at hr
      change (0 : ℝ) < r ^ 2
      exact pow_pos hr 2
  have hlimit := ENNReal.Tendsto.const_mul (a := 2) (ht.comp hsquare) (Or.inl one_ne_zero)
  simp only [mul_one] at hlimit
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change (0 : ℝ) < r at hr
  simp only [Function.comp_apply]
  have hend : volume (E ∩ Ioo (t - r ^ 2) (t + r ^ 2)) =
      volume (E ∩ Metric.closedBall t (r ^ 2)) := by
    rw [Real.closedBall_eq_Icc]
    exact measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl Ioo_ae_eq_Icc)
  rw [densityRatio, hball ε a N hε hεsmall hd E hE hEJ t r hr, hend,
    Real.volume_closedBall, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hr.le, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

end ParabolicRectifiability.Examples
