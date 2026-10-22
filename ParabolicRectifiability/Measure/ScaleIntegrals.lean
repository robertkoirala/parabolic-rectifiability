import ParabolicRectifiability.Measure.ScaleEnergy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Inverse-power integrals against `dr/r`

Exact values of `∫ r^(-p) dr/r` over `(a, ∞)` and over `(a, b)` for the
scale measure `scaleMeasure`, and the identity expressing the tail integral over `(2, ∞)`
as a multiple of the integral over the annulus `(1, 2)`
(`lintegral_inv_pow_tail_eq_annulus`). -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability

theorem setLIntegral_scaleMeasure {A : Set ℝ} (hA : MeasurableSet A)
    (hpos : A ⊆ Ioi 0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ r in A, g r ∂scaleMeasure = ∫⁻ r in A, ENNReal.ofReal (1 / r) * g r ∂volume := by
  unfold scaleMeasure
  rw [setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_scaleDensity hg hA,
    Measure.restrict_restrict hA, inter_eq_left.mpr hpos]
  rfl

theorem measurable_inv_pow_ofReal (p : ℕ) :
    Measurable (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ p) := by fun_prop

theorem scaleDensity_mul_inv_pow (p : ℕ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (1 / r) * (ENNReal.ofReal r)⁻¹ ^ p =
      ENNReal.ofReal (r ^ (-((p + 1 : ℕ) : ℝ))) := by
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast,
    ENNReal.ofReal_pow (inv_nonneg.mpr hr.le), ENNReal.ofReal_inv_of_pos hr,
    one_div, ENNReal.ofReal_inv_of_pos hr, pow_succ']

theorem lintegral_inv_pow_Ioi_scaleMeasure (p : ℕ) (hp : 0 < p)
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ r in Ioi a, (ENNReal.ofReal r)⁻¹ ^ p ∂scaleMeasure) =
      ENNReal.ofReal ((a ^ p)⁻¹ / (p : ℝ)) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have he : -((p + 1 : ℕ) : ℝ) < -1 := by push_cast; linarith
  have hi := integrableOn_Ioi_rpow_of_lt he ha
  calc
    _ = ∫⁻ r in Ioi a, ENNReal.ofReal (r ^ (-((p + 1 : ℕ) : ℝ))) ∂volume := by
      rw [setLIntegral_scaleMeasure measurableSet_Ioi
        (Ioi_subset_Ioi ha.le) _ (measurable_inv_pow_ofReal p)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact scaleDensity_mul_inv_pow p (ha.trans hr)
    _ = ENNReal.ofReal (∫ r : ℝ in Ioi a, r ^ (-((p + 1 : ℕ) : ℝ))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact Real.rpow_nonneg (ha.trans hr).le _
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt he ha]
      congr 1
      have heq : -((p + 1 : ℕ) : ℝ) + 1 = -(p : ℝ) := by push_cast; ring
      rw [heq, Real.rpow_neg ha.le, Real.rpow_natCast]
      ring


theorem lintegral_inv_pow_Ioo_scaleMeasure (p : ℕ) (hp : 0 < p)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ r in Ioo a b, (ENNReal.ofReal r)⁻¹ ^ p ∂scaleMeasure) =
      ENNReal.ofReal (((a ^ p)⁻¹ - (b ^ p)⁻¹) / (p : ℝ)) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hb : 0 < b := ha.trans_le hab
  have he : -((p + 1 : ℕ) : ℝ) < -1 := by push_cast; linarith
  have hi := integrableOn_Ioi_rpow_of_lt he ha
  have hj := hi.mono_set (Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a)
  calc
    _ = ∫⁻ r in Ioo a b, ENNReal.ofReal (r ^ (-((p + 1 : ℕ) : ℝ))) ∂volume := by
      rw [setLIntegral_scaleMeasure measurableSet_Ioo
        (fun r hr => ha.trans hr.1) _ (measurable_inv_pow_ofReal p)]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      exact scaleDensity_mul_inv_pow p (ha.trans hr.1)
    _ = ENNReal.ofReal (∫ r : ℝ in Ioo a b, r ^ (-((p + 1 : ℕ) : ℝ))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hj
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact Real.rpow_nonneg (ha.trans hr.1).le _
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
        ← intervalIntegral.integral_Ioi_sub_Ioi hi hab,
        integral_Ioi_rpow_of_lt he ha, integral_Ioi_rpow_of_lt he hb]
      congr 1
      have heq : -((p + 1 : ℕ) : ℝ) + 1 = -(p : ℝ) := by push_cast; ring
      rw [heq, Real.rpow_neg ha.le, Real.rpow_natCast,
        Real.rpow_neg hb.le, Real.rpow_natCast]
      ring

theorem lintegral_inv_pow_tail_eq_annulus (p : ℕ) (hp : 0 < p) :
    (∫⁻ r in Ioi (2 : ℝ), (ENNReal.ofReal r)⁻¹ ^ p ∂scaleMeasure) =
      (ENNReal.ofReal ((2 : ℝ) ^ p - 1))⁻¹ *
        ∫⁻ r in Ioo (1 : ℝ) 2, (ENNReal.ofReal r)⁻¹ ^ p ∂scaleMeasure := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hpow : 1 < (2 : ℝ) ^ p := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hp)
  have hdiff : 0 < (2 : ℝ) ^ p - 1 := sub_pos.mpr hpow
  rw [lintegral_inv_pow_Ioi_scaleMeasure p hp (by norm_num),
    lintegral_inv_pow_Ioo_scaleMeasure p hp (by norm_num) (by norm_num), one_pow,
    inv_one, ← ENNReal.ofReal_inv_of_pos hdiff,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hdiff.le)]
  congr 1
  field_simp [ne_of_gt hpr, ne_of_gt (zero_lt_one.trans hpow), ne_of_gt hdiff]

end ParabolicRectifiability
