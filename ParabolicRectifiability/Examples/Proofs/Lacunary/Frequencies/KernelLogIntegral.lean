import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! The logarithmic mass of the scale kernel is two: each side of its peak has mass one. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Examples

/-- The kernel equals its increasing branch before its positive peak. -/
private theorem kernelAt_of_le {b r : ℝ} (hb : 0 < b) (hr : 0 < r) (hrb : r ≤ b) :
    e2_kernelAt b r = r / b := by
  unfold e2_kernelAt
  apply min_eq_left
  apply (div_le_div_iff₀ hb hr).2
  nlinarith

/-- The kernel equals its decreasing branch after its positive peak. -/
private theorem kernelAt_of_ge {b r : ℝ} (hb : 0 < b) (hbr : b ≤ r) :
    e2_kernelAt b r = b / r := by
  have hr : 0 < r := hb.trans_le hbr
  unfold e2_kernelAt
  apply min_eq_right
  apply (div_le_div_iff₀ hr hb).2
  nlinarith

/-- Exact logarithmic kernel integral with the genuine scale measure `dr/r`. -/
theorem e2_kernelLogIntegral_proof : E2KernelLogIntegralStatement := by
  intro b hb
  have hlow : (∫⁻ r in Ioc 0 b, ENNReal.ofReal (e2_kernelAt b r) ∂scaleMeasure) = 1 := by
    calc
      _ = ∫⁻ r in Ioc 0 b, ENNReal.ofReal (r / b) ∂scaleMeasure := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro r hr
        change ENNReal.ofReal (e2_kernelAt b r) = ENNReal.ofReal (r / b)
        rw [kernelAt_of_le hb hr.1 hr.2]
      _ = ∫⁻ r in Ioc 0 b, ENNReal.ofReal (1 / r) * ENNReal.ofReal (r / b) := by
        exact setLIntegral_scaleMeasure measurableSet_Ioc (fun _ hr => hr.1) _ (by fun_prop)
      _ = ∫⁻ _r in Ioc 0 b, ENNReal.ofReal b⁻¹ := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro r hr
        change ENNReal.ofReal (1 / r) * ENNReal.ofReal (r / b) = ENNReal.ofReal b⁻¹
        rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hr.1.le)]
        congr 1
        field_simp [ne_of_gt hr.1, ne_of_gt hb]
      _ = 1 := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hb.le)]
        simp [hb.ne']
  have hhigh : (∫⁻ r in Ioi b, ENNReal.ofReal (e2_kernelAt b r) ∂scaleMeasure) = 1 := by
    calc
      _ = ∫⁻ r in Ioi b, ENNReal.ofReal b * (ENNReal.ofReal r)⁻¹ ^ 1 ∂scaleMeasure := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change ENNReal.ofReal (e2_kernelAt b r) =
          ENNReal.ofReal b * (ENNReal.ofReal r)⁻¹ ^ 1
        rw [kernelAt_of_ge hb hr.le, pow_one, div_eq_mul_inv,
          ENNReal.ofReal_mul hb.le, ENNReal.ofReal_inv_of_pos (hb.trans hr)]
      _ = ENNReal.ofReal b * (∫⁻ r in Ioi b, (ENNReal.ofReal r)⁻¹ ^ 1 ∂scaleMeasure) :=
        lintegral_const_mul _ (measurable_inv_pow_ofReal 1)
      _ = 1 := by
        rw [lintegral_inv_pow_Ioi_scaleMeasure 1 (by decide) hb]
        simp only [pow_one, Nat.cast_one, div_one]
        rw [← ENNReal.ofReal_mul hb.le]
        simp [hb.ne']
  rw [← Ioc_union_Ioi_eq_Ioi hb.le,
    lintegral_union measurableSet_Ioi (disjoint_left.mpr (fun _ hr hs => hr.2.not_gt hs)),
    hlow, hhigh]
  norm_num

end ParabolicRectifiability.Examples
