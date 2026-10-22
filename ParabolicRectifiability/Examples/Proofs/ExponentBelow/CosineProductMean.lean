import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Mean of a product of two cosines

For `0 ≤ μ`, `0 < ν` and `16 μ ≤ ν`, the integral of `cos (μ t) cos (ν t)` over any interval
has absolute value at most `3 / ν`.
-/

noncomputable section

open MeasureTheory

namespace ParabolicRectifiability.Examples

private theorem e2_cosProduct_toSum (μ ν t : ℝ) :
    Real.cos (μ * t) * Real.cos (ν * t) =
      (Real.cos ((ν - μ) * t) + Real.cos ((ν + μ) * t)) / 2 := by
  calc
    Real.cos (μ * t) * Real.cos (ν * t) =
        Real.cos (ν * t) * Real.cos (μ * t) := by ring
    _ = (Real.cos (ν * t - μ * t) + Real.cos (ν * t + μ * t)) / 2 := by
      rw [Real.cos_sub, Real.cos_add]
      ring
    _ = (Real.cos ((ν - μ) * t) + Real.cos ((ν + μ) * t)) / 2 := by
      rw [show ν * t - μ * t = (ν - μ) * t by ring,
        show ν * t + μ * t = (ν + μ) * t by ring]

private theorem e2_cosIntegral_bound {w a b : ℝ} (hw : 0 < w) :
    |∫ t in a..b, Real.cos (w * t)| ≤ 2 / w := by
  rw [intervalIntegral.integral_comp_mul_left _ (ne_of_gt hw), integral_cos]
  simp only [smul_eq_mul]
  have hsin : |Real.sin (w * b) - Real.sin (w * a)| ≤ 2 := by
    have hb := abs_le.mp (Real.abs_sin_le_one (w * b))
    have ha := abs_le.mp (Real.abs_sin_le_one (w * a))
    rw [abs_le]
    constructor <;> nlinarith
  calc
    |w⁻¹ * (Real.sin (w * b) - Real.sin (w * a))| =
        w⁻¹ * |Real.sin (w * b) - Real.sin (w * a)| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hw)]
    _ ≤ w⁻¹ * 2 := mul_le_mul_of_nonneg_left hsin (le_of_lt (inv_pos.mpr hw))
    _ = 2 / w := by ring

theorem e2_cosProduct_mean_proof : E2CosProductMeanStatement := by
  intro μ ν hμ hν hfreq α ℓ
  have hgap : 15 * ν / 16 ≤ ν - μ := by nlinarith
  have hgapPos : 0 < ν - μ := lt_of_lt_of_le (by positivity) hgap
  have hsumPos : 0 < ν + μ := by linarith
  have hgapInv : 1 / (ν - μ) ≤ 16 / (15 * ν) := by
    have hden : 0 < 15 * ν / 16 := by positivity
    have hrewrite : 16 / (15 * ν) = 1 / (15 * ν / 16) := by
      field_simp [ne_of_gt hν]
    rw [hrewrite, one_div_le_one_div hgapPos hden]
    exact hgap
  have hsumInv : 1 / (ν + μ) ≤ 1 / ν :=
    one_div_le_one_div_of_le hν (by linarith)
  have hconstant : 16 / (15 * ν) + 1 / ν ≤ 3 / ν := by
    rw [show 16 / (15 * ν) = (16 / 15) / ν by field_simp [ne_of_gt hν]]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num : (16 : ℝ) / 15 + 1 ≤ 3)
      (le_of_lt hν)
  have hI1 : IntervalIntegrable (fun t : ℝ => Real.cos ((ν - μ) * t))
      volume α (α + ℓ) := by
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => Real.cos ((ν + μ) * t))
      volume α (α + ℓ) := by
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hrewrite :
      (∫ t in α..α + ℓ, Real.cos (μ * t) * Real.cos (ν * t)) =
        ((∫ t in α..α + ℓ, Real.cos ((ν - μ) * t)) +
          ∫ t in α..α + ℓ, Real.cos ((ν + μ) * t)) / 2 := by
    calc
      (∫ t in α..α + ℓ, Real.cos (μ * t) * Real.cos (ν * t)) =
          ∫ t in α..α + ℓ,
            (Real.cos ((ν - μ) * t) + Real.cos ((ν + μ) * t)) / 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact e2_cosProduct_toSum μ ν t
      _ = ((∫ t in α..α + ℓ, Real.cos ((ν - μ) * t)) +
          ∫ t in α..α + ℓ, Real.cos ((ν + μ) * t)) / 2 := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add hI1 hI2]
  calc
    |∫ t in α..α + ℓ, Real.cos (μ * t) * Real.cos (ν * t)| =
        |((∫ t in α..α + ℓ, Real.cos ((ν - μ) * t)) +
          ∫ t in α..α + ℓ, Real.cos ((ν + μ) * t)) / 2| := by rw [hrewrite]
    _ ≤ (|∫ t in α..α + ℓ, Real.cos ((ν - μ) * t)| +
          |∫ t in α..α + ℓ, Real.cos ((ν + μ) * t)|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ (2 / (ν - μ) + 2 / (ν + μ)) / 2 :=
      div_le_div_of_nonneg_right
        (add_le_add (e2_cosIntegral_bound hgapPos) (e2_cosIntegral_bound hsumPos))
        (by norm_num)
    _ = 1 / (ν - μ) + 1 / (ν + μ) := by ring
    _ ≤ 16 / (15 * ν) + 1 / ν := add_le_add hgapInv hsumInv
    _ ≤ 3 / ν := hconstant

end ParabolicRectifiability.Examples
