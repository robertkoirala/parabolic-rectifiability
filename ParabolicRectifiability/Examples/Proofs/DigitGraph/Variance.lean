import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Two-height variance estimate

The two-height variance estimate, with an arbitrary affine offset (`e2_variance_proof`): if a
`{0,1}`-valued `β` on `[-h,h]` has mean `δ ∈ (0, 1/2]` up to discrepancy `2δP` and covariance with
`X` at most `4δPh`, where `P ≤ 2^{-10} h`, then `∫_{-h}^{h} (aX + bhβ(X) - c)^2 dX ≥ δh^3/4` for
every unit `(a,b)` and every `c`. -/

noncomputable section
open MeasureTheory Set

namespace ParabolicRectifiability.Examples

private theorem variance_algebra (h δ P m t a b c : ℝ)
    (hh : 0 < h) (hδ : 0 < δ) (hδu : δ ≤ 1 / 2) (hP : 0 < P)
    (hscale : 2 ^ 10 * P ≤ h)
    (hmlo : -(2 * δ * P) ≤ 2 * h * m - 2 * h * δ)
    (hmhi : 2 * h * m - 2 * h * δ ≤ 2 * δ * P)
    (htlo : -(4 * δ * P * h) ≤ 2 * h * t)
    (hthi : 2 * h * t ≤ 4 * δ * P * h)
    (hab : a ^ 2 + b ^ 2 = 1) :
    δ * h ^ 3 / 4 ≤
      2 * h * (a ^ 2 * h ^ 2 / 3 + b ^ 2 * h ^ 2 * m * (1 - m) +
        2 * a * b * h * t + (c - b * h * m) ^ 2) := by
  have hPh : 16 * P ≤ h := by norm_num at hscale; linarith
  have hδPh : 16 * δ * P ≤ δ * h := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hPh)]
  have hm₁ : 15 * δ / 16 ≤ m := by nlinarith
  have hm₂ : m ≤ 17 * δ / 16 := by nlinarith
  have hm₃ : 15 / 32 ≤ 1 - m := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hvar : δ / 4 ≤ m * (1 - m) := by
    have := mul_le_mul hm₁ hm₃ (by norm_num : (0 : ℝ) ≤ 15 / 32) hm0
    nlinarith
  have ht₁ : -(δ * h / 4) ≤ t := by nlinarith
  have ht₂ : t ≤ δ * h / 4 := by nlinarith
  have htq : 4 * t ^ 2 ≤ δ * h ^ 2 / 8 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht₂) (by linarith : 0 ≤ δ * h / 4 + t),
      mul_nonneg (mul_nonneg hδ.le (by linarith : 0 ≤ 1 / 2 - δ)) (sq_nonneg h)]
  have hv := mul_le_mul_of_nonneg_left hvar (mul_nonneg (sq_nonneg b) (sq_nonneg h))
  have ht := mul_le_mul_of_nonneg_left htq (sq_nonneg b)
  have ha := mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg h))
    (by linarith : 0 ≤ 1 / 12 - δ / 8)
  have hn : δ * h ^ 2 / 8 ≤ a ^ 2 * h ^ 2 / 3 + b ^ 2 * h ^ 2 * m * (1 - m) +
      2 * a * b * h * t + (c - b * h * m) ^ 2 := by
    nlinarith [sq_nonneg (a * h / 2 + 2 * b * t), sq_nonneg (c - b * h * m),
      congrArg (fun x : ℝ => x * δ * h ^ 2 / 8) hab]
  nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hn)]

/-- The binary variance and the controlled covariance force a uniform line cost. -/
theorem e2_variance_proof : E2Variance := by
  intro h δ P β hh hδ hδu hP hscale hβ hbit hmean hcov a b c hab
  have hiβ : IntervalIntegrable β volume (-h) h := by
    apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun hβ.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by rcases hbit x with hx | hx <;> simp [hx]
  have hiX : IntervalIntegrable (fun x : ℝ => x) volume (-h) h :=
    continuous_id.intervalIntegrable _ _
  have hiX2 : IntervalIntegrable (fun x : ℝ => x ^ 2) volume (-h) h :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hiXB : IntervalIntegrable (fun x => x * β x) volume (-h) h :=
    hiβ.continuousOn_mul continuous_id.continuousOn
  have hX : (∫ x in (-h)..h, x) = 0 := by rw [integral_id]; ring
  have hlinear : (∫ x in (-h)..h, (-2 * a * c) * x) = 0 := by
    rw [intervalIntegral.integral_const_mul, hX, mul_zero]
  have hX2 : (∫ x in (-h)..h, x ^ 2) = 2 * h ^ 3 / 3 := by rw [integral_pow]; ring
  have hcross : (∫ x in (-h)..h, x * (β x - δ)) = ∫ x in (-h)..h, x * β x := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hiXB (hiX.mul_const δ),
      intervalIntegral.integral_mul_const, hX]
    ring
  let m : ℝ := (∫ x in (-h)..h, β x) / (2 * h)
  let t : ℝ := (∫ x in (-h)..h, x * β x) / (2 * h)
  have hm : (∫ x in (-h)..h, β x) = 2 * h * m := by dsimp [m]; field_simp
  have ht : (∫ x in (-h)..h, x * β x) = 2 * h * t := by dsimp [t]; field_simp
  have hexpand : (∫ x in (-h)..h, (a * x + b * h * β x - c) ^ 2) =
      2 * h * (a ^ 2 * h ^ 2 / 3 + b ^ 2 * h ^ 2 * m * (1 - m) +
        2 * a * b * h * t + (c - b * h * m) ^ 2) := by
    calc
      _ = ∫ x in (-h)..h, a ^ 2 * x ^ 2 + (2 * a * b * h) * (x * β x) +
          (b ^ 2 * h ^ 2 - 2 * b * h * c) * β x + (-2 * a * c) * x + c ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rcases hbit x with hb | hb <;> rw [hb] <;> ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (((hiX2.const_mul _).add (hiXB.const_mul _)).add (hiβ.const_mul _) |>.add (hiX.const_mul _))
          intervalIntegrable_const]
        rw [intervalIntegral.integral_add
          (((hiX2.const_mul _).add (hiXB.const_mul _)).add (hiβ.const_mul _)) (hiX.const_mul _)]
        rw [intervalIntegral.integral_add ((hiX2.const_mul _).add (hiXB.const_mul _)) (hiβ.const_mul _)]
        rw [intervalIntegral.integral_add (hiX2.const_mul _) (hiXB.const_mul _)]
        rw [hlinear]
        simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
          hX2, hm, ht, smul_eq_mul]
        ring
  rw [hexpand]
  rw [hm, abs_le] at hmean
  rw [hcross, ht, abs_le] at hcov
  exact variance_algebra h δ P m t a b c hh hδ hδu hP hscale hmean.1 hmean.2
    hcov.1 hcov.2 hab

end ParabolicRectifiability.Examples
