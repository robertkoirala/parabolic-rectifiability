import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The tilted-line baseline estimate

Reflection pairs the two offsets. The triangle inequality followed by convexity of
`x ↦ x ^ p` on the nonnegative half-line removes the offset. The resulting power
integral gives the exact lower bound, including the endpoint `p = 1`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- Pairing opposite offsets cannot decrease the centered power cost. -/
private lemma e2_abs_rpow_pair {p : ℝ} (hp : 1 ≤ p) (x c : ℝ) :
    2 * |x| ^ p ≤ |x - c| ^ p + |x + c| ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have htri : |x| ≤ (1 / 2 : ℝ) * |x - c| + (1 / 2 : ℝ) * |x + c| := by
    have ht := abs_add_le (x - c) (x + c)
    have he : x - c + (x + c) = 2 * x := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
    linarith
  have hc := (convexOn_rpow hp).2 (abs_nonneg (x - c)) (abs_nonneg (x + c))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hc
  have hm := Real.rpow_le_rpow (abs_nonneg x) htri hp0
  linarith

private lemma e2_continuous_offset_cost {p : ℝ} (hp : 0 ≤ p) (α c : ℝ) :
    Continuous (fun s : ℝ => |α * s - c| ^ p) :=
  (Real.continuous_rpow_const hp).comp
    ((continuous_const.mul continuous_id).sub continuous_const).abs

/-- The centered cost on a symmetric interval is no larger than an offset cost. -/
private lemma e2_offset_power_integral {p h : ℝ} (hp : 1 ≤ p) (hh : 0 < h)
    (α c : ℝ) :
    2 * |α| ^ p * (h ^ (p + 1) / (p + 1)) ≤
      ∫ s in (-h)..h, |α * s - c| ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hf := e2_continuous_offset_cost hp0 α c
  have hg : Continuous (fun s : ℝ => |α * (-s) - c| ^ p) := hf.comp continuous_neg
  have hb : Continuous (fun s : ℝ => (2 * |α| ^ p) * s ^ p) :=
    continuous_const.mul (Real.continuous_rpow_const hp0)
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 h) :
      (2 * |α| ^ p) * s ^ p ≤ |α * s - c| ^ p + |α * (-s) - c| ^ p := by
    have hx := e2_abs_rpow_pair hp (α * s) c
    have he : α * (-s) - c = -(α * s + c) := by ring
    rw [he, abs_neg]
    rw [abs_mul, abs_of_nonneg hs.1, Real.mul_rpow (abs_nonneg α) hs.1] at hx
    nlinarith [hx]
  have hm := intervalIntegral.integral_mono_on (μ := volume) hh.le (hb.intervalIntegrable 0 h)
    ((hf.add hg).intervalIntegrable 0 h) hpoint
  have hi : (∫ s in (0 : ℝ)..h, s ^ p) = h ^ (p + 1) / (p + 1) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < p)), Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]
  simp only [Pi.add_apply] at hm
  rw [intervalIntegral.integral_const_mul, hi,
    intervalIntegral.integral_add (hf.intervalIntegrable (μ := volume) 0 h)
      (hg.intervalIntegrable 0 h)] at hm
  have href : (∫ s in (0 : ℝ)..h, |α * (-s) - c| ^ p) =
      ∫ s in (-h)..0, |α * s - c| ^ p := by
    simpa only [neg_zero] using
      (intervalIntegral.integral_comp_neg (fun s : ℝ => |α * s - c| ^ p) (a := 0) (b := h))
  rw [href] at hm
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-h) 0) (hf.intervalIntegrable 0 h)
  linarith

/-- The tilted-line fitting estimate, for every `p ≥ 1`. -/
theorem e2_sap_fitTilted_proof : E2sapFitTilted := by
  intro p hp h hh α c hα
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hpow : (4 : ℝ) ^ (-p) ≤ |α| ^ p := by
    have hm := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hα hp0
    simpa only [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] using hm
  have hreal : 2 * (4 : ℝ) ^ (-p) / (p + 1) * h ^ (p + 1) ≤
      ∫ s in (-h)..h, |α * s - c| ^ p := by
    calc
      _ = 2 * (4 : ℝ) ^ (-p) * (h ^ (p + 1) / (p + 1)) := by ring
      _ ≤ 2 * |α| ^ p * (h ^ (p + 1) / (p + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (div_nonneg (Real.rpow_nonneg hh.le _) (by linarith))
      _ ≤ _ := e2_offset_power_integral hp hh α c
  have hf := e2_continuous_offset_cost hp0 α c
  have hi : IntegrableOn (fun s : ℝ => |α * s - c| ^ p) (Icc (-h) h) :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hbridge : ENNReal.ofReal (∫ s in (-h)..h, |α * s - c| ^ p) =
      ∫⁻ s in Icc (-h) h, ENNReal.ofReal |α * s - c| ^ p := by
    rw [intervalIntegral.integral_of_le (by linarith : -h ≤ h),
      ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
        (fun s => Real.rpow_nonneg (abs_nonneg (α * s - c)) p))]
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0]
  exact hbridge ▸ ENNReal.ofReal_le_ofReal hreal

end ParabolicRectifiability.Examples
