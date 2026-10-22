import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The cosine increment has both a uniform bound and a frequency times time-increment
bound. Taking their minimum gives the scale kernel. Summability follows directly
from the weight hypothesis, since the kernel is bounded by its decaying branch. -/

noncomputable section

namespace ParabolicRectifiability.Examples

private theorem e2_cosine_weight_summable {a : ℕ → ℝ} {N : ℕ → ℕ}
    (hpos : ∀ j, 0 ≤ a j / Real.sqrt (N j))
    (hw : Summable (fun j => a j / Real.sqrt (N j))) (t : ℝ) :
    Summable (fun j => a j / Real.sqrt (N j) * Real.cos (N j * t)) := by
  apply Summable.of_norm_bounded hw
  intro j
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpos j)] using
    mul_le_of_le_one_right (hpos j) (Real.abs_cos_le_one (N j * t))

private theorem e2_cosine_increment_kernel {a v t s r : ℝ}
    (ha : 0 ≤ a) (hv : 0 < v) (hr : 0 < r) (hts : |t - s| ≤ r ^ 2) :
    |a / Real.sqrt v * Real.cos (v * t) - a / Real.sqrt v * Real.cos (v * s)| ≤
      (2 * r) * (a * e2_kernelAt (Real.sqrt v)⁻¹ r) := by
  have hq : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hw : 0 ≤ a / Real.sqrt v := div_nonneg ha hq.le
  have hsmall : |Real.cos (v * t) - Real.cos (v * s)| ≤ v * r ^ 2 := by
    calc
      _ ≤ |v * t - v * s| := Real.abs_cos_sub_cos_le _ _
      _ = v * |t - s| := by rw [← mul_sub, abs_mul, abs_of_pos hv]
      _ ≤ v * r ^ 2 := mul_le_mul_of_nonneg_left hts hv.le
  have hlarge : |Real.cos (v * t) - Real.cos (v * s)| ≤ 2 := by
    calc
      _ ≤ |Real.cos (v * t)| + |Real.cos (v * s)| := abs_sub _ _
      _ ≤ 2 := by linarith [Real.abs_cos_le_one (v*t), Real.abs_cos_le_one (v*s)]
  rw [← mul_sub, abs_mul, abs_of_nonneg hw]
  unfold e2_kernelAt
  rw [mul_min_of_nonneg _ _ ha, mul_min_of_nonneg _ _ (by positivity : 0 ≤ 2*r)]
  apply le_min
  · calc
      _ ≤ (a / Real.sqrt v) * (v * r ^ 2) := mul_le_mul_of_nonneg_left hsmall hw
      _ ≤ (2*r) * (a * (r / (Real.sqrt v)⁻¹)) := by
        calc
          _ = (a / Real.sqrt v) * ((Real.sqrt v)^2 * r^2) := by rw [Real.sq_sqrt hv.le]
          _ = a*r*(r*Real.sqrt v) := by field_simp [ne_of_gt hq, ne_of_gt hr]
          _ ≤ (2*r) * (a * (r / (Real.sqrt v)⁻¹)) := by
            rw [div_inv_eq_mul]
            nlinarith [mul_nonneg (mul_nonneg ha (sq_nonneg r)) hq.le]
  · calc
      _ ≤ (a / Real.sqrt v) * 2 := mul_le_mul_of_nonneg_left hlarge hw
      _ = (2*r) * (a * ((Real.sqrt v)⁻¹ / r)) := by field_simp [ne_of_gt hq, ne_of_gt hr]

/-- The modulus estimate at every positive scale, from the summable lacunary weights. -/
theorem e2_lacunary_kernelBound_proof : E2LacunaryWeightStatement → E2KernelBoundStatement := by
  intro hweight ε a N hε hdata t s r hr hts
  have hw := (hweight a N hdata).2.2.2.1
  have hapos (j : ℕ) : 0 ≤ a j := (hdata.amplitude_pos j).le
  have hqpos (j : ℕ) : 0 < Real.sqrt (N j : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hdata.frequency_pos j)
  have hwpos (j : ℕ) : 0 ≤ a j / Real.sqrt (N j) := div_nonneg (hapos j) (hqpos j).le
  have hkpos (j : ℕ) : 0 ≤ a j * e2_kernelAt (e2_invSqrtFreq N j) r := by
    unfold e2_kernelAt
    exact mul_nonneg (hapos j) (le_min (by positivity) (by positivity))
  have hk : Summable (fun j => a j * e2_kernelAt (e2_invSqrtFreq N j) r) := by
    apply Summable.of_nonneg_of_le hkpos _ (hw.div_const r)
    intro j
    calc
      _ ≤ a j * (e2_invSqrtFreq N j / r) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (hapos j)
      _ = (a j / Real.sqrt (N j)) / r := by simp only [e2_invSqrtFreq, div_eq_mul_inv]; ring
  refine ⟨hk, ?_⟩
  have ht := e2_cosine_weight_summable hwpos hw t
  have hs := e2_cosine_weight_summable hwpos hw s
  have hd : |∑' j, (a j / Real.sqrt (N j) * Real.cos (N j * t) -
      a j / Real.sqrt (N j) * Real.cos (N j * s))| ≤
      (2*r) * e2_lacunaryKernelSum a N r := by
    have h := tsum_of_norm_bounded
      (f := fun j => a j / Real.sqrt (N j) * Real.cos (N j * t) -
        a j / Real.sqrt (N j) * Real.cos (N j * s))
      (hk.mul_left (2*r)).hasSum (fun j => by
      simpa only [Real.norm_eq_abs, e2_invSqrtFreq] using e2_cosine_increment_kernel (hapos j)
        (show 0 < (N j : ℝ) by exact_mod_cast hdata.frequency_pos j) hr hts)
    simpa only [Real.norm_eq_abs, e2_lacunaryKernelSum, tsum_mul_left] using h
  rw [lacunaryFunction, lacunaryFunction, ← mul_sub, ← ht.tsum_sub hs,
    abs_mul, abs_of_nonneg hε]
  calc
    _ ≤ ε * ((2*r) * e2_lacunaryKernelSum a N r) := mul_le_mul_of_nonneg_left hd hε
    _ = _ := by ring

end ParabolicRectifiability.Examples
