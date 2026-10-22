import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Reciprocal square-root decay of lacunary frequencies -/

namespace ParabolicRectifiability.Examples

/-- Frequency growth by a factor of sixteen gives reciprocal square-root decay
by a factor of four. Positivity permits inversion of the square-root bound. -/
theorem e2_lacunary_invSqrtDecay_proof : E2InvSqrtDecayStatement := by
  intro a N hd j
  have hj : (0 : ℝ) < N j := by exact_mod_cast hd.frequency_pos j
  have hj' : (0 : ℝ) < N (j + 1) := by exact_mod_cast hd.frequency_pos (j + 1)
  have hgrowth : (16 : ℝ) * N j ≤ N (j + 1) := by
    exact_mod_cast hd.frequency_growth j
  have hsqrt : (4 : ℝ) * Real.sqrt (N j : ℝ) ≤ Real.sqrt (N (j + 1) : ℝ) := by
    calc
      (4 : ℝ) * Real.sqrt (N j : ℝ) = Real.sqrt ((16 : ℝ) * N j) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
      _ ≤ Real.sqrt (N (j + 1) : ℝ) := Real.sqrt_le_sqrt hgrowth
  have hinv := (inv_le_inv₀ (Real.sqrt_pos.2 hj')
    (mul_pos (by norm_num : (0 : ℝ) < 4) (Real.sqrt_pos.2 hj))).2 hsqrt
  calc
    (Real.sqrt (N (j + 1) : ℝ))⁻¹ ≤ ((4 : ℝ) * Real.sqrt (N j : ℝ))⁻¹ := hinv
    _ = (Real.sqrt (N j : ℝ))⁻¹ / 4 := by rw [mul_inv_rev, div_eq_mul_inv]

end ParabolicRectifiability.Examples
