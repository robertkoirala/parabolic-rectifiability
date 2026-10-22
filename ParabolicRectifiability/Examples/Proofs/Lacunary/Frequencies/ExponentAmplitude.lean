import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # Admissibility of the exponent amplitudes

The amplitudes `a_j = c₀ / (√(j+1) log(j+2))` satisfy the admissibility conditions
(`e2_exponentAmplitude_admissible_proof`). -/

noncomputable section

namespace ParabolicRectifiability.Examples

/-- Proof of the admissibility of the exponent amplitudes
`a_j = c₀ / (√(j+1) log(j+2))`. -/
theorem e2_exponentAmplitude_admissible_proof : E2ExponentAmplitudeStatement := by
  intro c₀ hc
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : ∀ j : ℕ, Real.log 2 ≤ Real.sqrt ((j : ℝ) + 1) * Real.log ((j : ℝ) + 2) := by
    intro j
    have h1 : (1 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) :=
      Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    have h2 : Real.log 2 ≤ Real.log ((j : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    nlinarith
  refine ⟨fun j => ?_, ⟨fun h => ?_, fun h j => ?_⟩⟩
  · unfold exponentAmplitude
    exact div_pos hc (lt_of_lt_of_le hlog (hD j))
  · have h0 := h 0
    unfold exponentAmplitude at h0
    simp only [Nat.cast_zero, zero_add, Real.sqrt_one, one_mul] at h0
    exact (div_le_one hlog).mp h0
  · unfold exponentAmplitude
    exact (div_le_one (lt_of_lt_of_le hlog (hD j))).mpr (h.trans (hD j))

end ParabolicRectifiability.Examples
