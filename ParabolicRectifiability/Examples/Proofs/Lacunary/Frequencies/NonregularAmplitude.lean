import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # Admissibility of the nonregular amplitudes

The amplitudes `a_j = (√(j+1))⁻¹` satisfy the admissibility conditions
(`e2_nonregularAmplitude_admissible_proof`). -/

noncomputable section

namespace ParabolicRectifiability.Examples

/-- Proof of the admissibility of the nonregular amplitudes `a_j = (√(j+1))⁻¹`. -/
theorem e2_nonregularAmplitude_admissible_proof : E2NonregularAmplitudeStatement := by
  intro j
  have h1 : (1 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) :=
    Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  unfold nonregularAmplitude
  exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ h1⟩

end ParabolicRectifiability.Examples
