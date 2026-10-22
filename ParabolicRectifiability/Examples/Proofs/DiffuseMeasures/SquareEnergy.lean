import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements

/-! # Quadratic specialization of the diffuse energy bounds

Proof of `E2DiffuseSquareStatement` (`e2e1_diffuse_square_proof`): the second
conjunct of `EnergyTwoStatement` at endpoint `2` rewrites the `T`-clauses of
`E2DiffuseEnergyBounds n k .mixed 2` into `squareEnergy`; take `A = A_T`. -/

noncomputable section

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

theorem e2e1_diffuse_square_proof : E2DiffuseSquareStatement := by
  intro hE n k hn hk hkn hB
  obtain ⟨AS, AT, hAS, hAT, hpt, hSint, hTint⟩ := hB
  have hEq : ∀ z : Space n,
      energyT (e2_diffuseBase n) k .mixed 2 2 z = squareEnergy (e2_diffuseBase n) k .mixed 2 z :=
    fun z => (hE n hn k hk (by omega) .mixed (e2_diffuseBase n) 2 (by norm_num) z).2
  refine ⟨AT, hAT, fun z => ?_, ?_, ?_⟩
  · rw [← hEq z]; exact (hpt z).2
  · simp only [← hEq]; exact hTint.1
  · simp only [← hEq]; exact hTint.2

end ParabolicRectifiability.Examples
