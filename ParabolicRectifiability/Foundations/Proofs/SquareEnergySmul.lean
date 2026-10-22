import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds

/-! # Scalar law for the square function

Proof of `SquareEnergySmulStatement`. Available families use
`squareEnergy_smul`; unavailable families give `⊤` on both sides.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

theorem f2i_squareEnergySmul_proof : SquareEnergySmulStatement := by
  intro n _ k _ _ T μ c hc A hA z
  by_cases h : Nonempty (Models n k T)
  · exact squareEnergy_smul μ (ENNReal.ofReal c) ENNReal.ofReal_ne_top k T A z
  · have hE : IsEmpty (Models n k T) := not_nonempty_iff.mp h
    rw [bf1m45_squareEnergy_eq_top_of_isEmpty (μ := ENNReal.ofReal c • μ) k T z hA,
      bf1m45_squareEnergy_eq_top_of_isEmpty (μ := μ) k T z hA]
    exact (ENNReal.mul_top (by simpa using hc)).symm

end ParabolicRectifiability.Foundations
