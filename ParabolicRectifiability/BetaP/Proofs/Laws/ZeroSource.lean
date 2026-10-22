import ParabolicRectifiability.BetaP.Proofs.Laws.Basic
import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.BetaP.Statements.Laws

/-! # Zero source

Proof: `claws_betaPow_eq_zero_of_ball` for the zero measure, then `0 ^ (2/p) = 0`, then the
integral of the zero function. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Zero source. -/
theorem c2_betaPowZeroSource_proof : BetaPowZeroSourceStatement := by
  intro n _ k _ _ T hT p hp z
  have h0 : ∀ r : ℝ, betaPow (0 : Measure (Space n)) k T p z r = 0 := fun r => by
    have := hT
    exact claws_betaPow_eq_zero_of_ball (T := T) (by simp)
  refine ⟨h0, fun a _ => ⟨?_, ?_⟩⟩
  · unfold energyS
    simp only [h0, ENNReal.zero_rpow_of_pos (div_pos two_pos hp), lintegral_zero]
  · unfold energyT
    simp only [h0, lintegral_zero]

end ParabolicRectifiability.BetaP
