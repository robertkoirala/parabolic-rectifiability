import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo
import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # `S_2 = T_2 = S`

`Foundations.EnergyTwoStatement`. At `p = 2` the exponent `2 / p` is `1`, so
`energyS` and `energyT` both integrate `betaPow μ k T 2 z r`, which is `betaSq μ k T z r` by
`f3_betaPow_two_eq_betaSq_proof`; that integral is `squareEnergy`. The hypothesis
`0 < a` is unused.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The two energies at `p = 2` are the square energy, for every family. -/
theorem f2c_energyTwo_proof : EnergyTwoStatement := by
  intro n hn k hk hkn T μ a _ z
  have h := f3_betaPow_two_eq_betaSq_proof n hn k hk hkn T μ z
  constructor
  · unfold energyS squareEnergy
    refine lintegral_congr fun r => ?_
    rw [h r, show (2 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  · unfold energyT squareEnergy
    exact lintegral_congr fun r => h r

end ParabolicRectifiability.Foundations
