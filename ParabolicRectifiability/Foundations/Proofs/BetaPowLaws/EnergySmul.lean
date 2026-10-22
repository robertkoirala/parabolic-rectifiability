import ParabolicRectifiability.BetaP.Proofs.Laws.Smul
import ParabolicRectifiability.Foundations.BetaPow
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Amplitude laws for the beta-`p` energies

`f2c_energyPowSmul_proof : EnergyPowSmulStatement`, by integrating the amplitude law
`c2_betaPowSmul_proof` with `ENNReal.mul_rpow_of_nonneg` and `lintegral_const_mul'`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The amplitude laws of the beta-`p` energies: `EnergyPowSmulStatement`. -/
theorem f2c_energyPowSmul_proof : EnergyPowSmulStatement := by
  intro n hn k hk hkn T μ p hp c hc a ha z
  have hC : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq : (0 : ℝ) ≤ 2 / p := by positivity
  have hCq : ENNReal.ofReal c ^ (2 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq hC
  have hb : ∀ r : ℝ, betaPow (ENNReal.ofReal c • μ) k T p z r
      = ENNReal.ofReal c * betaPow μ k T p z r := fun r =>
    ParabolicRectifiability.BetaP.c2_betaPowSmul_proof n hn k hk hkn T μ p hp c hc z r
  constructor
  · unfold energyS
    simp_rw [hb, ENNReal.mul_rpow_of_nonneg _ _ hq]
    exact lintegral_const_mul' _ _ hCq
  · unfold energyT
    simp_rw [hb]
    exact lintegral_const_mul' _ _ hC

end ParabolicRectifiability.Foundations
