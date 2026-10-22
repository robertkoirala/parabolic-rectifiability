import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.BetaP.Proofs.Carrier.Domination

/-! # Amplitude law `B_{p,cμ} = c B_{p,μ}`

`c2_betaPowSmul_proof : BetaPowSmulStatement`. Two applications of the domination helper
`CarrierTree.ccare_betaPow_le_smul` (with `c` and `c⁻¹`), then antisymmetry.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Amplitude law for `B_p` (`BetaPowSmulStatement`). -/
theorem c2_betaPowSmul_proof : BetaPowSmulStatement := by
  intro n _ k _ _ T μ p _ c hc z r
  have hC0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hCt : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hI0 : (ENNReal.ofReal c)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hCt
  have hIt : (ENNReal.ofReal c)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hC0
  have h1 : betaPow (ENNReal.ofReal c • μ) k T p z r ≤ ENNReal.ofReal c * betaPow μ k T p z r :=
    CarrierTree.ccare_betaPow_le_smul hC0 hCt le_rfl k T p z r
  have hle : μ ≤ (ENNReal.ofReal c)⁻¹ • (ENNReal.ofReal c • μ) := by
    rw [smul_smul, ENNReal.inv_mul_cancel hC0 hCt, one_smul]
  have h2 : betaPow μ k T p z r ≤
      (ENNReal.ofReal c)⁻¹ * betaPow (ENNReal.ofReal c • μ) k T p z r :=
    CarrierTree.ccare_betaPow_le_smul hI0 hIt hle k T p z r
  refine le_antisymm h1 ?_
  calc ENNReal.ofReal c * betaPow μ k T p z r
      ≤ ENNReal.ofReal c * ((ENNReal.ofReal c)⁻¹ * betaPow (ENNReal.ofReal c • μ) k T p z r) :=
        mul_le_mul' le_rfl h2
    _ = betaPow (ENNReal.ofReal c • μ) k T p z r := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCt, one_mul]

end ParabolicRectifiability.BetaP
