import ParabolicRectifiability.BetaP.Proofs.Comparison.ComparisonStatements
import ParabolicRectifiability.BetaP.Proofs.Laws.Holder
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo

/-! # Small scales below two (`c2_cmpLt_smallScale`)

Proof of `c2_CmpLtSmallScaleStatement`. Pointwise at `0 < r < ρ`, Hölder clause 1 at `(p, 2)` (`claws_holder_proof`) is
`B_p^{1/p} ≤ Θ^{1/p - 1/2} B_2^{1/2}`. Raising to the power `2` gives
`B_p^{2/p} ≤ Θ^{2/p - 1} B_2`; with `B_2 = betaSq` (`f3_betaPow_two_eq_betaSq_proof`) and
`Θ^{2/p-1} ≤ A^{2/p-1}` (`2/p - 1 ≥ 0`), integrate with `setLIntegral_mono'` and pull the
finite constant out with `lintegral_const_mul'`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Squared Hölder, pointwise: `B_p^{1/p} ≤ Θ^{1/p-1/2} B_2^{1/2}` gives `B_p^{2/p} ≤ Θ^{2/p-1} * B_2`. -/
theorem c2l_pointwise {B Θ B2 : ℝ≥0∞} {p : ℝ}
    (h : B ^ (1 / p) ≤ Θ ^ (1 / p - 1 / 2) * B2 ^ (1 / (2 : ℝ))) :
    B ^ (2 / p) ≤ Θ ^ (2 / p - 1) * B2 := by
  have h2 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 2 by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 2 by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have e1 : 1 / p * 2 = 2 / p := by ring
  have e2 : (1 / p - 1 / 2) * 2 = 2 / p - 1 := by ring
  have e3 : 1 / (2 : ℝ) * 2 = 1 := by norm_num
  rw [e1, e2, e3, ENNReal.rpow_one] at h2
  exact h2

/-- **Small scales below two:** `∫_{(0,ρ)} B_p^{2/p} ≤ A^{2/p-1} ∫_{(0,ρ)} betaSq`. -/
theorem c2_cmpLt_smallScale_proof : c2_CmpLtSmallScaleStatement := by
  intro n hn k hk hkn T hT μ hfin hreg p hp hp2 z A ρ hA hΘ
  have hexp : (0 : ℝ) ≤ 2 / p - 1 := by
    rw [sub_nonneg, le_div_iff₀ hp]; linarith
  have hHolder := (claws_holder_proof n hn k hk hkn T hT μ hfin hreg)
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hexp hA)]
  refine setLIntegral_mono' measurableSet_Ioo (fun r hr => ?_)
  have hr0 : 0 < r := hr.1
  have h1 := (hHolder z r hr0).1 p 2 hp hp2
  have h2 := c2l_pointwise h1
  rw [f3_betaPow_two_eq_betaSq_proof n hn k hk hkn T μ z r] at h2
  exact h2.trans (by gcongr; exact hΘ r hr0 hr.2)

end ParabolicRectifiability.BetaP
