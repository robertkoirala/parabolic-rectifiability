import ParabolicRectifiability.BetaP.Proofs.Comparison.ComparisonStatements
import ParabolicRectifiability.BetaP.Proofs.Laws.Holder
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo

/-! # Small scales above two (`c2_cmpGt_smallScale`)

Pointwise `betaSq = B_2` and Hölder clause 2 give `betaSq ≤ Θ^{1-2/p} B_p^{2/p}`; then
`Θ ≤ A` on `(0,ρ)` and monotone integration, pulling out the finite constant. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

theorem c2g_pointwise {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    {T : FamilyKind} (hT : Nonempty (Models n k T)) {μ : Measure (Space n)}
    (hfin : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {p : ℝ} (hp : 2 < p)
    (z : Space n) (A : ℝ≥0∞) (ρ : ℝ)
    (hΘ : ∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A) (r : ℝ) (hr : r ∈ Ioo 0 ρ) :
    betaSq μ k T z r ≤ A ^ (1 - 2 / p) * betaPow μ k T p z r ^ (2 / p) := by
  have hexp : 0 ≤ 1 - 2 / p := by
    have : 2 / p ≤ 1 := by rw [div_le_one (by linarith)]; exact hp.le
    linarith
  have h2 := (claws_holder_proof n hn k hk hkn T hT μ hfin hreg z r hr.1).2 p hp.le
  rw [f3_betaPow_two_eq_betaSq_proof n hn k hk hkn T μ z r] at h2
  refine h2.trans ?_
  exact mul_le_mul' (ENNReal.rpow_le_rpow (hΘ r hr.1 hr.2) hexp) le_rfl

theorem c2_cmpGt_smallScale_proof : c2_CmpGtSmallScaleStatement := by
  intro n hn k hk hkn T hT μ hfin hreg p hp z A ρ hA hΘ
  have hexp : 0 ≤ 1 - 2 / p := by
    have : 2 / p ≤ 1 := by rw [div_le_one (by linarith)]; exact hp.le
    linarith
  calc (∫⁻ r in Ioo 0 ρ, betaSq μ k T z r ∂scaleMeasure)
      ≤ ∫⁻ r in Ioo 0 ρ, A ^ (1 - 2 / p) * betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioo
          (fun r hr => c2g_pointwise hn hk hkn hT hfin hreg hp z A ρ hΘ r hr)
    _ = A ^ (1 - 2 / p) * ∫⁻ r in Ioo 0 ρ, betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hexp hA)

end ParabolicRectifiability.BetaP
