import ParabolicRectifiability.BetaP.Proofs.Comparison.ComparisonStatements

/-! # `S_p` endpoint completion (proof of `c2_EnergySEndpointStatement`)

Case `a ≤ ρ`: monotonicity of the set. Case `ρ < a`: `(0,a) ⊆ (0,ρ) ∪ (ρ/2,a)` and the
finite-annulus law `BetaPowAnnulusStatement` (a hypothesis) on the annulus `(ρ/2,a)`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

theorem c2e_Ioo_subset_union {ρ a : ℝ} (hρ : 0 < ρ) :
    Ioo 0 a ⊆ Ioo 0 ρ ∪ Ioo (ρ / 2) a := by
  intro x hx
  by_cases h : x < ρ
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨by linarith [not_lt.mp h], hx.2⟩

theorem c2_energyS_endpoint_proof : c2_EnergySEndpointStatement := by
  intro hL3 n hn k hk hkn T hT μ hμ hreg p hp z ρ a hρ hfin
  unfold energyS
  by_cases ha : a ≤ ρ
  · exact lt_of_le_of_lt
      (lintegral_mono_set (Ioo_subset_Ioo_right ha)) hfin
  · have hρa : ρ < a := not_le.mp ha
    have hann := (hL3 n hn k hk hkn T hT μ hμ hreg p hp z (ρ / 2) a
      (by linarith) (by linarith)).1
    calc _ ≤ (∫⁻ r in Ioo 0 ρ ∪ Ioo (ρ / 2) a,
          betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure) :=
          lintegral_mono_set (c2e_Ioo_subset_union hρ)
      _ ≤ _ := lintegral_union_le _ _ _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hfin, hann⟩

end ParabolicRectifiability.BetaP
