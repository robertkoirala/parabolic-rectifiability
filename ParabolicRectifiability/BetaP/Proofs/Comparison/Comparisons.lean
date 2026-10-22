import ParabolicRectifiability.BetaP.Proofs.Comparison.ComparisonLemmas
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds

/-! # Pointwise comparison of `S_p` and `S_2` at points of finite upper density

* `c2_energyS_lt_top_of_squareEnergy_lt_top` proves the statement of
  `energyS_lt_top_of_squareEnergy_lt_top` (`0 < p < 2`: `S_2^a(z) < ∞ ⇒ S_p^a(z) < ∞`).
* `c2_squareEnergy_lt_top_of_energyS_lt_top` proves the statement of
  `squareEnergy_lt_top_of_energyS_lt_top` (`p > 2`: `S_p^a(z) < ∞ ⇒ S_2^a(z) < ∞`).

Proof: from the finite upper density take `A < ∞`, `ρ > 0` with `Θ(z,r) ≤ A` on `(0,ρ)` and put
`ρ' = min ρ a > 0`.
* `p < 2`: `∫_0^{ρ'} betaSq ≤ S_2^a(z) < ∞`, so `∫_0^{ρ'} B_p^{2/p} ≤ A^{2/p-1} ∫_0^{ρ'} betaSq
  < ∞`; the endpoint completion (with the finite-annulus law) gives `S_p^a(z) < ∞`.
* `p > 2`: `∫_0^{ρ'} B_p^{2/p} ≤ S_p^a(z) < ∞`, so `S_2^{ρ'}(z) = ∫_0^{ρ'} betaSq ≤ A^{1-2/p}
  ∫_0^{ρ'} B_p^{2/p} < ∞`; `squareEnergy_lt_top_iff_of_endpoints_proof` moves
  the endpoint from `ρ'` to `a`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- For `0 < p < 2`, at a point of finite upper `k`-density, `S_2^a(z) < ∞` implies
`S_p^a(z) < ∞` (the statement of `energyS_lt_top_of_squareEnergy_lt_top`). -/
theorem c2_energyS_lt_top_of_squareEnergy_lt_top {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T)) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {p : ℝ} (hp : 0 < p) (hp2 : p < 2)
    {a : ℝ} (ha : 0 < a) {z : Space n} (hz : upperDensity μ k z < ⊤)
    (hS : squareEnergy μ k T a z < ⊤) : energyS μ k T p a z < ⊤ := by
  obtain ⟨A, ρ, hA, hρ, hΘ⟩ := c2_upperDensity_bound μ k z hz
  have hρa : 0 < min ρ a := lt_min hρ ha
  have hΘ' : ∀ r : ℝ, 0 < r → r < min ρ a → densityRatio μ k z r ≤ A :=
    fun r hr hr' => hΘ r hr (hr'.trans_le (min_le_left ρ a))
  have hsq : (∫⁻ r in Ioo 0 (min ρ a), betaSq μ k T z r ∂scaleMeasure) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (Ioo_subset_Ioo_right (min_le_right ρ a))) hS
  have hexp : 0 ≤ 2 / p - 1 := sub_nonneg.mpr ((one_lt_div hp).mpr hp2).le
  have hfin : (∫⁻ r in Ioo 0 (min ρ a), betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure) < ⊤ :=
    lt_of_le_of_lt (c2_cmpLt_smallScale hn hk hkn hT hμ hreg hp hp2 z A (min ρ a) hA hΘ')
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hexp hA) hsq)
  exact c2_energyS_endpoint c2_cmp_input_annulus hn hk hkn hT hμ hreg hp z (min ρ a) a hρa hfin

/-- For `p > 2`, at a point of finite upper `k`-density, `S_p^a(z) < ∞` implies
`S_2^a(z) < ∞` (the statement of `squareEnergy_lt_top_of_energyS_lt_top`). -/
theorem c2_squareEnergy_lt_top_of_energyS_lt_top {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T)) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {p : ℝ} (hp2 : 2 < p) {a : ℝ}
    (ha : 0 < a) {z : Space n} (hz : upperDensity μ k z < ⊤)
    (hS : energyS μ k T p a z < ⊤) : squareEnergy μ k T a z < ⊤ := by
  obtain ⟨A, ρ, hA, hρ, hΘ⟩ := c2_upperDensity_bound μ k z hz
  have hρa : 0 < min ρ a := lt_min hρ ha
  have hΘ' : ∀ r : ℝ, 0 < r → r < min ρ a → densityRatio μ k z r ≤ A :=
    fun r hr hr' => hΘ r hr (hr'.trans_le (min_le_left ρ a))
  have hSp : (∫⁻ r in Ioo 0 (min ρ a), betaPow μ k T p z r ^ (2 / p) ∂scaleMeasure) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set (Ioo_subset_Ioo_right (min_le_right ρ a))) hS
  have hp0 : (0 : ℝ) < p := by linarith
  have hexp : 0 ≤ 1 - 2 / p := sub_nonneg.mpr ((div_lt_one hp0).mpr hp2).le
  have hfin : squareEnergy μ k T (min ρ a) z < ⊤ :=
    lt_of_le_of_lt (c2_cmpGt_smallScale hn hk hkn hT hμ hreg hp2 z A (min ρ a) hA hΘ')
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hexp hA) hSp)
  exact (squareEnergy_lt_top_iff_of_endpoints_proof n hn k hk hkn T μ hμ hreg z (min ρ a) a
    hρa ha).mp hfin

end ParabolicRectifiability.BetaP
