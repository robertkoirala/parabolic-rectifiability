import ParabolicRectifiability.BetaP.Proofs.Laws.Measurability

/-! # The zero-error bridge `S_p^a(z) = 0 ⇒ squareEnergy(z) = 0`

`squareEnergy_eq_zero_of_energyS_eq_zero`. Proof:

1. `S_p^a(z) = ∫_{(0,a)} B_p(z,r)^{2/p} dr/r = 0` and the integrand is Borel in `r`
   (`cfit_measurable_betaPow`), so `B_p(z,r)^{2/p} = 0`, hence `B_p(z,r) = 0` (`2/p > 0`), for
   `scaleMeasure`-a.e. `r ∈ (0,a)`;
2. at such a radius `r > 0` the prefactor `r^{-k-p}` is nonzero and finite, so the fitting
   infimum vanishes; the infimum is **attained** on the bounded testing ball
   (`cfit_exists_fitPow_minimizer`), so one model `L` has `∫_{P(z,r)} d_P(w,L)^p dμ = 0`;
3. then `d_P(·,L) = 0` a.e. on the ball, so the quadratic fit of the same `L` vanishes
   (`cfit_fit_eq_zero_of_fitPow_eq_zero`), hence `betaSq μ k T z r = 0`;
4. so `squareEnergy μ k T a z = ∫_{(0,a)} betaSq(z,r) dr/r = 0`.

The identity `B_2 = betaSq` is not used: the argument works with `betaSq` directly. Inner regularity, `1 ≤ n`, `1 ≤ k` and `k ≤ n+2` are not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- At a positive radius, `B_p(z,r) = 0` (`p > 0`, available family, finite-on-compacts source)
forces `betaSq μ k T z r = 0`, through an attained `p`-fit. -/
theorem cfit_betaSq_eq_zero_of_betaPow_eq_zero {n k : ℕ} {T : FamilyKind}
    (hT : Nonempty (Models n k T)) {μ : Measure (Space n)} [IsFiniteMeasureOnCompacts μ]
    {p : ℝ} (hp : 0 < p) {z : Space n} {r : ℝ} (hr : 0 < r)
    (h : betaPow μ k T p z r = 0) : betaSq μ k T z r = 0 := by
  have hpre : (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) ≠ 0 := by
    have h0 : 0 < (ENNReal.ofReal r)⁻¹ :=
      ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
    have ht : (ENNReal.ofReal r)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne'
    exact (ENNReal.rpow_pos h0 ht).ne'
  have hinf : (⨅ L : Models n k T, fitPow μ p L z r) = 0 := by
    have h' := h
    simp only [betaPow, hr, ↓reduceIte] at h'
    exact (mul_eq_zero.mp h').resolve_left hpre
  obtain ⟨L, hL⟩ := cfit_exists_fitPow_minimizer μ hT hp.le z r
  have hfit : fit μ L z r = 0 := cfit_fit_eq_zero_of_fitPow_eq_zero hp (hL.trans hinf)
  rw [betaSq_of_pos μ k T z hr]
  have hle : (⨅ Q : Models n k T, fit μ Q z r) = 0 :=
    le_antisymm ((iInf_le _ L).trans hfit.le) zero_le
  rw [hle, mul_zero]

/-- **The zero-error bridge** (`squareEnergy_eq_zero_of_energyS_eq_zero`). -/
theorem cfit_squareEnergy_eq_zero_of_energyS_eq_zero_proof {n : ℕ} (_hn : 1 ≤ n) {k : ℕ}
    (_hk : 1 ≤ k) (_hkn : k ≤ n + 2) {T : FamilyKind} (hT : Nonempty (Models n k T))
    {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ) (_hreg : μ.InnerRegular) {p : ℝ}
    (hp : 0 < p) {a : ℝ} (_ha : 0 < a) {z : Space n} (h : energyS μ k T p a z = 0) :
    squareEnergy μ k T a z = 0 := by
  have hBm : Measurable (fun r : ℝ => betaPow μ k T p z r) :=
    (cfit_measurable_betaPow μ k T hp.le).comp measurable_prodMk_left
  have hae := (lintegral_eq_zero_iff (hBm.pow_const (2 / p))).mp h
  have hSm : Measurable (fun r : ℝ => betaSq μ k T z r) :=
    (measurable_betaSq μ k T).comp measurable_prodMk_left
  unfold squareEnergy
  refine (lintegral_eq_zero_iff hSm).mpr ?_
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with r hr hr0
  have hr' : betaPow μ k T p z r ^ (2 / p) = 0 := hr
  have hB : betaPow μ k T p z r = 0 := by
    rcases ENNReal.rpow_eq_zero_iff.mp hr' with h0 | h0
    · exact h0.1
    · exact absurd h0.2 (not_lt.mpr (div_pos two_pos hp).le)
  exact cfit_betaSq_eq_zero_of_betaPow_eq_zero hT hp hr0.1 hB

end ParabolicRectifiability.BetaP
