import ParabolicRectifiability.BetaP.Proofs.Localization.LocalizationStatements
import ParabolicRectifiability.Measure.BetaTail

/-! # The exact `p`-tail

Proves `cloc_pTail_proof : ClocPTailStatement`, the real-exponent analogue of the quadratic
tail computation (at `p = 2`, `q_p = k + 2`).

Let `I_p = inf_L ∫ d_P(w,L)^p dν(w)` (`clocp_globalFitPow`) and `q = q_p = 2 + 2k/p`.
* For `s ≥ 1` the support of `ν` (compact, of diameter `< 1`, containing `z`) lies in `P(z,s)`,
  and the support is `ν`-conull for every measure on this second-countable space, so
  `B_p(ν;z,s)^{2/p} = (ofReal s)⁻¹^q · I_p^{2/p}`
  (`clocp_betaPow_rpow_eq_global_of_support_diam`).
* `∫_{(2,∞)} s^{-q} ds/s = 2^{-q}/q` and `∫_{(1,2)} s^{-q} ds/s = (1 - 2^{-q})/q`, both finite and
  strictly positive; the constant `I_p^{2/p} ∈ [0,∞]` is pulled out, with no subtraction of
  infinite quantities. In particular
  `∫_{(1,2)} B_p^{2/p} ds/s = ofReal((1 - 2^{-q})/q) · I_p^{2/p}`
  (`clocp_lintegral_betaPow_rpow_Ioo_one_two`) with a finite, strictly positive
  coefficient (`clocp_annulusCoeff_pos`, `clocp_annulusCoeff_ennreal`). These
  support the deduction `I_p = 0` from vanishing energy; the tail ratio alone does not.
* An unavailable family gives `I_p = ⊤`; every identity above holds verbatim.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-! ## The global fitting infimum and the exponent `q_p` -/

/-- The global `p`-fitting infimum `I_p = inf_{L ∈ T} ∫ d_P(w,L)^p dν(w)` of the whole source
(no testing ball, no normalization). It is `⊤` for an unavailable family and may be `⊤`
otherwise. -/
def clocp_globalFitPow {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ) :
    ℝ≥0∞ :=
  ⨅ L : Models n k T, ∫⁻ w, Metric.infEDist w (modelSet L) ^ p ∂ν

/-- `q_p = 2 + 2k/p > 0` for `p > 0`. -/
theorem clocp_q_pos (k : ℕ) {p : ℝ} (hp : 0 < p) : 0 < 2 + 2 * (k : ℝ) / p :=
  add_pos_of_pos_of_nonneg two_pos (div_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg k)) hp.le)

/-! ## Global-fit factorization above scale one -/

theorem clocp_fitPow_eq_global_of_ae_mem_ball {n k : ℕ} {T : FamilyKind}
    (ν : Measure (Space n)) (p : ℝ) (L : Models n k T) (z : Space n) (r : ℝ)
    (h : ∀ᵐ w ∂ν, w ∈ Metric.ball z r) :
    fitPow ν p L z r = ∫⁻ w, Metric.infEDist w (modelSet L) ^ p ∂ν := by
  rw [fitPow, Measure.restrict_eq_self_of_ae_mem h]

/-- Compact support of diameter `< 1` through `z`: for `s ≥ 1`, `ν`-almost every point lies in
`P(z,s)` (the support is conull for every measure here; no local finiteness is used). -/
theorem clocp_ae_mem_ball_of_support_diam {n : ℕ} (ν : Measure (Space n))
    (hc : IsCompact ν.support) (hd : Metric.diam ν.support < 1) {z : Space n}
    (hz : z ∈ ν.support) {s : ℝ} (hs : 1 ≤ s) : ∀ᵐ w ∂ν, w ∈ Metric.ball z s := by
  filter_upwards [ν.support_mem_ae] with w hw
  exact support_subset_ball_of_diam_lt_one ν hc hd hz hs hw

/-- For `s ≥ 1`, `B_p(ν;z,s) = s^{-k-p} I_p`. -/
theorem clocp_betaPow_eq_global_of_support_diam {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (p : ℝ) (hc : IsCompact ν.support) (hd : Metric.diam ν.support < 1)
    {z : Space n} (hz : z ∈ ν.support) {s : ℝ} (hs : 1 ≤ s) :
    betaPow ν k T p z s = (ENNReal.ofReal s)⁻¹ ^ ((k : ℝ) + p) * clocp_globalFitPow ν k T p := by
  have hae := clocp_ae_mem_ball_of_support_diam ν hc hd hz hs
  rw [betaPow, ite_eq_left (zero_lt_one.trans_le hs)]
  simp only [clocp_fitPow_eq_global_of_ae_mem_ball ν p _ z s hae, clocp_globalFitPow]

/-- **Repair 1 (i), global-fit factorization.** For `s ≥ 1`,
`B_p(ν;z,s)^{2/p} = (ofReal s)^{-q} I_p^{2/p}`, `q = 2 + 2k/p`, valid for `I_p ∈ [0,∞]`. -/
theorem clocp_betaPow_rpow_eq_global_of_support_diam {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) {p : ℝ} (hp : 0 < p) (hc : IsCompact ν.support)
    (hd : Metric.diam ν.support < 1) {z : Space n} (hz : z ∈ ν.support) {s : ℝ} (hs : 1 ≤ s) :
    betaPow ν k T p z s ^ (2 / p) =
      (ENNReal.ofReal s)⁻¹ ^ (2 + 2 * (k : ℝ) / p) * clocp_globalFitPow ν k T p ^ (2 / p) := by
  have hp0 : p ≠ 0 := hp.ne'
  have he : ((k : ℝ) + p) * (2 / p) = 2 + 2 * (k : ℝ) / p := by
    field_simp
    ring
  rw [clocp_betaPow_eq_global_of_support_diam ν k T p hc hd hz hs,
    ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_two hp.le), ← ENNReal.rpow_mul, he]

/-! ## Real-exponent scale integrals -/

theorem clocp_measurable_inv_rpow (q : ℝ) :
    Measurable (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ q) :=
  (ENNReal.measurable_ofReal.inv).pow_const q

theorem clocp_scaleDensity_mul_inv_rpow {q : ℝ} (hq : 0 ≤ q) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (1 / r) * (ENNReal.ofReal r)⁻¹ ^ q = ENNReal.ofReal (r ^ (-(q + 1))) := by
  rw [← ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hr.le) hq,
    ← ENNReal.ofReal_mul (one_div_nonneg.mpr hr.le)]
  congr 1
  rw [Real.inv_rpow hr.le, Real.rpow_neg hr.le, Real.rpow_add_one hr.ne', one_div]
  ring

/-- `∫_{(a,∞)} s^{-q} ds/s = a^{-q}/q` for real `q > 0`, `a > 0`. -/
theorem clocp_lintegral_inv_rpow_Ioi {q : ℝ} (hq : 0 < q) {a : ℝ} (ha : 0 < a) :
    (∫⁻ r in Ioi a, (ENNReal.ofReal r)⁻¹ ^ q ∂scaleMeasure) =
      ENNReal.ofReal (a ^ (-q) / q) := by
  have he : -(q + 1) < -1 := by linarith
  have hi := integrableOn_Ioi_rpow_of_lt he ha
  calc
    _ = ∫⁻ r in Ioi a, ENNReal.ofReal (r ^ (-(q + 1))) ∂volume := by
      rw [setLIntegral_scaleMeasure measurableSet_Ioi
        (Ioi_subset_Ioi ha.le) _ (clocp_measurable_inv_rpow q)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact clocp_scaleDensity_mul_inv_rpow hq.le (ha.trans hr)
    _ = ENNReal.ofReal (∫ r : ℝ in Ioi a, r ^ (-(q + 1))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact Real.rpow_nonneg (ha.trans hr).le _
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt he ha]
      have heq : -(q + 1) + 1 = -q := by ring
      rw [heq, neg_div_neg_eq]

/-- `∫_{(a,b)} s^{-q} ds/s = (a^{-q} - b^{-q})/q` for real `q > 0`, `0 < a ≤ b`. -/
theorem clocp_lintegral_inv_rpow_Ioo {q : ℝ} (hq : 0 < q) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    (∫⁻ r in Ioo a b, (ENNReal.ofReal r)⁻¹ ^ q ∂scaleMeasure) =
      ENNReal.ofReal ((a ^ (-q) - b ^ (-q)) / q) := by
  have hb : 0 < b := ha.trans_le hab
  have he : -(q + 1) < -1 := by linarith
  have hi := integrableOn_Ioi_rpow_of_lt he ha
  have hj := hi.mono_set (Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a)
  calc
    _ = ∫⁻ r in Ioo a b, ENNReal.ofReal (r ^ (-(q + 1))) ∂volume := by
      rw [setLIntegral_scaleMeasure measurableSet_Ioo
        (fun r hr => ha.trans hr.1) _ (clocp_measurable_inv_rpow q)]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      exact clocp_scaleDensity_mul_inv_rpow hq.le (ha.trans hr.1)
    _ = ENNReal.ofReal (∫ r : ℝ in Ioo a b, r ^ (-(q + 1))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hj
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact Real.rpow_nonneg (ha.trans hr.1).le _
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
        ← intervalIntegral.integral_Ioi_sub_Ioi hi hab,
        integral_Ioi_rpow_of_lt he ha, integral_Ioi_rpow_of_lt he hb]
      have heq : -(q + 1) + 1 = -q := by ring
      rw [heq, neg_div_neg_eq, neg_div_neg_eq, ← sub_div]

/-- The scalar tail identity for a real exponent `q > 0`:
`∫_{(2,∞)} s^{-q} ds/s = (2^q - 1)^{-1} ∫_{(1,2)} s^{-q} ds/s`. -/
theorem clocp_inv_rpow_tail_eq_annulus {q : ℝ} (hq : 0 < q) :
    (∫⁻ r in Ioi (2 : ℝ), (ENNReal.ofReal r)⁻¹ ^ q ∂scaleMeasure) =
      (ENNReal.ofReal ((2 : ℝ) ^ q - 1))⁻¹ *
        ∫⁻ r in Ioo (1 : ℝ) 2, (ENNReal.ofReal r)⁻¹ ^ q ∂scaleMeasure := by
  have hpow : 1 < (2 : ℝ) ^ q := Real.one_lt_rpow (by norm_num) hq
  have hdiff : 0 < (2 : ℝ) ^ q - 1 := sub_pos.mpr hpow
  have hx : (2 : ℝ) ^ q ≠ 0 := (zero_lt_one.trans hpow).ne'
  rw [clocp_lintegral_inv_rpow_Ioi hq (by norm_num : (0 : ℝ) < 2),
    clocp_lintegral_inv_rpow_Ioo hq one_pos (by norm_num : (1 : ℝ) ≤ 2), Real.one_rpow,
    ← ENNReal.ofReal_inv_of_pos hdiff, ← ENNReal.ofReal_mul (inv_nonneg.mpr hdiff.le)]
  congr 1
  have h1 : 1 - ((2 : ℝ) ^ q)⁻¹ = ((2 : ℝ) ^ q - 1) * ((2 : ℝ) ^ q)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hx, one_mul]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), h1, mul_div_assoc, ← mul_assoc,
    inv_mul_cancel₀ hdiff.ne', one_mul]

/-! ## Scale integrals of `B_p^{2/p}` above scale one -/

/-- Every measurable scale set above one: the scalar integral of `s^{-q}` times `I_p^{2/p}`. -/
theorem clocp_lintegral_betaPow_rpow_of_support_diam {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) {p : ℝ} (hp : 0 < p) (hc : IsCompact ν.support)
    (hd : Metric.diam ν.support < 1) {z : Space n} (hz : z ∈ ν.support) (A : Set ℝ)
    (hA : MeasurableSet A) (hA1 : A ⊆ Ici 1) :
    (∫⁻ s in A, betaPow ν k T p z s ^ (2 / p) ∂scaleMeasure) =
      (∫⁻ s in A, (ENNReal.ofReal s)⁻¹ ^ (2 + 2 * (k : ℝ) / p) ∂scaleMeasure) *
        clocp_globalFitPow ν k T p ^ (2 / p) := by
  calc
    _ = ∫⁻ s in A, (ENNReal.ofReal s)⁻¹ ^ (2 + 2 * (k : ℝ) / p) *
          clocp_globalFitPow ν k T p ^ (2 / p) ∂scaleMeasure := by
      apply setLIntegral_congr_fun hA
      intro s hs
      exact clocp_betaPow_rpow_eq_global_of_support_diam ν k T hp hc hd hz (hA1 hs)
    _ = _ := lintegral_mul_const _ (clocp_measurable_inv_rpow _)

/-- **Repair 1 (ii), annular evaluation.**
`∫_{(1,2)} B_p(ν;z,s)^{2/p} ds/s = ofReal((1 - 2^{-q})/q) · I_p^{2/p}`, `q = 2 + 2k/p`. -/
theorem clocp_lintegral_betaPow_rpow_Ioo_one_two {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) {p : ℝ} (hp : 0 < p) (hc : IsCompact ν.support)
    (hd : Metric.diam ν.support < 1) {z : Space n} (hz : z ∈ ν.support) :
    (∫⁻ s in Ioo (1 : ℝ) 2, betaPow ν k T p z s ^ (2 / p) ∂scaleMeasure) =
      ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(2 + 2 * (k : ℝ) / p))) / (2 + 2 * (k : ℝ) / p)) *
        clocp_globalFitPow ν k T p ^ (2 / p) := by
  rw [clocp_lintegral_betaPow_rpow_of_support_diam ν k T hp hc hd hz _ measurableSet_Ioo
      (fun s hs => hs.1.le),
    clocp_lintegral_inv_rpow_Ioo (clocp_q_pos k hp) one_pos (by norm_num : (1 : ℝ) ≤ 2),
    Real.one_rpow]

/-- The tail evaluation `∫_{(2,∞)} B_p(ν;z,s)^{2/p} ds/s = ofReal(2^{-q}/q) · I_p^{2/p}`. -/
theorem clocp_lintegral_betaPow_rpow_Ioi_two {n : ℕ} (ν : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) {p : ℝ} (hp : 0 < p) (hc : IsCompact ν.support)
    (hd : Metric.diam ν.support < 1) {z : Space n} (hz : z ∈ ν.support) :
    (∫⁻ s in Ioi (2 : ℝ), betaPow ν k T p z s ^ (2 / p) ∂scaleMeasure) =
      ENNReal.ofReal ((2 : ℝ) ^ (-(2 + 2 * (k : ℝ) / p)) / (2 + 2 * (k : ℝ) / p)) *
        clocp_globalFitPow ν k T p ^ (2 / p) := by
  rw [clocp_lintegral_betaPow_rpow_of_support_diam ν k T hp hc hd hz _ measurableSet_Ioi
      (fun s hs => mem_Ici.mpr (le_trans one_le_two (le_of_lt hs))),
    clocp_lintegral_inv_rpow_Ioi (clocp_q_pos k hp) (by norm_num : (0 : ℝ) < 2)]

/-- **Repair 1 (iii).** The annular coefficient `(1 - 2^{-q})/q` is strictly positive. -/
theorem clocp_annulusCoeff_pos (k : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < (1 - (2 : ℝ) ^ (-(2 + 2 * (k : ℝ) / p))) / (2 + 2 * (k : ℝ) / p) := by
  have hq := clocp_q_pos k hp
  have hlt : (2 : ℝ) ^ (-(2 + 2 * (k : ℝ) / p)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr hq)
  exact div_pos (sub_pos.mpr hlt) hq

/-- **Repair 1 (iii).** The annular coefficient `ofReal((1 - 2^{-q})/q)` is finite and strictly
positive in `ℝ≥0∞`. -/
theorem clocp_annulusCoeff_ennreal (k : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(2 + 2 * (k : ℝ) / p))) / (2 + 2 * (k : ℝ) / p)) ∧
      ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(2 + 2 * (k : ℝ) / p))) / (2 + 2 * (k : ℝ) / p)) ≠ ⊤ :=
  ⟨ENNReal.ofReal_pos.mpr (clocp_annulusCoeff_pos k hp), ENNReal.ofReal_ne_top⟩

/-! ## L-a -/

/-- **Exact `p`-tail** (`ClocPTailStatement`). -/
theorem cloc_pTail_proof : ClocPTailStatement := by
  intro n ν k T p hp hc hd z hz
  rw [clocp_lintegral_betaPow_rpow_of_support_diam ν k T hp hc hd hz _ measurableSet_Ioi
      (fun s hs => mem_Ici.mpr (le_trans one_le_two (le_of_lt hs))),
    clocp_lintegral_betaPow_rpow_of_support_diam ν k T hp hc hd hz _ measurableSet_Ioo
      (fun s hs => hs.1.le),
    clocp_inv_rpow_tail_eq_annulus (clocp_q_pos k hp), mul_assoc]

end ParabolicRectifiability.BetaP
