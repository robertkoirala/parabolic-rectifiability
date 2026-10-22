import ParabolicRectifiability.BetaP.Proofs.Laws.Basic

/-! # Hölder with the density factor

`BetaPowHolderStatement`. For one model `L` and the restricted measure `μ⌊P(z,r)`, the comparison of `L^p` norms on a
measure space (`eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ`, valid for every `0 < p ≤ q`) gives
`(∫ d^p)^{1/p} ≤ (∫ d^q)^{1/q} μ(P)^{1/p-1/q}`. Multiplying by the radius factors
`r^{-(k+p)/p} = r^{-k(1/p-1/q)} r^{-(k+q)/q}` gives the normalized inequality for one model
(`claws_normalized_holder`); `B_p^{1/p}` is below the left side for every model, and the right
side, as a function of the model, has infimum `Θ^{1/p-1/q} β_q` because `x ↦ x^{1/q}` is an
order isomorphism and `Θ^{1/p-1/q}` is finite and nonzero. The case `μ(P) = 0` is the empty
testing ball (`claws_betaPow_eq_zero_of_ball`, using the availability guard); `μ(P) < ⊤` by local
finiteness. Part 2 is part 1 for `(2,p)`, `p > 2`, squared; at `p = 2` both factors are trivial.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- A positive real power commutes with infima in `ℝ≥0∞`. -/
theorem claws_iInf_rpow {ι : Sort*} (f : ι → ℝ≥0∞) {e : ℝ} (he : 0 < e) :
    (⨅ i, f i) ^ e = ⨅ i, f i ^ e :=
  (ENNReal.orderIsoRpow e he).map_iInf f

/-- Hölder for one model on the ball: `(∫ d^p)^{1/p} ≤ (∫ d^q)^{1/q} μ(P)^{1/p-1/q}`. -/
theorem claws_fitPow_holder {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (L : Models n k T) (z : Space n) (r : ℝ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    fitPow μ p L z r ^ (1 / p) ≤
      fitPow μ q L z r ^ (1 / q) * μ (Metric.ball z r) ^ (1 / p - 1 / q) := by
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (μ := μ.restrict (Metric.ball z r)) hp hpq
    (f := fun w => Metric.infEDist w (modelSet L)) measurable_infEDist.aestronglyMeasurable
  simpa only [eLpNorm', enorm_eq_self, Measure.restrict_apply_univ, fitPow] using h

/-- The normalized Hölder inequality for one model at a positive radius. -/
theorem claws_normalized_holder {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n))
    (L : Models n k T) (z : Space n) {r : ℝ} (hr : 0 < r) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) :
    ((ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) * fitPow μ p L z r) ^ (1 / p) ≤
      densityRatio μ k z r ^ (1 / p - 1 / q) *
        ((ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + q) * fitPow μ q L z r) ^ (1 / q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hc0 : (ENNReal.ofReal r)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hct : (ENNReal.ofReal r)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne'
  have he : 0 ≤ 1 / p - 1 / q := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq)
  have hp1 : (0 : ℝ) ≤ 1 / p := (one_div_pos.mpr hp).le
  have hq1 : (0 : ℝ) ≤ 1 / q := (one_div_pos.mpr hq).le
  have hΘ : densityRatio μ k z r = μ (Metric.ball z r) * (ENNReal.ofReal r)⁻¹ ^ (k : ℝ) := by
    rw [densityRatio, div_eq_mul_inv, ENNReal.inv_pow, ← ENNReal.rpow_natCast]
  have hexp : ((k : ℝ) + p) * (1 / p) = (k : ℝ) * (1 / p - 1 / q) + ((k : ℝ) + q) * (1 / q) := by
    have h1 : p * (1 / p) = 1 := mul_one_div_cancel hp.ne'
    have h2 : q * (1 / q) = 1 := mul_one_div_cancel hq.ne'
    linear_combination h1 - h2
  rw [hΘ, ENNReal.mul_rpow_of_nonneg _ _ hp1, ENNReal.mul_rpow_of_nonneg _ _ hq1,
    ENNReal.mul_rpow_of_nonneg _ _ he, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, hexp, ENNReal.rpow_add _ _ hc0 hct]
  calc _ ≤ ((ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) * (1 / p - 1 / q)) *
          (ENNReal.ofReal r)⁻¹ ^ (((k : ℝ) + q) * (1 / q))) *
          (fitPow μ q L z r ^ (1 / q) * μ (Metric.ball z r) ^ (1 / p - 1 / q)) :=
        mul_le_mul' le_rfl (claws_fitPow_holder μ L z r hp hpq)
    _ = _ := by ring

/-- Part 1 of the Hölder law: `β_p ≤ Θ^{1/p-1/q} β_q` for `0 < p < q`. -/
theorem claws_holder_root {n k : ℕ} {T : FamilyKind} [Nonempty (Models n k T)]
    (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ] (z : Space n) {r : ℝ} (hr : 0 < r)
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    betaPow μ k T p z r ^ (1 / p) ≤
      densityRatio μ k z r ^ (1 / p - 1 / q) * betaPow μ k T q z r ^ (1 / q) := by
  have hq : 0 < q := hp.trans hpq
  by_cases hm : μ (Metric.ball z r) = 0
  · rw [claws_betaPow_eq_zero_of_ball hm, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)]
    exact bot_le
  have hmt : μ (Metric.ball z r) ≠ ⊤ := (measure_ball_lt_top μ z r).ne
  have hc0 : (ENNReal.ofReal r)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hct : (ENNReal.ofReal r)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne'
  have hepos : 0 < 1 / p - 1 / q := sub_pos.mpr (one_div_lt_one_div_of_lt hp hpq)
  have hkq : 0 ≤ (k : ℝ) + q := by positivity
  have hΘ0 : densityRatio μ k z r ≠ 0 := by
    rw [densityRatio]
    exact ENNReal.div_ne_zero.mpr ⟨hm, ENNReal.pow_ne_top ENNReal.ofReal_ne_top⟩
  have hΘt : densityRatio μ k z r ≠ ⊤ := by
    rw [densityRatio]
    exact (ENNReal.div_lt_top hmt (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne')).ne
  have hB : betaPow μ k T q z r ^ (1 / q) =
      ⨅ L : Models n k T, ((ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + q) * fitPow μ q L z r) ^ (1 / q) := by
    rw [claws_betaPow_of_pos _ _ _ _ _ hr,
      ENNReal.mul_iInf_of_ne (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hct).ne'
        (ENNReal.rpow_ne_top_of_nonneg hkq hct),
      claws_iInf_rpow _ (one_div_pos.mpr hq)]
  rw [hB, ENNReal.mul_iInf_of_ne
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hΘ0) hΘt).ne'
    (ENNReal.rpow_ne_top_of_nonneg hepos.le hΘt)]
  refine le_iInf fun L => le_trans ?_ (claws_normalized_holder μ L z hr hp hpq.le)
  rw [claws_betaPow_of_pos _ _ _ _ _ hr]
  exact ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (iInf_le _ L)) (one_div_pos.mpr hp).le

/-- Hölder with the density factor. -/
theorem claws_holder_proof : BetaPowHolderStatement := by
  intro n _ k _ _ T hT μ hμ _ z r hr
  have := hT
  have := hμ
  refine ⟨fun p q hp hpq => claws_holder_root μ z hr hp hpq, fun p hp2 => ?_⟩
  rcases hp2.eq_or_lt with h | h
  · subst h
    have e1 : (1 : ℝ) - 2 / 2 = 0 := by norm_num
    have e2 : (2 : ℝ) / 2 = 1 := by norm_num
    rw [e1, e2, ENNReal.rpow_zero, ENNReal.rpow_one, one_mul]
  · have h1 := claws_holder_root (k := k) (T := T) μ z hr two_pos h
    have h2 := ENNReal.rpow_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 2)
    have e1 : (1 : ℝ) / 2 * 2 = 1 := by norm_num
    have e2 : (1 / 2 - 1 / p) * 2 = 1 - 2 / p := by ring
    have e3 : 1 / p * 2 = 2 / p := by ring
    rwa [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, e1, e2, e3, ENNReal.rpow_one] at h2

end ParabolicRectifiability.BetaP
