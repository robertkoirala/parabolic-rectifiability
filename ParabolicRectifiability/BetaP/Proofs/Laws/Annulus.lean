import ParabolicRectifiability.BetaP.Statements.Laws
import ParabolicRectifiability.Geometry.AdmissibleModels
import ParabolicRectifiability.Measure.CountableFitting
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Finite annuli for the beta-`p` scale integrands

`BetaPowAnnulusStatement`, general `p > 0`, with no separate `p = 2` branch. The pointwise bound
`B_p(z,r) ≤ r^{-k} μ(P(z,r))` (no local finiteness) is integrated against `scaleMeasure` after
bounding by the constant `u^{-k} μ(closedBall z v)`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Exact cancellation of the radius powers at a positive, finite radius. -/
theorem c2_inv_radius_rpow_mul {r : ℝ} (hr : 0 < r) (k : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (a : ℝ≥0∞) :
    (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) * (ENNReal.ofReal r ^ p * a) =
      (ENNReal.ofReal r)⁻¹ ^ k * a := by
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have h1 : (ENNReal.ofReal r)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have h2 : (ENNReal.ofReal r)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
  have hc : (ENNReal.ofReal r)⁻¹ ^ p * ENNReal.ofReal r ^ p = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top,
      ENNReal.one_rpow]
  rw [ENNReal.rpow_add _ _ h1 h2, ENNReal.rpow_natCast]
  calc
    _ = (ENNReal.ofReal r)⁻¹ ^ k * (((ENNReal.ofReal r)⁻¹ ^ p * ENNReal.ofReal r ^ p) * a) := by
      simp only [mul_assoc]
    _ = _ := by rw [hc, one_mul]

/-- `B_p(z,r) ≤ r^{-k} μ(P(z,r))` for an available family; no local finiteness is used. -/
theorem c2_betaPow_le_radius_inv_pow_mul_measure {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (T : FamilyKind) [Nonempty (Models n k T)] {p : ℝ} (hp : 0 < p) (z : Space n)
    {r : ℝ} (hr : 0 < r) :
    betaPow μ k T p z r ≤ (ENNReal.ofReal r)⁻¹ ^ k * μ (Metric.ball z r) := by
  obtain ⟨L, hz⟩ := exists_model_mem (inferInstance : Nonempty (Models n k T)) z
  have hfit : fitPow μ p L z r ≤ ENNReal.ofReal r ^ p * μ (Metric.ball z r) := by
    calc
      fitPow μ p L z r ≤ ∫⁻ _w in Metric.ball z r, ENNReal.ofReal r ^ p ∂μ :=
        setLIntegral_mono' measurableSet_ball fun w hw =>
          ENNReal.rpow_le_rpow
            ((Metric.infEDist_le_edist_of_mem hz).trans (by
              rw [edist_dist]
              exact ENNReal.ofReal_le_ofReal (Metric.mem_ball.mp hw).le)) hp.le
      _ = _ := by simp
  simp only [betaPow, hr, ↓reduceIte]
  calc
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) * fitPow μ p L z r := by
      gcongr; exact iInf_le _ L
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) * (ENNReal.ofReal r ^ p * μ (Metric.ball z r)) := by
      gcongr
    _ = _ := c2_inv_radius_rpow_mul hr k hp.le _

/-- Finite annuli, for every `p > 0`. -/
theorem c2_betaPowAnnulus_proof : BetaPowAnnulusStatement := by
  intro n _ k _ _ T hT μ hμ _ p hp z u v hu huv
  have := hT
  have := hμ
  set C : ℝ≥0∞ := (ENNReal.ofReal u)⁻¹ ^ k * μ (Metric.closedBall z v) with hC
  have hCtop : C ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ (measure_closedBall_lt_top μ z v).ne
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hu).ne')
  have hpt : ∀ r ∈ Ioo u v, betaPow μ k T p z r ≤ C := by
    intro r hr
    have hr0 : 0 < r := hu.trans hr.1
    refine (c2_betaPow_le_radius_inv_pow_mul_measure μ k T hp z hr0).trans ?_
    rw [hC]
    gcongr
    · exact hr.1.le
    · exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr.2.le)
  have hσ : scaleMeasure (Ioo u v) < ⊤ :=
    (measure_mono Ioo_subset_Icc_self).trans_lt (scaleMeasure_Icc_lt_top hu)
  have hint : ∀ (c : ℝ≥0∞), c ≠ ⊤ → ∀ f : ℝ → ℝ≥0∞, (∀ r ∈ Ioo u v, f r ≤ c) →
      (∫⁻ r in Ioo u v, f r ∂scaleMeasure) < ⊤ := by
    intro c hc f hf
    calc
      _ ≤ ∫⁻ _r in Ioo u v, c ∂scaleMeasure := setLIntegral_mono' measurableSet_Ioo hf
      _ = c * scaleMeasure (Ioo u v) := by simp
      _ < ⊤ := ENNReal.mul_lt_top hc.lt_top hσ
  refine ⟨hint (C ^ (2 / p)) (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCtop) _ fun r hr =>
    ENNReal.rpow_le_rpow (hpt r hr) (by positivity), hint C hCtop _ hpt⟩
