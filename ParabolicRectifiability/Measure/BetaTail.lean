import ParabolicRectifiability.Measure.ScaleIntegrals
import Mathlib.MeasureTheory.Measure.Support

/-! # Beta numbers at large scales

When the whole support of a source lies in the testing ball, the fitting error on that
ball equals the global fitting error `globalFittingError`. Hence above the diameter of
the support every scale sees the same error, which gives the tail identity
`betaSq_tail_eq_annulus`. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability

/-- The actual global squared fitting error, with no normalization by source mass. -/
def globalFittingError {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (F : FamilyKind) : ℝ≥0∞ :=
  ⨅ L : Models n k F, ∫⁻ w, modelCost L w ∂μ

theorem fit_eq_global_of_ae_mem_ball {n k : ℕ} {F : FamilyKind}
    (μ : Measure (Space n)) (L : Models n k F) (z : Space n) (r : ℝ)
    (h : ∀ᵐ w ∂μ, w ∈ Metric.ball z r) :
    fit μ L z r = ∫⁻ w, modelCost L w ∂μ := by
  rw [fit, Measure.restrict_eq_self_of_ae_mem h]

theorem betaSq_eq_global_of_ae_mem_ball {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (F : FamilyKind) (z : Space n) {r : ℝ} (hr : 0 < r)
    (h : ∀ᵐ w ∂μ, w ∈ Metric.ball z r) :
    betaSq μ k F z r = (ENNReal.ofReal r)⁻¹ ^ (k + 2) * globalFittingError μ k F := by
  rw [betaSq_of_pos μ k F z hr]
  simp only [fit_eq_global_of_ae_mem_ball μ _ z r h, globalFittingError]

theorem support_subset_ball_of_diam_lt_one {n : ℕ} (μ : Measure (Space n))
    (hc : IsCompact μ.support) (hd : Metric.diam μ.support < 1)
    {z : Space n} (hz : z ∈ μ.support) {r : ℝ} (hr : 1 ≤ r) :
    μ.support ⊆ Metric.ball z r := by
  intro w hw
  exact (Metric.dist_le_diam_of_mem hc.isBounded hw hz).trans_lt (hd.trans_le hr)

theorem betaSq_eq_global_of_support_diam {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (F : FamilyKind) (hc : IsCompact μ.support)
    (hd : Metric.diam μ.support < 1) {z : Space n} (hz : z ∈ μ.support)
    {r : ℝ} (hr : 1 ≤ r) :
    betaSq μ k F z r = (ENNReal.ofReal r)⁻¹ ^ (k + 2) * globalFittingError μ k F := by
  apply betaSq_eq_global_of_ae_mem_ball μ k F z (lt_of_lt_of_le zero_lt_one hr)
  filter_upwards [μ.support_mem_ae] with w hw
  exact support_subset_ball_of_diam_lt_one μ hc hd hz hr hw


/-- Every scale set above one sees the same global fitting error. The error may be infinite. -/
theorem lintegral_betaSq_of_support_diam {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (F : FamilyKind) (hc : IsCompact μ.support)
    (hd : Metric.diam μ.support < 1) {z : Space n} (hz : z ∈ μ.support)
    (A : Set ℝ) (hA : MeasurableSet A) (hA1 : A ⊆ Ici 1) :
    (∫⁻ r in A, betaSq μ k F z r ∂scaleMeasure) =
      (∫⁻ r in A, (ENNReal.ofReal r)⁻¹ ^ (k + 2) ∂scaleMeasure) *
        globalFittingError μ k F := by
  calc
    _ = ∫⁻ r in A, (ENNReal.ofReal r)⁻¹ ^ (k + 2) * globalFittingError μ k F
        ∂scaleMeasure := by
      apply setLIntegral_congr_fun hA
      intro r hr
      exact betaSq_eq_global_of_support_diam μ k F hc hd hz (hA1 hr)
    _ = _ := lintegral_mul_const _ (measurable_inv_pow_ofReal (k + 2))

/-- The exact finite-upper-endpoint identity; no energy bound near scale zero is assumed. -/
theorem betaSq_tail_eq_annulus {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (F : FamilyKind) (hc : IsCompact μ.support)
    (hd : Metric.diam μ.support < 1) {z : Space n} (hz : z ∈ μ.support) :
    (∫⁻ r in Ioi (2 : ℝ), betaSq μ k F z r ∂scaleMeasure) =
      (ENNReal.ofReal ((2 : ℝ) ^ (k + 2) - 1))⁻¹ *
        ∫⁻ r in Ioo (1 : ℝ) 2, betaSq μ k F z r ∂scaleMeasure := by
  rw [lintegral_betaSq_of_support_diam μ k F hc hd hz _ measurableSet_Ioi
      (fun r hr => le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hr)),
    lintegral_betaSq_of_support_diam μ k F hc hd hz _ measurableSet_Ioo
      (fun r hr => hr.1.le),
    lintegral_inv_pow_tail_eq_annulus (k + 2) (by omega), mul_assoc]

end ParabolicRectifiability
