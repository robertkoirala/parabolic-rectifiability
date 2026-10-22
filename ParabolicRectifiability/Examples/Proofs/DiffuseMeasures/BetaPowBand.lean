import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Decomposition.Carrier.BetaPointBoundAndRankZero

/-! # A logarithmic band lower bound for beta powers

Nested balls make every unnormalized fitting integral nondecreasing. The same
holds for the infimum over models, including an empty model family. On a dyadic
band the inverse radius power loses at most the factor `2 ^ (k + q)`. Integrating
this constant lower bound uses the mass of the scale band.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- Enlarging the radius increases the unnormalized fitting infimum. -/
theorem e2_fitPow_iInf_mono {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (q : ℝ) (z : Space n) {s r : ℝ} (hsr : s ≤ r) :
    (⨅ L : Models n k T, fitPow μ q L z s) ≤
      ⨅ L : Models n k T, fitPow μ q L z r := by
  apply iInf_mono
  intro L
  exact lintegral_mono_set (Metric.ball_subset_ball hsr)

/-- The exact inverse-power comparison on a dyadic radius band. -/
theorem e2_betaPow_band_pointwise {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (q : ℝ) (hq : 0 ≤ q) (z : Space n)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : r ∈ Icc ρ (2 * ρ)) :
    ((2 : ℝ≥0∞) ^ ((k : ℝ) + q))⁻¹ * betaPow μ k T q z ρ ≤
      betaPow μ k T q z r := by
  have hp : 0 ≤ (k : ℝ) + q := add_nonneg (Nat.cast_nonneg k) hq
  have hr0 : 0 < r := hρ.trans_le hr.1
  have hfactor : ((2 : ℝ≥0∞) ^ ((k : ℝ) + q))⁻¹ *
      (ENNReal.ofReal ρ)⁻¹ ^ ((k : ℝ) + q) ≤
      (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + q) := by
    calc
      _ = (ENNReal.ofReal (2 * ρ))⁻¹ ^ ((k : ℝ) + q) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ENNReal.mul_inv (a := (2 : ℝ≥0∞)) (b := ENNReal.ofReal ρ)
            (by simp) (by simp),
          ENNReal.mul_rpow_of_nonneg _ _ hp,
          ENNReal.inv_rpow (2 : ℝ≥0∞) ((k : ℝ) + q)]
      _ ≤ _ := ENNReal.rpow_le_rpow (ENNReal.inv_le_inv.mpr
        (ENNReal.ofReal_le_ofReal hr.2)) hp
  rw [betaPow, betaPow, ite_eq_left hρ, ite_eq_left hr0, ← mul_assoc]
  exact mul_le_mul' hfactor (e2_fitPow_iInf_mono μ k T q z hr.1)

/-- One logarithmic scale band controls the beta power at its inner radius. -/
theorem e2_betaPow_band_proof : E2BandStatement := by
  intro n μ k T q hq z ρ hρ
  calc
    _ = (((2 : ℝ≥0∞) ^ ((k : ℝ) + q))⁻¹ * betaPow μ k T q z ρ) *
        scaleMeasure (Icc ρ (2 * ρ)) := by
      rw [scaleMeasure_Icc_two_mul hρ]
      ac_rfl
    _ = ∫⁻ _r in Icc ρ (2 * ρ),
        ((2 : ℝ≥0∞) ^ ((k : ℝ) + q))⁻¹ * betaPow μ k T q z ρ ∂scaleMeasure := by
      rw [setLIntegral_const]
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc
      (fun r hr => e2_betaPow_band_pointwise μ k T q hq z hρ hr)

end ParabolicRectifiability.Examples
