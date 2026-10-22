import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Measure.Beta
import ParabolicRectifiability.Geometry.AdmissibleModels

/-! # A measure carried by one model has zero square energy -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Examples

theorem e2f1_fit_eq_zero {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    (h : μ (modelSet L)ᶜ = 0) (z : Space n) (r : ℝ) : fit μ L z r = 0 := by
  have hae : ∀ᵐ w ∂μ, w ∈ modelSet L := by
    rw [ae_iff]; exact h
  have hcost : ∀ᵐ w ∂μ.restrict (Metric.ball z r), modelCost L w = 0 := by
    refine ae_restrict_of_ae (hae.mono fun w hw => ?_)
    simp [modelCost, Metric.infEDist_zero_of_mem hw]
  unfold fit
  rw [lintegral_congr_ae hcost]
  simp

theorem e2f1_betaSq_eq_zero {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    (h : μ (modelSet L)ᶜ = 0) (z : Space n) (r : ℝ) : betaSq μ k T z r = 0 := by
  rcases le_or_gt r 0 with hr | hr
  · exact betaSq_of_nonpos μ k T z hr
  · rw [betaSq_of_pos μ k T z hr]
    have : ⨅ L' : Models n k T, fit μ L' z r = 0 :=
      le_antisymm ((iInf_le _ L).trans (e2f1_fit_eq_zero μ L h z r).le) bot_le
    rw [this, mul_zero]

theorem e2_squareEnergy_zero_of_modelCarried_proof : E2ModelCarriedSquareZeroStatement := by
  intro n k T μ L h R z
  unfold squareEnergy
  simp [e2f1_betaSq_eq_zero μ L h z]

end ParabolicRectifiability.Examples
