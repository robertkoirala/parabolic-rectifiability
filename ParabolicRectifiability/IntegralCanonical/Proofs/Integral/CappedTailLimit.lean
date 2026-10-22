import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements

/-! # The capped-tail limit

Proof of `i2_CappedTailLimitStatement`, the auxiliary statement `i2_cappedTail_limit`.

Route: dominated convergence along the countably generated filter
`𝓝[>] 0` for the measure `μ.restrict A`, with measurable integrands (`measurable_squareEnergy`),
bound `1`, `∫_A 1 dμ = μ A < ∞` (`A` bounded in the proper space, `IsFiniteMeasureOnCompacts`),
the pointwise limit hypothesis, and `∫_A 1_N dμ = μ(A ∩ N)` (`lintegral_indicator_const`, `N`
Borel by `measurable_squareEnergy`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- The level set `{S = ∞}` of a square energy is Borel. -/
theorem i2_measurableSet_squareEnergy_eq_top {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (T : FamilyKind) (R : ℝ) :
    MeasurableSet {z | squareEnergy μ k T R z = ⊤} :=
  measurableSet_eq_fun (measurable_squareEnergy μ k T R) measurable_const

/-- The restricted integral of the indicator of `{S = ∞}` is `μ(A ∩ {S = ∞})`. -/
theorem i2_lintegral_indicator_eq_top {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (T : FamilyKind) (R : ℝ) (A : Set (Space n)) :
    ∫⁻ z in A, {z | squareEnergy μ k T R z = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) z ∂μ
      = μ (A ∩ {z | squareEnergy μ k T R z = ⊤}) := by
  have hN := i2_measurableSet_squareEnergy_eq_top μ k T R
  rw [lintegral_indicator_const hN, one_mul, Measure.restrict_apply hN, inter_comm]

/-- **Limit of the capped tails** (`i2_cappedTail_limit`). -/
theorem i2_cappedTail_limit_proof : i2_CappedTailLimitStatement := by
  intro n _ k _ _ μ hμ _ T _ R _ A _ hAb hlim
  have := hμ
  rw [← i2_lintegral_indicator_eq_top μ k T R A]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ρ =>
      measurable_const.min (measurable_squareEnergy μ k T ρ)
  · exact Eventually.of_forall fun ρ => ae_of_all _ fun z => min_le_left _ _
  · rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
    exact (hAb.measure_lt_top (μ := μ)).ne
  · exact ae_of_all _ hlim

end ParabolicRectifiability.IntegralCanonical
