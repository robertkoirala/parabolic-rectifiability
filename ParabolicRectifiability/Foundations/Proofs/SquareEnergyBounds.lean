import ParabolicRectifiability.Foundations.Statements.Measurability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Finite-annulus bound and endpoint independence of square finiteness

Proofs of `AnnulusBoundStatement` (`lintegral_betaSq_Ioo_le_annulus`) and
`SquareFinitenessEndpointStatement` (`squareEnergy_lt_top_iff_of_endpoints`).

Both rest on one integrand bound `bf1m45_betaSq_le_of_mem_Icc`: for an available family and
`0 < a ≤ r ≤ b`, `β²(z,r) ≤ a^{-k} μ(closed P(z,b))`. The endpoint-independence statement does
not use the annulus bound.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Shared integrand bound: for an available family and `0 < a ≤ r ≤ b`,
`β²_{μ,T}(z,r) ≤ a^{-k} μ(closedBall z b)`. -/
theorem bf1m45_betaSq_le_of_mem_Icc {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    [Nonempty (Models n k T)] (z : Space n) {a b r : ℝ} (ha : 0 < a) (hr : r ∈ Icc a b) :
    betaSq μ k T z r ≤ (ENNReal.ofReal a)⁻¹ ^ k * μ (Metric.closedBall z b) := by
  have hr0 : 0 < r := ha.trans_le hr.1
  calc betaSq μ k T z r ≤ (ENNReal.ofReal r)⁻¹ ^ k * μ (Metric.ball z r) :=
        betaSq_le_radius_inv_pow_mul_measure μ k T z hr0
    _ ≤ (ENNReal.ofReal a)⁻¹ ^ k * μ (Metric.closedBall z b) := by
        gcongr
        · exact hr.1
        · exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr.2)

/-- The `dr/r` measure of `(a,b)` is `log(b/a)` for `0 < a ≤ b`. -/
theorem bf1m45_scaleMeasure_Ioo {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    scaleMeasure (Ioo a b) = ENNReal.ofReal (Real.log (b / a)) := by
  rw [scaleMeasure_apply _ measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo a b ⊆ Ioi 0 from fun r hr => ha.trans hr.1)]
  have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Icc a b) :=
    continuousOn_const.div continuousOn_id fun r hr => (ha.trans_le hr.1).ne'
  have hint : IntegrableOn (fun r : ℝ => 1 / r) (Ioo a b) volume :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      integral_one_div_of_pos ha (ha.trans_le hab)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (one_div_pos.mpr (ha.trans hr.1)).le

/-- **Finite-annulus bound.** `AnnulusBoundStatement`. -/
theorem lintegral_betaSq_Ioo_le_annulus_proof : AnnulusBoundStatement := by
  intro n _ k _ _ T hT μ hμ _ z a b ha hab
  have := hT
  have := hμ
  refine ⟨?_, ?_⟩
  · calc (∫⁻ r in Ioo a b, betaSq μ k T z r ∂scaleMeasure)
        ≤ ∫⁻ _r in Ioo a b, (ENNReal.ofReal a)⁻¹ ^ k * μ (Metric.closedBall z b)
            ∂scaleMeasure :=
          setLIntegral_mono' measurableSet_Ioo fun r hr =>
            bf1m45_betaSq_le_of_mem_Icc μ k T z ha (Ioo_subset_Icc_self hr)
      _ = _ := by rw [setLIntegral_const, bf1m45_scaleMeasure_Ioo ha hab.le]
  · refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ (measure_closedBall_lt_top μ z b))
      ENNReal.ofReal_lt_top
    exact ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr ha))

/-- For an available family and `0 < R ≤ R'`, the energy up to `R'` exceeds the energy up to
`R` by at most `R^{-k} μ(closed P(z,R')) · scaleMeasure([R,R'])`. -/
theorem bf1m45_squareEnergy_le_add {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    [Nonempty (Models n k T)] (z : Space n) {R R' : ℝ} (hR : 0 < R) :
    squareEnergy μ k T R' z ≤ squareEnergy μ k T R z +
      (ENNReal.ofReal R)⁻¹ ^ k * μ (Metric.closedBall z R') * scaleMeasure (Icc R R') := by
  have hsub : Ioo 0 R' ⊆ Ioo 0 R ∪ Icc R R' := by
    intro r hr
    rcases lt_or_ge r R with h | h
    · exact Or.inl ⟨hr.1, h⟩
    · exact Or.inr ⟨h, hr.2.le⟩
  unfold squareEnergy
  calc (∫⁻ r in Ioo 0 R', betaSq μ k T z r ∂scaleMeasure)
      ≤ ∫⁻ r in Ioo 0 R ∪ Icc R R', betaSq μ k T z r ∂scaleMeasure := lintegral_mono_set hsub
    _ ≤ (∫⁻ r in Ioo 0 R, betaSq μ k T z r ∂scaleMeasure) +
          ∫⁻ r in Icc R R', betaSq μ k T z r ∂scaleMeasure := lintegral_union_le _ _ _
    _ ≤ (∫⁻ r in Ioo 0 R, betaSq μ k T z r ∂scaleMeasure) +
          ∫⁻ _r in Icc R R', (ENNReal.ofReal R)⁻¹ ^ k * μ (Metric.closedBall z R')
            ∂scaleMeasure :=
        add_le_add le_rfl (setLIntegral_mono' measurableSet_Icc fun r hr =>
          bf1m45_betaSq_le_of_mem_Icc μ k T z hR hr)
    _ = _ := by rw [setLIntegral_const]

/-- For an unavailable family the square energy is `⊤` at every positive endpoint. -/
theorem bf1m45_squareEnergy_eq_top_of_isEmpty {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) [IsEmpty (Models n k T)] (z : Space n) {R : ℝ} (hR : 0 < R) :
    squareEnergy μ k T R z = ⊤ := by
  have hpos : scaleMeasure (Ioo 0 R) ≠ 0 := by
    rw [scaleMeasure_apply _ measurableSet_Ioo]
    apply ne_of_gt
    rw [setLIntegral_pos_iff measurable_scaleDensity]
    have hsupp : Function.support (fun r : ℝ => ENNReal.ofReal (1 / r)) ∩
        (Ioo 0 R ∩ Ioi 0) = Ioo 0 R := by
      ext r
      simp only [Function.mem_support, mem_inter_iff, mem_Ioo, mem_Ioi, ne_eq,
        ENNReal.ofReal_eq_zero, not_le, one_div, inv_pos]
      tauto
    rw [hsupp, Real.volume_Ioo]
    simpa using hR
  unfold squareEnergy
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => (⊤ : ℝ≥0∞))
    (fun r hr => betaSq_of_isEmpty μ k T z hr.1), setLIntegral_const, ENNReal.top_mul hpos]

/-- The one-sided form of endpoint independence: `0 < R ≤ R'`. -/
theorem bf1m45_lt_top_iff_of_le {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    (k : ℕ) (T : FamilyKind) (z : Space n) {R R' : ℝ} (hR : 0 < R) (hRR' : R ≤ R') :
    squareEnergy μ k T R z < ⊤ ↔ squareEnergy μ k T R' z < ⊤ := by
  have hmono : squareEnergy μ k T R z ≤ squareEnergy μ k T R' z :=
    lintegral_mono_set (Ioo_subset_Ioo_right hRR')
  refine ⟨fun h => ?_, fun h => hmono.trans_lt h⟩
  rcases isEmpty_or_nonempty (Models n k T) with hT | hT
  · rw [bf1m45_squareEnergy_eq_top_of_isEmpty μ k T z hR] at h
    exact absurd h (lt_irrefl _)
  · refine (bf1m45_squareEnergy_le_add μ k T z (R' := R') hR).trans_lt
      (ENNReal.add_lt_top.mpr ⟨h, ?_⟩)
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ (measure_closedBall_lt_top μ z R'))
      (scaleMeasure_Icc_lt_top hR)
    exact ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hR))

/-- **Endpoint independence of finiteness.** `SquareFinitenessEndpointStatement`. -/
theorem squareEnergy_lt_top_iff_of_endpoints_proof : SquareFinitenessEndpointStatement := by
  intro n _ k _ _ T μ hμ _ z R R' hR hR'
  have := hμ
  rcases le_total R R' with h | h
  · exact bf1m45_lt_top_iff_of_le μ k T z hR h
  · exact (bf1m45_lt_top_iff_of_le μ k T z hR' h).symm

end ParabolicRectifiability.Foundations
