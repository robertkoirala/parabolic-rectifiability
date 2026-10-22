import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # The bad cost of the slab covering

Proofs of `BadCostStatement` (in implication form over `SlabBasicsStatement`) and of the
numerical bound `log 10 ≤ 3`.

* `d1fbad_scaleMeasure_Ico`: the `dr/r` measure of `[ℓ/10, ℓ)` is `log 10` for `ℓ > 0`.
* `d1f_badCost_proof`: countable subadditivity over the bad cells, `Measure.prod_prod` on each slab,
  `μ(Q ∩ P₀) ≤ μ(Q)`, and the bad mass of the stopping decomposition.
* `d1f_logTen_le_three_proof`: `log 10 ≤ log 16 = 4 log 2 < 4 · 0.6931471808 < 3`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- The `dr/r` measure of the decade `[ℓ/10, ℓ)` is exactly `log 10`. -/
theorem d1fbad_scaleMeasure_Ico {ℓ : ℝ} (hℓ : 0 < ℓ) :
    scaleMeasure (Ico (ℓ / 10) ℓ) = ENNReal.ofReal (Real.log 10) := by
  have h10 : 0 < ℓ / 10 := by positivity
  have hle : ℓ / 10 ≤ ℓ := by linarith
  rw [scaleMeasure_apply _ measurableSet_Ico,
    inter_eq_left.mpr (show Ico (ℓ / 10) ℓ ⊆ Ioi 0 from fun r hr => h10.trans_le hr.1)]
  have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Icc (ℓ / 10) ℓ) :=
    continuousOn_const.div continuousOn_id fun r hr => (h10.trans_le hr.1).ne'
  have hint : IntegrableOn (fun r : ℝ => 1 / r) (Ico (ℓ / 10) ℓ) volume :=
    hcont.integrableOn_Icc.mono_set Ico_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hle, integral_one_div_of_pos h10 hℓ,
      div_div_cancel₀ hℓ.ne']
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with r hr
    exact (one_div_pos.mpr (h10.trans_le hr.1)).le

/-- The cell sides `ℓ_j = 10^{-j} ℓ₀` of a direct partition are positive. -/
theorem d1fbad_scale_pos {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (j : ℕ) : 0 < P.scale j := by
  show 0 < coherentScale ℓ₀ j
  exact div_pos P.scale_pos (pow_pos (by norm_num) j)

/-- The point–scale mass of one slab is at most `μ(Q) · log 10`. -/
theorem d1fbad_slab_le {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (μ : Measure (Space n)) (a : Space n) (R : ℝ) (Q : ℕ × Space n) :
    pointScaleMeasure μ (slab P a R Q) ≤ μ (P.cellOf Q) * ENNReal.ofReal (Real.log 10) := by
  rw [pointScaleMeasure, slab, Measure.prod_prod, d1fbad_scaleMeasure_Ico (d1fbad_scale_pos P Q.1)]
  gcongr
  exact inter_subset_left

/-- **The bad cost**: `∬_𝓑 dμ dr/r ≤ log 10 · ∑_{bad} μ(Q) ≤
(log 10) K R^k`, in implication form over the slab basics. -/
theorem d1f_badCost_proof : SlabBasicsStatement → BadCostStatement := by
  intro hB n μ a R P k Λ b K SD
  have hcount : SD.bad.Countable := by
    refine (hB n μ a R P).1.mono fun Q hQ => ?_
    obtain ⟨z₀, -, -, hbelow⟩ := SD.bad_forest Q hQ
    exact hbelow.1
  calc pointScaleMeasure μ (badSlabs SD)
      ≤ ∑' Q : SD.bad, pointScaleMeasure μ (slab P a R Q) :=
        measure_biUnion_le _ hcount _
    _ ≤ ∑' Q : SD.bad, μ (P.cellOf Q.1) * ENNReal.ofReal (Real.log 10) :=
        ENNReal.tsum_le_tsum fun Q => d1fbad_slab_le P μ a R Q.1
    _ = (∑' Q : SD.bad, μ (P.cellOf Q.1)) * ENNReal.ofReal (Real.log 10) :=
        ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (K * R ^ k) * ENNReal.ofReal (Real.log 10) := by
        gcongr
        exact SD.bad_mass
    _ = ENNReal.ofReal (Real.log 10 * (K * R ^ k)) := by
        rw [mul_comm, ENNReal.ofReal_mul (Real.log_nonneg (by norm_num))]

/-- **`log 10 ≤ 3`** (so the bad-cost constant may be taken `C₆ = 3`):
`log 10 ≤ log 16 = 4 log 2 < 4 · 0.6931471808 < 3`. -/
theorem d1f_logTen_le_three_proof : Real.log 10 ≤ 3 := by
  have h16 : Real.log 10 ≤ Real.log ((2 : ℝ) ^ 4) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h16
  have h2 := Real.log_two_lt_d9
  norm_num at h16 h2
  linarith

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
