import ParabolicRectifiability.BetaP.Statements.Main
import ParabolicRectifiability.Enhancements.Proofs.Scaling.RescaledCoreDecomposition

/-! # Transport of a unit beta-`p` decomposition

`cscb_isBetaPDecomposition_of_rescaledSource_proof` proves
`IsBetaPDecomposition.of_rescaledSource`: a unit beta-`p` decomposition of a rescaled source
transports back to a decomposition of the original source at `(q, R)`.

With `S = similarity q R hR` and `ν = rescaledSource μ k q R hR = R^{-k} S_# μ`, the measures
`μ_X = R^k (S.symm)_# ν_X` decompose `μ` at `(q, R)` with the same constant and loss `R^k L`:
the measure identity is `R^k (S.symm)_# (R^{-k} S_# μ) = μ`; `S.symm⁻¹' P(q,R) = P(0,1)`; the
actual support of `μ_X` is `S⁻¹' supp ν_X` (`fsim_support_restrict_preimage_homeomorph`);
the support bundle comes from the similarity covariance of the support bounds and of the covers
(regular-class covariance, with the half-time bracket integrability discharged by
`fhpa_halfTimeBracketIntegrable`), exactly as in the scaled-core argument of the `Enhancements`
development, whose `sc2c_` lemmas are reused.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Enhancements.ScaledCoreTree

/-- `S.symm⁻¹' P(q,R) = P(0,1)`. -/
theorem cscb_preimage_symm_ball {n : ℕ} (q : Space n) (R : ℝ) (hR : 0 < R) :
    (similarity q R hR).symm ⁻¹' Metric.ball q R = Metric.ball (point 0 0) 1 := by
  rw [← sc2c_preimage_similarity_unitBall q R hR, ← preimage_comp, Homeomorph.self_comp_symm,
    preimage_id]

/-- Evaluation of `R^k (S.symm)_# m` on any set. -/
theorem cscb_lift_apply {n : ℕ} (m : Measure (Space n)) (k : ℕ) (q : Space n) (R : ℝ)
    (hR : 0 < R) (A : Set (Space n)) :
    (ENNReal.ofReal R ^ k • m.map (similarity q R hR).symm) A =
      ENNReal.ofReal R ^ k * m ((similarity q R hR).symm ⁻¹' A) := by
  rw [Measure.smul_apply, smul_eq_mul]
  congr 1
  exact (similarity q R hR).symm.toMeasurableEquiv.map_apply A

/-- `R^{-k} S_# (R^k (S.symm)_# m) = m`. -/
theorem cscb_rescale_lift {n : ℕ} (m : Measure (Space n)) (k : ℕ) (q : Space n) (R : ℝ)
    (hR : 0 < R) :
    (ENNReal.ofReal R)⁻¹ ^ k • (ENNReal.ofReal R ^ k • m.map (similarity q R hR).symm).map
      (similarity q R hR) = m := by
  have h0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  rw [Measure.map_smul _ (similarity q R hR).measurable.aemeasurable,
    Measure.map_map (similarity q R hR).measurable (similarity q R hR).symm.measurable,
    Homeomorph.self_comp_symm, Measure.map_id, smul_smul,
    ← mul_pow, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_pow, one_smul]

/-- `R^k (S.symm)_# (rescaledSource μ k q R hR) = μ`. -/
theorem cscb_lift_rescaledSource {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (q : Space n) (R : ℝ)
    (hR : 0 < R) :
    ENNReal.ofReal R ^ k • (rescaledSource μ k q R hR).map (similarity q R hR).symm = μ := by
  have h0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  rw [rescaledSource, Measure.map_smul _ (similarity q R hR).symm.measurable.aemeasurable,
    Measure.map_map (similarity q R hR).symm.measurable
    (similarity q R hR).measurable, Homeomorph.symm_comp_self, Measure.map_id, smul_smul,
    ← mul_pow, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_pow, one_smul]

/-- The actual support of `R^k (S.symm)_# m` is `S⁻¹' supp m` (`fsim_support_restrict_preimage_homeomorph` with `A = univ`). -/
theorem cscb_support_lift {n : ℕ} (m : Measure (Space n)) (k : ℕ) (q : Space n) (R : ℝ)
    (hR : 0 < R) :
    (ENNReal.ofReal R ^ k • m.map (similarity q R hR).symm).support =
      similarity q R hR ⁻¹' m.support := by
  have h := fsim_support_restrict_preimage_homeomorph
    (ENNReal.ofReal R ^ k • m.map (similarity q R hR).symm) (similarity q R hR)
    ((ENNReal.ofReal R)⁻¹ ^ k) (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hR).ne')) univ
  rwa [preimage_univ, Measure.restrict_univ, Measure.restrict_univ, cscb_rescale_lift] at h

/-- **Transport of a unit decomposition**: the statement
`IsBetaPDecomposition.of_rescaledSource`. -/
theorem cscb_isBetaPDecomposition_of_rescaledSource_proof {n : ℕ} (_hn : 1 ≤ n) {k : ℕ} (_hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {T : FamilyKind} {μ : Measure (Space n)} {q : Space n} {R : ℝ}
    (hR : 0 < R) {C loss : ℝ} (_hC : 0 < C) {νplus νH νV : Measure (Space n)}
    (h : IsBetaPDecomposition k T C (point 0 0) 1 loss (rescaledSource μ k q R hR) νplus νH νV) :
    ∃ μplus μH μV : Measure (Space n),
      IsBetaPDecomposition k T C q R (R ^ k * loss) μ μplus μH μV := by
  have hb := cscb_preimage_symm_ball q R hR
  have hm := (similarity q R hR).symm.measurable
  have hH := fsim_hausdorffP_preimage_similarity n k q R hR
  have hT := fsim_parabolicVolume_thickening_preimage_similarity q R hR
  have hregS : ∀ (W : Submodule ℝ (Spatial n)) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ),
      IsGeneralRegularVerticalFunction W F ε →
        IsGeneralRegularVerticalFunction W
          (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking q.2.val)
            R p)) ε :=
    fun W F ε hF => fsim_isGeneralRegularVerticalFunction_baseSimilarity
      fhpa_halfTimeBracketIntegrable W R hR q.2.val F ε hF
  have hbundle : HasRegularSupportBounds k C q R
      (similarity q R hR ⁻¹' νH.support) (similarity q R hR ⁻¹' νV.support) := by
    have h' := fsim_hasRegularSupportBounds_preimage_similarity hkn C q R hR hH hT (point 0 0) 1
      _ _ h.supports
      (fun ε hε => fsim_hasHorizontalGraphCover_preimage_similarity q R hR hH _ ε
        (h.supports.horizontal_graphs ε hε))
      (fun ε hε => fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity q R hR hH hregS
        _ ε (h.supports.vertical_graphs ε hε))
    rwa [sc2c_similarity_symm_zero, mul_one] at h'
  refine ⟨ENNReal.ofReal R ^ k • νplus.map (similarity q R hR).symm,
    ENNReal.ofReal R ^ k • νH.map (similarity q R hR).symm,
    ENNReal.ofReal R ^ k • νV.map (similarity q R hR).symm, ?_⟩
  exact
    { measure_eq := by
        rw [← smul_add, ← smul_add, ← Measure.map_add _ _ hm, ← Measure.map_add _ _ hm,
          ← h.measure_eq, cscb_lift_rescaledSource]
      remainder_bound := by
        rw [cscb_lift_apply, hb, ENNReal.ofReal_mul (pow_nonneg hR.le k),
          ENNReal.ofReal_pow hR.le]
        have hr := h.remainder_bound
        gcongr
      horizontal_carried := by
        rw [cscb_lift_apply, preimage_compl, hb, h.horizontal_carried, mul_zero]
      vertical_carried := by
        rw [cscb_lift_apply, preimage_compl, hb, h.vertical_carried, mul_zero]
      horizontal_unavailable := fun hu => by
        rw [h.horizontal_unavailable hu, Measure.map_zero, smul_zero]
      vertical_unavailable := fun hu => by
        rw [h.vertical_unavailable hu, Measure.map_zero, smul_zero]
      horizontal_disallowed := fun hv => by
        rw [h.horizontal_disallowed hv, Measure.map_zero, smul_zero]
      vertical_disallowed := fun hv => by
        rw [h.vertical_disallowed hv, Measure.map_zero, smul_zero]
      supports := by
        rw [cscb_support_lift, cscb_support_lift]
        exact hbundle }

end ParabolicRectifiability.BetaP
