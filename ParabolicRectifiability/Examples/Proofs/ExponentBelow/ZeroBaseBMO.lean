import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements
import ParabolicRectifiability.Analysis.MeanOscillation

/-! # Interval BMO on the zero spatial base

The zero base has only a time coordinate. Its intrinsic ball is the ordinary
interval `(τ-r², τ+r²)`, and its volume is `2r²`. The lift from real values to
the one-dimensional normal space is an isometric scalar embedding, so its
vector average and mean oscillation are the corresponding scalar ones.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private def e2_zeroBaseUnit : zeroDirectionᗮ :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), by
    rw [Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top⟩

private theorem e2_zeroBaseLift_smul (h : ℝ → ℝ) (p : SubspaceSpace zeroDirection) :
    zeroBaseLift h p = h p.2.val • e2_zeroBaseUnit := by
  apply Subtype.ext
  ext i
  simp [zeroBaseLift, e2_zeroBaseUnit, EuclideanSpace.single]

private theorem e2_zeroBaseUnit_norm : ‖e2_zeroBaseUnit‖ = 1 := by
  simp [e2_zeroBaseUnit, EuclideanSpace.single]

private def e2_zeroBaseTimeHomeomorph : SubspaceSpace zeroDirection ≃ₜ ℝ where
  toEquiv :=
    { toFun := fun p => p.2.val
      invFun := fun t => ((0 : zeroDirection), Metric.Snowflaking.toSnowflaking t)
      left_inv := by
        rintro ⟨w, t⟩
        have hw : w = 0 := Subsingleton.elim _ _
        subst w
        cases t
        rfl
      right_inv := by intro t; rfl }
  continuous_toFun := continuous_snd.comp (subspaceTimeHomeomorph zeroDirection).continuous
  continuous_invFun := continuous_const.prodMk Metric.Snowflaking.continuous_toSnowflaking

private theorem e2_zeroBaseTimeHomeomorph_apply (p : SubspaceSpace zeroDirection) :
    e2_zeroBaseTimeHomeomorph p = p.2.val := rfl

private theorem e2_zeroBaseTimeHomeomorph_symm_apply (t : ℝ) :
    e2_zeroBaseTimeHomeomorph.symm t =
      ((0 : zeroDirection), Metric.Snowflaking.toSnowflaking t) := rfl

private theorem e2_zeroDirection_volume_univ :
    (volume : Measure zeroDirection) univ = 1 := by
  have hdim : Module.finrank ℝ zeroDirection = 0 := by simp [zeroDirection]
  have hcoord :=
    (subspaceCoordinates_spatial_measurePreserving zeroDirection).measure_preimage_equiv
      (univ : Set (Spatial (Module.finrank ℝ zeroDirection)))
  have h0 : (volume : Measure (Spatial 0)) (univ : Set (Spatial 0)) = 1 := by
    rw [volume_euclideanSpace_eq_dirac (Fin 0)]
    simp
  calc
    (volume : Measure zeroDirection) univ =
        (volume : Measure (Spatial (Module.finrank ℝ zeroDirection))) univ := by
      simpa using hcoord
    _ = (volume : Measure (Spatial 0)) (univ : Set (Spatial 0)) := by rw [hdim]
    _ = 1 := h0

private theorem e2_zeroBaseTime_measurePreserving :
    MeasurePreserving e2_zeroBaseTimeHomeomorph (intrinsicParabolicVolume zeroDirection) volume := by
  let : IsProbabilityMeasure (volume : Measure zeroDirection) :=
    ⟨e2_zeroDirection_volume_univ⟩
  have hprod : MeasurePreserving (Prod.snd : zeroDirection × ℝ → ℝ)
      ((volume : Measure zeroDirection).prod (volume : Measure ℝ)) (volume : Measure ℝ) :=
    measurePreserving_snd
  have h := hprod.comp (subspaceTime_measurePreserving zeroDirection)
  convert h using 1
  ext p
  rfl

private theorem e2_zeroBase_preimage_interval (p : SubspaceSpace zeroDirection) {r : ℝ}
    (hr : 0 < r) :
    e2_zeroBaseTimeHomeomorph ⁻¹' Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2) =
      Metric.ball p r := by
  rcases p with ⟨w, τ⟩
  rcases τ with ⟨τ⟩
  ext q
  rcases q with ⟨v, s⟩
  rcases s with ⟨s⟩
  have hvw : v = w := Subsingleton.elim _ _
  subst v
  change s ∈ Ioo (τ - r ^ 2) (τ + r ^ 2) ↔
    dist ((w, Metric.Snowflaking.toSnowflaking s) : SubspaceSpace zeroDirection)
      (w, Metric.Snowflaking.toSnowflaking τ) < r
  rw [dist_subspace_time, sub_self, norm_zero,
    max_eq_right (Real.sqrt_nonneg _), Real.sqrt_lt (abs_nonneg _) hr.le,
    abs_sub_lt_iff]
  constructor
  · rintro ⟨hs₁, hs₂⟩
    constructor <;> linarith
  · rintro ⟨hs₁, hs₂⟩
    constructor <;> linarith

private theorem e2_zeroBase_setIntegral (p : SubspaceSpace zeroDirection) {r : ℝ}
    (hr : 0 < r) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) :
    (∫ t in Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2), F t ∂volume) =
      ∫ q in Metric.ball p r, F (e2_zeroBaseTimeHomeomorph q)
        ∂intrinsicParabolicVolume zeroDirection := by
  rw [← e2_zeroBase_preimage_interval p hr]
  exact (e2_zeroBaseTime_measurePreserving.setIntegral_preimage_emb
    e2_zeroBaseTimeHomeomorph.measurableEmbedding F
      (Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2))).symm

private theorem e2_zeroBase_ball_volume (p : SubspaceSpace zeroDirection) {r : ℝ}
    (hr : 0 < r) :
    intrinsicParabolicVolume zeroDirection (Metric.ball p r) = ENNReal.ofReal (2 * r ^ 2) := by
  rw [intrinsicParabolicVolume_ball zeroDirection p r hr]
  have hdim : Module.finrank ℝ zeroDirection = 0 := by simp [zeroDirection]
  rw [hdim, omega_zero, Nat.zero_add]
  rw [← ENNReal.ofReal_pow hr.le]
  calc
    2 * 1 * ENNReal.ofReal (r ^ 2) = ENNReal.ofReal 2 * ENNReal.ofReal (r ^ 2) := by norm_num
    _ = ENNReal.ofReal (2 * r ^ 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]

private theorem e2_zeroBase_ball_average (h : ℝ → ℝ) (p : SubspaceSpace zeroDirection)
    {r : ℝ} (hr : 0 < r) :
    parabolicBallAverage zeroDirection (zeroBaseLift h) p r =
      (((2 * r ^ 2)⁻¹ * ∫ t in Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2), h t ∂volume) : ℝ) •
        e2_zeroBaseUnit := by
  have hInt :
      ∫ q in Metric.ball p r, zeroBaseLift h q ∂intrinsicParabolicVolume zeroDirection =
        (∫ t in Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2), h t ∂volume) • e2_zeroBaseUnit := by
    calc
      _ = ∫ q in Metric.ball p r, h (e2_zeroBaseTimeHomeomorph q) • e2_zeroBaseUnit
          ∂intrinsicParabolicVolume zeroDirection := by
            apply setIntegral_congr_ae
            · exact measurableSet_ball
            · filter_upwards with q hq
              simpa only [e2_zeroBaseTimeHomeomorph_apply] using e2_zeroBaseLift_smul h q
      _ = ∫ t in Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2),
            h t • e2_zeroBaseUnit ∂volume :=
          (e2_zeroBase_setIntegral p hr (fun t => h t • e2_zeroBaseUnit)).symm
      _ = (∫ t in Ioo (p.2.val - r ^ 2) (p.2.val + r ^ 2), h t ∂volume) •
            e2_zeroBaseUnit := by
          exact integral_smul_const _ _
  have hvol := e2_zeroBase_ball_volume p hr
  rw [parabolicBallAverage, hInt, hvol]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [smul_smul]

theorem e2_zeroBase_bmo_proof : E2ZeroBaseBMOStatement := by
  intro h C hBMO
  have hC : 0 ≤ C := by
    have hnonneg :
        0 ≤ ∫ s in Ioo (-1 : ℝ) 1,
          |h s - (2 * (1 : ℝ))⁻¹ * (∫ u in Ioo (-1 : ℝ) 1, h u)| ∂volume :=
      integral_nonneg (fun _ => abs_nonneg _)
    have hbound := hBMO.2 0 1 one_pos
    nlinarith
  refine ⟨Real.toNNReal C, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [Real.coe_toNNReal C hC]
      exact hC
    · have htime : LocallyIntegrable (fun t : ℝ => h t • e2_zeroBaseUnit) volume :=
        locallyIntegrable_iff.2 fun K hK =>
          (hBMO.1.integrableOn_isCompact hK).smul_const e2_zeroBaseUnit
      have hmp : MeasurePreserving e2_zeroBaseTimeHomeomorph.toMeasurableEquiv
          (intrinsicParabolicVolume zeroDirection) volume := e2_zeroBaseTime_measurePreserving
      rw [← hmp.symm.map_eq]
      refine (locallyIntegrable_map_homeomorph e2_zeroBaseTimeHomeomorph.symm).mpr ?_
      have hfun : (fun t : ℝ => zeroBaseLift h (e2_zeroBaseTimeHomeomorph.symm t)) =
          fun t => h t • e2_zeroBaseUnit := by
        funext t
        rw [e2_zeroBaseTimeHomeomorph_symm_apply, e2_zeroBaseLift_smul]
        rfl
      change LocallyIntegrable (fun t : ℝ => zeroBaseLift h (e2_zeroBaseTimeHomeomorph.symm t)) volume
      rw [hfun]
      exact htime
    · intro p r hr
      let τ := p.2.val
      let c : ℝ := (2 * r ^ 2)⁻¹ *
        (∫ t in Ioo (τ - r ^ 2) (τ + r ^ 2), h t ∂volume)
      have hvol := intrinsicBall_volume_pos_lt_top zeroDirection p hr
      have hdenpos :
          0 < (intrinsicParabolicVolume zeroDirection (Metric.ball p r)).toReal :=
        ENNReal.toReal_pos hvol.1.ne' hvol.2.ne
      have hvolR :
          (intrinsicParabolicVolume zeroDirection (Metric.ball p r)).toReal = 2 * r ^ 2 := by
        rw [e2_zeroBase_ball_volume p hr, ENNReal.toReal_ofReal (by positivity)]
      have hmean : parabolicBallAverage zeroDirection (zeroBaseLift h) p r =
          c • e2_zeroBaseUnit := by
        simpa [τ, c] using e2_zeroBase_ball_average h p hr
      have hnum :
          (∫ q in Metric.ball p r,
            ‖zeroBaseLift h q - parabolicBallAverage zeroDirection (zeroBaseLift h) p r‖
              ∂intrinsicParabolicVolume zeroDirection) =
            ∫ t in Ioo (τ - r ^ 2) (τ + r ^ 2), |h t - c| ∂volume := by
        calc
          _ = ∫ q in Metric.ball p r,
                |h (e2_zeroBaseTimeHomeomorph q) - c| ∂intrinsicParabolicVolume zeroDirection := by
              apply setIntegral_congr_ae
              · exact measurableSet_ball
              · filter_upwards with q hq
                rw [e2_zeroBaseLift_smul h q, hmean, ← sub_smul, norm_smul,
                  e2_zeroBaseUnit_norm, mul_one, Real.norm_eq_abs]
                simp only [e2_zeroBaseTimeHomeomorph_apply]
          _ = ∫ t in Ioo (τ - r ^ 2) (τ + r ^ 2), |h t - c| ∂volume := by
              simpa [τ] using
                (e2_zeroBase_setIntegral p hr (fun t => |h t - c|)).symm
      have hscalar := hBMO.2 τ (r ^ 2) (by positivity)
      have hratio :
          (∫ t in Ioo (τ - r ^ 2) (τ + r ^ 2), |h t - c| ∂volume) /
            (intrinsicParabolicVolume zeroDirection (Metric.ball p r)).toReal ≤ C := by
        rw [hvolR]
        apply (div_le_iff₀ (by positivity : 0 < 2 * r ^ 2)).2
        simpa [c, τ] using hscalar
      rw [hnum]
      exact hratio.trans (by rw [Real.coe_toNNReal C hC])
  · rw [Real.coe_toNNReal C hC]

end ParabolicRectifiability.Examples
