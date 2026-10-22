import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Analysis.TraceExtension.Similarity
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Measurability

/-! # The vertical affine Carleson bounds

Proof of `ba1_vertical_unit_carleson` and `ba1_vertical_carleson`; the statement types are copied
below.

Notation: `μ = parabolicVolume m`, `κ_F(y,s)² = affineErrorSq μ F y s`, `Ψ` the ordinary
coordinates `fourierToParabolicMeasurableEquiv m`, `T = similarity 0 R` (so `T = δ_{1/R}`,
`T⁻¹ = δ_R`).

* **Unit scale** (`ba1_vertical_unit_carleson_proof`). The localization input at `p₀ = z` gives
  `H ∈ L²` with `H = F - F(z)` on `P(z,2)`. For `y ∈ P(z,1)` and `0 < s < 1`,
  `P(y,s) ⊆ P(z,2)`; the competitor `(a + F(z), B)` for `F` has the fit integral of `(a,B)` for
  `H` over `Ψ⁻¹ P(y,s) = coordBall (Ψ⁻¹ y) s` (`Ψ` measure preserving), so
  `κ_F(y,s)² ≤ FourierAffine.affineEnergy H (Ψ⁻¹ y) s` (both normalized by `s^{-(m+4)}`).
  Enlarging to all centres and scales and transporting by `Ψ⁻¹` gives
  `affineCarlesonEnergy H ≤ C₂ E(H) ≤ C₂ C₁ (L² + B²)`.
* **All scales, vector** (`ba1_vertical_carleson_proof`), constant `max(1,d) C_m`. Scalar: 
  `traceErrorSq_similarity_proof` (`K = univ`, `v = 0`, `x₀ = 0`) gives
  `κ_G(y,s)² = κ_{G_R}(T y, s/R)²` with `G_R = R⁻¹ G ∘ δ_R`; the `ds/s` invariance and
  `setLIntegral_comp_similarity` give `Carl_G(z,R) = R^{m+2} Carl_{G_R}(T z, 1)`; the
  dilation hypothesis keeps the Lipschitz and BMO data, so the unit hypothesis applies.
  Vector: `κ_F² ≤ Σ_α κ_{F^α}²` (coordinatewise competitors, `ENNReal.iInf_sum`). The sum is
  moved out of the two integrals through the measurability of compact trace errors
  (`measurable_traceErrorSq_of_isCompact_proof`, `K = closedBall z (2R)`, on which the
  errors at centres in `P(z,R)` and scales `< R` coincide with the unrestricted ones).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ### Small facts -/

/-- The base dimension of `ℝ^m × Time` is `m + 2` (local copy of a private lemma). -/
theorem b1vcar_baseDimension (m : ℕ) : baseDimension (Spatial m) = m + 2 := by
  show Module.finrank ℝ (Spatial m) + 2 = m + 2
  rw [finrank_euclideanSpace_fin]

/-- The scale measure `ds/s` is invariant under `s ↦ c s`, `c > 0` (local copy of a private
lemma of the similarity covariance). -/
theorem b1vcar_scaleMeasure_map_mul_left {c : ℝ} (hc : 0 < c) :
    Measure.map (fun s => c * s) scaleMeasure = scaleMeasure := by
  ext A hA
  have hA' : MeasurableSet (A ∩ Ioi 0) := hA.inter measurableSet_Ioi
  have hpre : MeasurableSet ((fun s => c * s) ⁻¹' A) := measurable_const_mul c hA
  rw [Measure.map_apply (measurable_const_mul c) hA, scaleMeasure_apply _ hpre,
    scaleMeasure_apply _ hA]
  have hset : (fun s => c * s) ⁻¹' A ∩ Ioi 0 = (fun s => c * s) ⁻¹' (A ∩ Ioi 0) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, mul_pos hc h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pos_of_mul_pos_right h2 hc.le⟩
  rw [hset, ← lintegral_indicator (measurable_const_mul c hA'), ← lintegral_indicator hA']
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ≥0∞,
      G = (A ∩ Ioi 0).indicator (fun t => ENNReal.ofReal (1 / t)) := ⟨_, rfl⟩
  rw [← hG]
  have hfun : ∀ r, ((fun s => c * s) ⁻¹' (A ∩ Ioi 0)).indicator
      (fun r => ENNReal.ofReal (1 / r)) r = ENNReal.ofReal c * G (c * r) := by
    intro r
    rw [hG]
    by_cases hr : c * r ∈ A ∩ Ioi 0
    · rw [indicator_of_mem (show r ∈ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_mem hr, ← ENNReal.ofReal_mul hc.le, mul_one_div,
        div_mul_cancel_left₀ hc.ne', one_div]
    · rw [indicator_of_notMem (show r ∉ (fun s => c * s) ⁻¹' (A ∩ Ioi 0) from hr),
        indicator_of_notMem hr, mul_zero]
  have hmap : ∫⁻ r, G (c * r) = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
    calc
      ∫⁻ r, G (c * r) = ∫⁻ t, G t ∂(Measure.map (fun s => c * s) volume) :=
        (lintegral_map_equiv G (MeasurableEquiv.mulLeft₀ c hc.ne')).symm
      _ = ∫⁻ t, G t ∂(ENNReal.ofReal |c⁻¹| • volume) := by
        rw [Real.map_volume_mul_left hc.ne']
      _ = ENNReal.ofReal |c⁻¹| * ∫⁻ t, G t := by
        rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_congr hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne',
    ENNReal.ofReal_one, one_mul]

/-- Change of scale `t = c s` for `ds/s`, valid for every function (local copy of a private
lemma of the similarity covariance). -/
theorem b1vcar_setLIntegral_scaleMeasure_comp_mul_left {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℝ≥0∞) (T : Set ℝ) :
    ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure = ∫⁻ t in T, f t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  symm
  calc
    ∫⁻ t in T, f t ∂scaleMeasure = ∫⁻ t in T, f t ∂(Measure.map e scaleMeasure) := by
      rw [he, b1vcar_scaleMeasure_map_mul_left hc]
    _ = ∫⁻ t, f t ∂((scaleMeasure.restrict (e ⁻¹' T)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, f (e s) ∂(scaleMeasure.restrict (e ⁻¹' T)) := lintegral_map_equiv f e
    _ = ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure := by
      rw [he]

/-! ### Unit scale: comparison with the Fourier-side affine energy -/

/-- The ordinary coordinates carry parabolic balls onto coordinate balls. -/
theorem b1vcar_preimage_ball {m : ℕ} (y : Space m) {s : ℝ} (hs : 0 < s) :
    (fourierToParabolicMeasurableEquiv m) ⁻¹' Metric.ball y s =
      FourierAffine.coordBall ((fourierToParabolicMeasurableEquiv m).symm y) s := by
  ext x
  have h := mem_ball_point y.1 (WithLp.ofLp x).1 y.2.val (WithLp.ofLp x).2 s hs
  simp only [FourierAffine.coordBall, Set.mem_preimage, fourierToParabolicMeasurableEquiv_apply,
    fourierToParabolicMeasurableEquiv_symm_apply, Set.mem_ofPred_eq, WithLp.ofLp_toLp]
  exact h

/-- Fit integrals of `F` with the competitor `(a + F(z), B)` are fit integrals of `H` with
`(a, B)`, when `H = F - F(z)` on `P(z,2) ⊇ P(y,s)`. -/
theorem b1vcar_fit_eq {m : ℕ} (F : Space m → ℝ) (H : FourierSpace m → ℝ) (z y : Space m)
    {s : ℝ} (hs : 0 < s) (hsub : Metric.ball y s ⊆ Metric.ball z 2)
    (hH : ∀ x : FourierSpace m, fourierToParabolic m x ∈ Metric.ball z 2 →
      H x = F (fourierToParabolic m x) - F z)
    (a : ℝ) (B : Spatial m →L[ℝ] ℝ) :
    affineFitIntegral (parabolicVolume m) F (a + F z) B y s =
      ∫⁻ x in FourierAffine.coordBall ((fourierToParabolicMeasurableEquiv m).symm y) s,
        ‖H x - (a + B (WithLp.ofLp x).1)‖ₑ ^ 2 := by
  have hmp := fourierToParabolic_measurePreserving m
  have hemb := (fourierToParabolicMeasurableEquiv m).measurableEmbedding
  have hpre := b1vcar_preimage_ball y hs
  calc affineFitIntegral (parabolicVolume m) F (a + F z) B y s
      = ∫⁻ q in Metric.ball y s, ‖F q - (a + F z + B q.1)‖ₑ ^ 2 ∂parabolicVolume m := rfl
    _ = ∫⁻ x in (fourierToParabolicMeasurableEquiv m) ⁻¹' Metric.ball y s,
          ‖F (fourierToParabolicMeasurableEquiv m x) -
            (a + F z + B (fourierToParabolicMeasurableEquiv m x).1)‖ₑ ^ 2 :=
        (hmp.setLIntegral_comp_preimage_emb hemb
          (fun q => ‖F q - (a + F z + B q.1)‖ₑ ^ 2) (Metric.ball y s)).symm
    _ = ∫⁻ x in FourierAffine.coordBall ((fourierToParabolicMeasurableEquiv m).symm y) s,
          ‖F (fourierToParabolicMeasurableEquiv m x) -
            (a + F z + B (fourierToParabolicMeasurableEquiv m x).1)‖ₑ ^ 2 := by
        rw [hpre]
    _ = _ := by
        refine setLIntegral_congr_fun (FourierAffine.measurableSet_coordBall _ _) ?_
        intro x hx
        have hx' : x ∈ (fourierToParabolicMeasurableEquiv m) ⁻¹' Metric.ball y s := by
          rw [hpre]
          exact hx
        have h2 : fourierToParabolic m x ∈ Metric.ball z 2 := hsub hx'
        show ‖F (fourierToParabolic m x) - (a + F z + B (WithLp.ofLp x).1)‖ₑ ^ 2 =
          ‖H x - (a + B (WithLp.ofLp x).1)‖ₑ ^ 2
        rw [hH x h2]
        congr 2
        ring

/-- For `y ∈ P(z,1)` and `0 < s < 1`: `κ_F(y,s)² ≤ a_H(Ψ⁻¹ y, s)²`. -/
theorem b1vcar_affineErrorSq_le_affineEnergy {m : ℕ} (F : Space m → ℝ)
    (H : FourierSpace m → ℝ) (z : Space m)
    (hH : ∀ x : FourierSpace m, fourierToParabolic m x ∈ Metric.ball z 2 →
      H x = F (fourierToParabolic m x) - F z)
    {y : Space m} (hy : y ∈ Metric.ball z 1) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    affineErrorSq (parabolicVolume m) F y s ≤
      FourierAffine.affineEnergy H ((fourierToParabolicMeasurableEquiv m).symm y) s := by
  have hsub : Metric.ball y s ⊆ Metric.ball z 2 := fun q hq => by
    have h1 := Metric.mem_ball.1 hq
    have h2 := Metric.mem_ball.1 hy
    exact Metric.mem_ball.2 (by linarith [dist_triangle q y z])
  have hk : baseDimension (Spatial m) + 2 = m + 4 := by
    have := b1vcar_baseDimension m
    omega
  rw [affineErrorSq_of_pos _ _ _ hs, FourierAffine.affineEnergy, FourierAffine.affineError, hk]
  refine mul_le_mul_right (le_iInf₂ fun a B => iInf₂_le_of_le (a + F z) B ?_) _
  rw [b1vcar_fit_eq F H z y hs hsub hH a B]

/-- **Proof of the statement `ba1_vertical_unit_carleson`**, with exactly its type
(implication form over the two input statements). Constant `C₂ C₁`. -/
theorem ba1_vertical_unit_carleson_proof
    (hloc : Characterization.CriticalSobolevLocalizationStatement)
    (hfour : Characterization.FourierAffineSquareStatement) :
    ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasStandardParabolicBMOBound m f B →
        RepresentsStandardHalfTimeDerivative m F f →
        ∀ z : Space m, affineCarlesonIntegral (parabolicVolume m) F z 1 ≤
          ENNReal.ofReal (C * ((L : ℝ) ^ 2 + B ^ 2)) := by
  intro m
  obtain ⟨C₁, hC₁, hloc'⟩ := hloc m
  obtain ⟨C₂, hC₂, hfour'⟩ := hfour m
  refine ⟨C₂ * C₁, mul_pos hC₂ hC₁, fun F f L B hF hf hFf z => ?_⟩
  obtain ⟨H, hH, hHeq, hHbd⟩ := hloc' F f L B hF hf hFf z
  have hmp := fourierToParabolic_symm_measurePreserving m
  have hemb := (fourierToParabolicMeasurableEquiv m).symm.measurableEmbedding
  calc affineCarlesonIntegral (parabolicVolume m) F z 1
      = ∫⁻ y in Metric.ball z 1, ∫⁻ s in Ioo 0 1,
          affineErrorSq (parabolicVolume m) F y s ∂scaleMeasure ∂parabolicVolume m := rfl
    _ ≤ ∫⁻ y in Metric.ball z 1, ∫⁻ s in Ioo 0 1,
          FourierAffine.affineEnergy H ((fourierToParabolicMeasurableEquiv m).symm y) s
            ∂scaleMeasure ∂parabolicVolume m :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet fun y hy =>
          setLIntegral_mono' measurableSet_Ioo fun s hs =>
            b1vcar_affineErrorSq_le_affineEnergy F H z hHeq hy hs.1 hs.2
    _ ≤ ∫⁻ y, ∫⁻ s,
          FourierAffine.affineEnergy H ((fourierToParabolicMeasurableEquiv m).symm y) s
            ∂scaleMeasure ∂parabolicVolume m :=
        (setLIntegral_le_lintegral _ _).trans
          (lintegral_mono fun y => setLIntegral_le_lintegral _ _)
    _ = ∫⁻ x, ∫⁻ s, FourierAffine.affineEnergy H x s ∂scaleMeasure :=
        hmp.lintegral_comp_emb hemb (fun x => ∫⁻ s, FourierAffine.affineEnergy H x s ∂scaleMeasure)
    _ = FourierAffine.affineCarlesonEnergy H := rfl
    _ ≤ ENNReal.ofReal C₂ * Characterization.parabolicFourierEnergy hH := hfour' H hH
    _ ≤ ENNReal.ofReal C₂ * ENNReal.ofReal (C₁ * ((L : ℝ) ^ 2 + B ^ 2)) :=
        mul_le_mul_right (le_add_self.trans hHbd) _
    _ = ENNReal.ofReal (C₂ * C₁ * ((L : ℝ) ^ 2 + B ^ 2)) := by
        rw [← ENNReal.ofReal_mul hC₂.le, mul_assoc]

/-! ### All scales: exact similarity scaling of a scalar Carleson integral -/

/-- `T⁻¹ = δ_R` for `T = similarity 0 R`. -/
theorem b1vcar_similarity_symm {m : ℕ} {R : ℝ} (hR : 0 < R) (q : Space m) :
    (similarity (point (0 : Spatial m) 0) R hR).symm q = dilate R q := by
  rw [similarity_symm_apply]
  show point (R • q.1 + 0) (R ^ 2 * q.2.val + 0) = point (R • q.1) (R ^ 2 * q.2.val)
  rw [add_zero, add_zero]

/-- `κ_G(y,s)² = κ_{G_R}(T y, R⁻¹ s)²`, `G_R = R⁻¹ G ∘ δ_R`:
`traceErrorSq_similarity_proof` with `K = univ`, `v = 0`, `x₀ = 0`. -/
theorem b1vcar_affineErrorSq_scale {m : ℕ} (G : Space m → ℝ) {R : ℝ} (hR : 0 < R)
    (y : Space m) (s : ℝ) :
    affineErrorSq (parabolicVolume m) G y s =
      affineErrorSq (parabolicVolume m) (fun p => R⁻¹ * G (dilate R p))
        (similarity (point (0 : Spatial m) 0) R hR y) (R⁻¹ * s) := by
  have h := traceErrorSq_similarity_proof (point (0 : Spatial m) 0) R hR univ G 0 y s
  simp only [traceErrorSq,
    Set.image_univ_of_surjective (similarity (point (0 : Spatial m) 0) R hR).surjective,
    Measure.restrict_univ, sub_zero, smul_eq_mul, b1vcar_similarity_symm hR] at h
  rw [← h, div_eq_inv_mul s R]

/-- `Carl_G(z,R) = R^{m+2} Carl_{G_R}(T z, 1)`. -/
theorem b1vcar_carleson_scale {m : ℕ} (G : Space m → ℝ) {R : ℝ} (hR : 0 < R) (z : Space m) :
    affineCarlesonIntegral (parabolicVolume m) G z R =
      ENNReal.ofReal R ^ (m + 2) *
        affineCarlesonIntegral (parabolicVolume m) (fun p => R⁻¹ * G (dilate R p))
          (similarity (point (0 : Spatial m) 0) R hR z) 1 := by
  have hpre : (fun s => R⁻¹ * s) ⁻¹' Ioo (0 : ℝ) 1 = Ioo 0 R := by
    ext s
    simp only [mem_preimage, mem_Ioo]
    rw [← div_eq_inv_mul s R, div_pos_iff_of_pos_right hR, div_lt_one hR]
  calc affineCarlesonIntegral (parabolicVolume m) G z R
      = ∫⁻ y in Metric.ball z R, (fun w => ∫⁻ u in Ioo 0 1,
          affineErrorSq (parabolicVolume m) (fun p => R⁻¹ * G (dilate R p)) w u ∂scaleMeasure)
            (similarity (point (0 : Spatial m) 0) R hR y) ∂parabolicVolume m := by
        unfold affineCarlesonIntegral
        refine lintegral_congr fun y => ?_
        simp only [b1vcar_affineErrorSq_scale G hR]
        rw [← hpre, b1vcar_setLIntegral_scaleMeasure_comp_mul_left (inv_pos.2 hR)
          (fun u => affineErrorSq (parabolicVolume m) (fun p => R⁻¹ * G (dilate R p))
            (similarity (point (0 : Spatial m) 0) R hR y) u)]
    _ = ENNReal.ofReal R ^ (m + 2) *
          ∫⁻ w in similarity (point (0 : Spatial m) 0) R hR '' Metric.ball z R,
            ∫⁻ u in Ioo 0 1, affineErrorSq (parabolicVolume m)
              (fun p => R⁻¹ * G (dilate R p)) w u ∂scaleMeasure ∂parabolicVolume m :=
        setLIntegral_comp_similarity (point (0 : Spatial m) 0) R hR (Metric.ball z R)
          (fun w => ∫⁻ u in Ioo 0 1, affineErrorSq (parabolicVolume m)
            (fun p => R⁻¹ * G (dilate R p)) w u ∂scaleMeasure)
    _ = _ := by
        rw [image_similarity_ball, div_self hR.ne']
        rfl

/-! ### Vector values: the coordinate split -/

/-- The slope `u ↦ (b_α u)_α` assembled from scalar slopes. -/
def b1vcar_pack {m d : ℕ} (b : Fin d → (Spatial m →L[ℝ] ℝ)) : Spatial m →L[ℝ] Spatial d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi b)

theorem b1vcar_pack_apply {m d : ℕ} (b : Fin d → (Spatial m →L[ℝ] ℝ)) (u : Spatial m)
    (α : Fin d) : b1vcar_pack b u α = b α u := rfl

/-- `‖v‖ₑ² = Σ_α ‖v_α‖ₑ²` on `ℝ^d`. -/
theorem b1vcar_enorm_sq_eq_sum {d : ℕ} (v : Spatial d) : ‖v‖ₑ ^ 2 = ∑ α, ‖v α‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun α _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- `κ_F(y,s)² ≤ Σ_α κ_{F^α}(y,s)²` for a continuous `F : Space m → ℝ^d` and any measure. -/
theorem b1vcar_affineErrorSq_le_sum {m d : ℕ} (ν : Measure (Space m)) (F : Space m → Spatial d)
    (hF : Continuous F) (y : Space m) (s : ℝ) :
    affineErrorSq ν F y s ≤ ∑ α : Fin d, affineErrorSq ν (fun q => F q α) y s := by
  classical
  rcases le_or_gt s 0 with hs | hs
  · rw [affineErrorSq_of_nonpos _ _ _ hs]
    exact zero_le
  simp only [affineErrorSq_of_pos _ _ _ hs]
  rw [← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  obtain ⟨g, hg⟩ : ∃ g : Fin d → ℝ × (Spatial m →L[ℝ] ℝ) → ℝ≥0∞,
      g = fun α p => affineFitIntegral ν (fun q => F q α) p.1 p.2 y s := ⟨_, rfl⟩
  have hFα : ∀ α : Fin d, Continuous fun q => F q α := fun α =>
    (EuclideanSpace.proj (𝕜 := ℝ) α).continuous.comp hF
  have key : ∀ P : Fin d → ℝ × (Spatial m →L[ℝ] ℝ),
      ⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d), affineFitIntegral ν F a B y s ≤
        ∑ α, g α (P α) := by
    intro P
    refine iInf₂_le_of_le (WithLp.toLp 2 fun α => (P α).1) (b1vcar_pack fun α => (P α).2)
      (le_of_eq ?_)
    have hpt : ∀ q : Space m,
        ‖F q - (WithLp.toLp 2 (fun α => (P α).1) + b1vcar_pack (fun α => (P α).2) q.1)‖ₑ ^ 2 =
          ∑ α, ‖F q α - ((P α).1 + (P α).2 q.1)‖ₑ ^ 2 := by
      intro q
      rw [b1vcar_enorm_sq_eq_sum]
      rfl
    have hmeas : ∀ α ∈ (Finset.univ : Finset (Fin d)),
        Measurable fun q : Space m => ‖F q α - ((P α).1 + (P α).2 q.1)‖ₑ ^ 2 := fun α _ =>
      ((hFα α).sub (continuous_const.add
        ((P α).2.continuous.comp continuous_fst))).measurable.enorm.pow_const 2
    simp only [hg, affineFitIntegral]
    rw [lintegral_congr hpt, lintegral_finsetSum _ hmeas]
  have hsum : ⨅ P : Fin d → ℝ × (Spatial m →L[ℝ] ℝ), ∑ α, g α (P α) =
      ∑ α, ⨅ P : Fin d → ℝ × (Spatial m →L[ℝ] ℝ), g α (P α) := by
    refine ENNReal.iInf_sum (ι := Fin d → ℝ × (Spatial m →L[ℝ] ℝ)) (s := Finset.univ)
      (f := fun P α => g α (P α)) fun t i j => ?_
    refine ⟨fun α => if g α (i α) ≤ g α (j α) then i α else j α, fun α _ => ?_⟩
    dsimp only
    split_ifs with h
    · exact ⟨le_rfl, h⟩
    · exact ⟨(not_le.1 h).le, le_rfl⟩
  calc ⨅ (a : Spatial d) (B : Spatial m →L[ℝ] Spatial d), affineFitIntegral ν F a B y s
      ≤ ⨅ P : Fin d → ℝ × (Spatial m →L[ℝ] ℝ), ∑ α, g α (P α) := le_iInf key
    _ = ∑ α, ⨅ P : Fin d → ℝ × (Spatial m →L[ℝ] ℝ), g α (P α) := hsum
    _ ≤ ∑ α, ⨅ (a : ℝ) (B : Spatial m →L[ℝ] ℝ),
          affineFitIntegral ν (fun q => F q α) a B y s := by
        refine Finset.sum_le_sum fun α _ => le_iInf₂ fun a B => ?_
        exact iInf_le_of_le (fun _ => (a, B)) (le_of_eq (by rw [hg]))

/-- Restricting the measure to a set containing the ball does not change the error. -/
theorem b1vcar_affineErrorSq_restrict {m : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (μ : Measure (Space m)) (f : Space m → Y) (K : Set (Space m))
    (y : Space m) (s : ℝ) (hsub : Metric.ball y s ⊆ K) :
    affineErrorSq (μ.restrict K) f y s = affineErrorSq μ f y s := by
  simp only [affineErrorSq, affineFitIntegral, Measure.restrict_restrict measurableSet_ball,
    Set.inter_eq_left.2 hsub]

/-- **Proof of the statement `ba1_vertical_carleson`**, with exactly its type
(implication form over the unit-scale and dilation conclusions). Constant `max(1,d) C_m`. -/
theorem ba1_vertical_carleson_proof
    (hunit : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasStandardParabolicBMOBound m f B →
        RepresentsStandardHalfTimeDerivative m F f →
        ∀ z : Space m, affineCarlesonIntegral (parabolicVolume m) F z 1 ≤
          ENNReal.ofReal (C * ((L : ℝ) ^ 2 + B ^ 2)))
    (hdil : ∀ (m : ℕ) (F f : Space m → ℝ) (L : ℝ≥0) (B ρ : ℝ), 0 < ρ →
      (LipschitzWith L F → LipschitzWith L (fun p => ρ⁻¹ * F (dilate ρ p))) ∧
      (HasStandardParabolicBMOBound m f B →
        HasStandardParabolicBMOBound m (fun p => f (dilate ρ p)) B) ∧
      (RepresentsStandardHalfTimeDerivative m F f →
        RepresentsStandardHalfTimeDerivative m (fun p => ρ⁻¹ * F (dilate ρ p))
          (fun p => f (dilate ρ p)))) :
    ∀ m d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F : Space m → Spatial d) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasCoordinateHalfTimeBMOBound m d F B →
        HasAffineCarlesonBound (parabolicVolume m) F (C * ((L : ℝ) ^ 2 + B ^ 2)) := by
  intro m d
  obtain ⟨C₀, hC₀, hu⟩ := hunit m
  have hmax : (0 : ℝ) < max 1 (d : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨max 1 (d : ℝ) * C₀, mul_pos hmax hC₀, fun F L B hF hB => ?_⟩
  have hLB : 0 ≤ (L : ℝ) ^ 2 + B ^ 2 := by positivity
  refine ⟨mul_nonneg (mul_pos hmax hC₀).le hLB, fun z R hR => ?_⟩
  -- coordinates are `L`-Lipschitz
  have hGL : ∀ α : Fin d, LipschitzWith L (fun q => F q α) := fun α =>
    LipschitzWith.of_dist_le_mul fun p q =>
      (PiLp.dist_apply_le (F p) (F q) α).trans (hF.dist_le_mul p q)
  -- scalar bound at every coordinate
  have hscalar : ∀ α : Fin d, affineCarlesonIntegral (parabolicVolume m) (fun q => F q α) z R ≤
      ENNReal.ofReal (C₀ * ((L : ℝ) ^ 2 + B ^ 2) * R ^ (m + 2)) := by
    intro α
    obtain ⟨-, fα, hfα, hrep⟩ := hB α
    obtain ⟨hdL, hdB, hdR⟩ := hdil m (fun q => F q α) fα L B R hR
    have hu' := hu _ _ L B (hdL (hGL α)) (hdB hfα) (hdR hrep)
      (similarity (point (0 : Spatial m) 0) R hR z)
    rw [b1vcar_carleson_scale (fun q => F q α) hR z]
    calc _ ≤ ENNReal.ofReal R ^ (m + 2) * ENNReal.ofReal (C₀ * ((L : ℝ) ^ 2 + B ^ 2)) :=
          mul_le_mul_right hu' _
      _ = _ := by
          rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (pow_nonneg hR.le _)]
          congr 1
          ring
  -- the compact set carrying every ball of the Carleson region
  set K : Set (Space m) := Metric.closedBall z (2 * R) with hK
  have hKc : IsCompact K := isCompact_closedBall z (2 * R)
  have hmeas : ∀ α : Fin d,
      Measurable (fun p : Space m × ℝ => traceErrorSq (parabolicVolume m) K (fun q => F q α)
        p.1 p.2) ∧
      ∀ R' : ℝ, Measurable (fun p : Space m =>
        ∫⁻ r in Ioo 0 R', traceErrorSq (parabolicVolume m) K (fun q => F q α) p r
          ∂scaleMeasure) := fun α =>
    measurable_traceErrorSq_of_isCompact_proof K hKc (fun q => F q α) L
      (hGL α).lipschitzOnWith
  have hsplit : ∀ y ∈ Metric.ball z R, ∀ s ∈ Ioo (0 : ℝ) R,
      affineErrorSq (parabolicVolume m) F y s ≤
        ∑ α : Fin d, traceErrorSq (parabolicVolume m) K (fun q => F q α) y s := by
    intro y hy s hs
    have hsub : Metric.ball y s ⊆ K := fun q hq => by
      have h1 := Metric.mem_ball.1 hq
      have h2 := Metric.mem_ball.1 hy
      exact Metric.mem_closedBall.2 (by linarith [dist_triangle q y z, hs.2])
    rw [← b1vcar_affineErrorSq_restrict (parabolicVolume m) F K y s hsub]
    exact b1vcar_affineErrorSq_le_sum _ F hF.continuous y s
  calc affineCarlesonIntegral (parabolicVolume m) F z R
      = ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R,
          affineErrorSq (parabolicVolume m) F y s ∂scaleMeasure ∂parabolicVolume m := rfl
    _ ≤ ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R,
          ∑ α : Fin d, traceErrorSq (parabolicVolume m) K (fun q => F q α) y s
            ∂scaleMeasure ∂parabolicVolume m :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet fun y hy =>
          setLIntegral_mono' measurableSet_Ioo fun s hs => hsplit y hy s hs
    _ = ∫⁻ y in Metric.ball z R, ∑ α : Fin d, ∫⁻ s in Ioo 0 R,
          traceErrorSq (parabolicVolume m) K (fun q => F q α) y s
            ∂scaleMeasure ∂parabolicVolume m :=
        lintegral_congr fun y => lintegral_finsetSum _ fun α _ =>
          (hmeas α).1.comp (measurable_const.prodMk measurable_id)
    _ = ∑ α : Fin d, ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R,
          traceErrorSq (parabolicVolume m) K (fun q => F q α) y s
            ∂scaleMeasure ∂parabolicVolume m :=
        lintegral_finsetSum _ fun α _ => (hmeas α).2 R
    _ ≤ ∑ α : Fin d, affineCarlesonIntegral (parabolicVolume m) (fun q => F q α) z R :=
        Finset.sum_le_sum fun α _ => lintegral_mono fun y => lintegral_mono fun s =>
          traceErrorSq_le_affineErrorSq _ _ _ _ _
    _ ≤ ∑ _α : Fin d, ENNReal.ofReal (C₀ * ((L : ℝ) ^ 2 + B ^ 2) * R ^ (m + 2)) :=
        Finset.sum_le_sum fun α _ => hscalar α
    _ = ENNReal.ofReal ((d : ℝ) * (C₀ * ((L : ℝ) ^ 2 + B ^ 2) * R ^ (m + 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (max 1 (d : ℝ) * C₀ * ((L : ℝ) ^ 2 + B ^ 2) *
          R ^ baseDimension (Spatial m)) := by
        rw [b1vcar_baseDimension]
        refine ENNReal.ofReal_le_ofReal ?_
        have hX : 0 ≤ C₀ * ((L : ℝ) ^ 2 + B ^ 2) * R ^ (m + 2) :=
          mul_nonneg (mul_nonneg hC₀.le hLB) (pow_nonneg hR.le _)
        calc (d : ℝ) * (C₀ * ((L : ℝ) ^ 2 + B ^ 2) * R ^ (m + 2))
            ≤ max 1 (d : ℝ) * (C₀ * ((L : ℝ) ^ 2 + B ^ 2) * R ^ (m + 2)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hX
          _ = _ := by ring

end ParabolicRectifiability.QuantitativeCharacterization
