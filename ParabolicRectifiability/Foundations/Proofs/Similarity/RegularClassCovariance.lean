import ParabolicRectifiability.Foundations.Proofs.Similarity.Covariance
import ParabolicRectifiability.Foundations.Proofs.Similarity.Transport
import ParabolicRectifiability.Decomposition.Carrier.Transport

/-! # Similarity covariance of the regular class

Assembly of the covariance and transport statements for a base similarity into the covariance
of the general regular class.

* `fsim_lipschitzWith_normalFourierComponent`: the vector-to-component adapter. Every
  orthonormal normal component of a `LipschitzWith L` map on a vertical base satisfies the
  Lipschitz hypothesis of `HalfTimeBracketIntegrableStatement` with the same `L`.
* `fsim_normalFourierComponent_smul_baseSimilarity`,
  `fsim_normalFourierComponent_baseSimilarity`: components of `R • F ∘ σ` and `g ∘ σ`,
  `σ = baseSimilarity W (0, t₀) R`, in ordinary coordinates.
* `fsim_representsGeneralHalfTimeDerivative_baseSimilarity` (vector form): the dilation
  stage, then the time-translation stage (with `HalfTimeBracketIntegrableStatement` as
  hypothesis), per component.
* `fsim_isGeneralRegularVerticalFunction_baseSimilarity`: the regular-class covariance
  (the representation covariance, `fsim_lipschitzWith_baseSimilarity` and the BMO invariance
  `hasParabolicBMOBound_baseSimilarity_proof`); this is the hypothesis `hreg` of
  `fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity`.
* `fsim_support_restrict_preimage_similarity`: the support of a pulled-back restriction for
  `ν = rescaledSource μ k a R hR`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Foundations

/-! ## Components on a vertical base -/

/-- **Vector-to-component adapter.** The `i`-th orthonormal normal component of a
`LipschitzWith L` map `F` on `W × ℝ`, read in ordinary coordinates, is `L`-Lipschitz for the
parabolic metric of `Space (finrank W)` (the convention of
`HalfTimeBracketIntegrableStatement`): ordinary coordinates followed by
`fourierToParabolic` is the inverse of the isometry `subspaceParabolicIsometry W`, and an
orthonormal coordinate is `1`-Lipschitz. -/
theorem fsim_lipschitzWith_normalFourierComponent {n : ℕ} (W : Submodule ℝ (Spatial n))
    (F : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (hF : LipschitzWith L F)
    (i : Fin (Module.finrank ℝ W.orthogonal)) :
    LipschitzWith L
      (normalFourierComponent W F i ∘ (fourierToParabolic (Module.finrank ℝ W)).symm) := by
  have hfun : normalFourierComponent W F i ∘ (fourierToParabolic (Module.finrank ℝ W)).symm =
      (fun v : W.orthogonal => normalCoordinates W v i) ∘ F ∘
        (subspaceParabolicIsometry W).symm := by
    funext z
    rfl
  have h1 : LipschitzWith 1 (fun v : W.orthogonal => normalCoordinates W v i) := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    have h := subspaceCoordinate_abs_le_norm W.orthogonal (v - w) i
    rw [map_sub, PiLp.sub_apply] at h
    exact h
  rw [hfun]
  simpa using h1.comp (hF.comp (subspaceParabolicIsometry W).symm.isometry.lipschitzWith)

/-- Components of `R • H ∘ σ`, `σ = baseSimilarity W (0, t₀) R`, in ordinary coordinates:
`x ↦ R · H_i(R⁻¹ x_u, R⁻² (x_t - t₀))`. -/
theorem fsim_normalFourierComponent_smul_baseSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (R t₀ : ℝ) (H : SubspaceSpace W → W.orthogonal) (i : Fin (Module.finrank ℝ W.orthogonal)) :
    normalFourierComponent W
        (fun p => R • H (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking t₀) R p)) i =
      fun x => R * normalFourierComponent W H i
        (WithLp.toLp 2 (R⁻¹ • (WithLp.ofLp x).1, R⁻¹ ^ 2 * ((WithLp.ofLp x).2 - t₀))) := by
  funext x
  simp only [normalFourierComponent, subspaceFourierToParabolic_apply, baseSimilarity,
    sub_zero, map_smul, PiLp.smul_apply, smul_eq_mul]
  rfl

/-- Components of `g ∘ σ`, `σ = baseSimilarity W (0, t₀) R`, in ordinary coordinates. -/
theorem fsim_normalFourierComponent_baseSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (R t₀ : ℝ) (H : SubspaceSpace W → W.orthogonal) (i : Fin (Module.finrank ℝ W.orthogonal)) :
    normalFourierComponent W
        (fun p => H (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking t₀) R p)) i =
      fun x => normalFourierComponent W H i
        (WithLp.toLp 2 (R⁻¹ • (WithLp.ofLp x).1, R⁻¹ ^ 2 * ((WithLp.ofLp x).2 - t₀))) := by
  funext x
  simp only [normalFourierComponent, subspaceFourierToParabolic_apply, baseSimilarity,
    sub_zero, map_smul]
  rfl

/-! ## Representation covariance, vector form, and the regular class -/

/-- **Representation covariance, vector form.** Under `HalfTimeBracketIntegrableStatement`, if
`F` is parabolic Lipschitz on `W × ℝ` and `g` represents its homogeneous half-time derivative,
then `g ∘ σ` represents that of `R • F ∘ σ`, `σ = baseSimilarity W (0, t₀) R`,
`σ(u,t) = (R⁻¹ u, R⁻² (t - t₀))`. Per component, the dilation stage, then the
time-translation stage applied to the dilated component, whose Lipschitz bound comes from
`fsim_lipschitzWith_baseSimilarity` and the adapter. -/
theorem fsim_representsGeneralHalfTimeDerivative_baseSimilarity
    (hhp : HalfTimeBracketIntegrableStatement) {n : ℕ} (W : Submodule ℝ (Spatial n)) (R : ℝ)
    (hR : 0 < R) (t₀ : ℝ) (F g : SubspaceSpace W → W.orthogonal)
    (hF : ∃ L : ℝ≥0, LipschitzWith L F) (h : RepresentsGeneralHalfTimeDerivative W F g) :
    RepresentsGeneralHalfTimeDerivative W
      (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking t₀) R p))
      (fun p => g (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking t₀) R p)) := by
  obtain ⟨L, hL⟩ := hF
  intro i
  have hD := fsim_representsHomogeneousHalfTimeDerivative_dilation R hR _ _ (h i)
  have hLip : ∃ L' : ℝ≥0, LipschitzWith L'
      ((fun y : FourierSpace (Module.finrank ℝ W) => R * normalFourierComponent W F i
        (WithLp.toLp 2 (R⁻¹ • (WithLp.ofLp y).1, R⁻¹ ^ 2 * (WithLp.ofLp y).2))) ∘
        (fourierToParabolic (Module.finrank ℝ W)).symm) := by
    refine ⟨L, ?_⟩
    have h1 := fsim_lipschitzWith_normalFourierComponent W _ L
      (fsim_lipschitzWith_baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking 0) R hR
        F L hL) i
    rw [fsim_normalFourierComponent_smul_baseSimilarity] at h1
    simpa only [sub_zero] using h1
  have hT := fsim_representsHomogeneousHalfTimeDerivative_timeShift hhp t₀ _ _ hLip hD
  rw [fsim_normalFourierComponent_smul_baseSimilarity, fsim_normalFourierComponent_baseSimilarity]
  exact hT

/-- **Regular-class covariance.** Under `HalfTimeBracketIntegrableStatement`, if `F` is general
regular with bound `ε` on `W × ℝ`, so is `R • F ∘ σ`, `σ = baseSimilarity W (0, t₀) R`, with
representative `g ∘ σ` and the same Lipschitz and BMO constants. Assembled from the
representation covariance (vector form), `fsim_lipschitzWith_baseSimilarity` and
`hasParabolicBMOBound_baseSimilarity_proof`. With `t₀ = a_t`, this is the hypothesis `hreg` of
`fsim_hasGeneralRegularVerticalGraphCover_preimage_similarity`. -/
theorem fsim_isGeneralRegularVerticalFunction_baseSimilarity
    (hhp : HalfTimeBracketIntegrableStatement) {n : ℕ} (W : Submodule ℝ (Spatial n)) (R : ℝ)
    (hR : 0 < R) (t₀ : ℝ) (F : SubspaceSpace W → W.orthogonal) (ε : ℝ)
    (hF : IsGeneralRegularVerticalFunction W F ε) :
    IsGeneralRegularVerticalFunction W
      (fun p => R • F (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking t₀) R p)) ε := by
  obtain ⟨g, L, B, hL, hB, hrep, hLB⟩ := hF
  exact ⟨fun p => g (baseSimilarity W ((0 : W), Metric.Snowflaking.toSnowflaking t₀) R p), L, B,
    fsim_lipschitzWith_baseSimilarity W _ R hR F L hL,
    hasParabolicBMOBound_baseSimilarity_proof W _ R hR hB,
    fsim_representsGeneralHalfTimeDerivative_baseSimilarity hhp W R hR t₀ F g ⟨L, hL⟩ hrep, hLB⟩

/-! ## Supports for the rescaled source -/

/-- **Supports for the rescaled source**:
the actual support of `μ⌊S⁻¹'(A)` is `S⁻¹'` of the actual support of `ν⌊A`,
`ν = rescaledSource μ k a R hR = R^{-k} S_# μ`, for every measure `μ` and every set `A`.
Follows from the general statement `fsim_support_restrict_preimage_homeomorph`. -/
theorem fsim_support_restrict_preimage_similarity {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (a : Space n) (R : ℝ) (hR : 0 < R) (A : Set (Space n)) :
    (μ.restrict (similarity a R hR ⁻¹' A)).support =
      similarity a R hR ⁻¹' ((rescaledSource μ k a R hR).restrict A).support :=
  fsim_support_restrict_preimage_homeomorph μ (similarity a R hR) ((ENNReal.ofReal R)⁻¹ ^ k)
    (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top))
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hR).ne')) A

end ParabolicRectifiability.Foundations
