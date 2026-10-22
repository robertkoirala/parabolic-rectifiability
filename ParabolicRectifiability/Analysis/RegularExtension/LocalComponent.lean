import ParabolicRectifiability.Analysis.RegularExtension.LocalSimilarity
import ParabolicRectifiability.Analysis.TraceExtension.TracePieces.Transport
import ParabolicRectifiability.Analysis.TraceExtension.Similarity
import ParabolicRectifiability.Analysis.HalfTimeDerivative.TailOscillation

/-! # One normal component of the local half-time decomposition

This file treats one normal coordinate of the local half-time decomposition; the vector
assembly and the final constant are in `LocalDecomposition`. The coordinate estimate
`affineErrorSq_component_le` enters as a hypothesis (at universe `0`).

Fix an intrinsic ball `P(p,r)`, `m = rank W`, `d = rank W^⊥`, and the Fourier coordinates
`Φ = subspaceFourierToParabolic W`. Let `x₀ = Φ⁻¹ p` and `Θ x = x - x₀` (the
`fourierSimilarity` at scale one). For each orthonormal normal coordinate `i`:

* the centred component `G_i = F_i ∘ Θ⁻¹` of `F_i = (normal coordinate i) ∘ F ∘ Φ` is
  compactly supported and parabolic `L`-Lipschitz; its affine Carleson constant is `B`,
  by the transport to ordinary coordinates, the translation invariance of the affine Carleson
  bound (at `ρ = 1`) and `affineErrorSq_component_le` for the coordinate functional of norm
  `≤ 1`;
* the scalar hypothesis at `R = r` gives `G_i = a_i + b_i` on the cylinder at the origin;
* the local covariance `rx5_repHalf_comp_fourierSimilarity_local` moves the representation
  to `Θ⁻¹ (cylinder) = Φ⁻¹ P(p,r)`;
* `b_i` is integrable on the cylinder: `a_i + b_i` is locally integrable there and
  `a_i ∈ L²`, so `b_i` is measurable on it, and the oscillation bound makes it bounded.

The vectors `a, b` are assembled from the components with `(normalCoordinates W)⁻¹`.
Parseval gives `∫ ‖a‖² = Σ_i ∫ a_i² ≤ d C (B + L²) r^(m+2)` and
`‖b x - b y‖ ≤ √d C L`. With `|P(p,r)| = 2ω_m r^(m+2)` and `B + L² ≤ (L + √B)²`, the constant
`C' = √d C + √(d C / (2ω_m))` depends only on `m, d, C`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ}

/-! ## Orthonormal normal coordinates -/

theorem rx5_abs_normalCoordinates_le (W : Submodule ℝ (Spatial n)) (v : W.orthogonal)
    (i : Fin (Module.finrank ℝ W.orthogonal)) : |normalCoordinates W v i| ≤ ‖v‖ := by
  have h := PiLp.norm_apply_le (normalCoordinates W v) i
  rwa [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] at h

/-- The `i`-th orthonormal normal coordinate as a continuous linear functional. -/
def rx5_normalCoordinateCLM (W : Submodule ℝ (Spatial n))
    (i : Fin (Module.finrank ℝ W.orthogonal)) : W.orthogonal →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => normalCoordinates W v i
      map_add' := fun u v => by simp only [map_add, PiLp.add_apply]
      map_smul' := fun c v => by
        simp only [map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply] }
    1 (fun v => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs, one_mul] using
        rx5_abs_normalCoordinates_le W v i)

theorem rx5_normalCoordinateCLM_apply (W : Submodule ℝ (Spatial n))
    (i : Fin (Module.finrank ℝ W.orthogonal)) (v : W.orthogonal) :
    rx5_normalCoordinateCLM W i v = normalCoordinates W v i := rfl

theorem rx5_norm_normalCoordinateCLM_le (W : Submodule ℝ (Spatial n))
    (i : Fin (Module.finrank ℝ W.orthogonal)) : ‖rx5_normalCoordinateCLM W i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Parseval in the orthonormal normal coordinates. -/
theorem rx5_norm_sq_eq_sum (W : Submodule ℝ (Spatial n)) (v : W.orthogonal) :
    ‖v‖ ^ 2 = ∑ i, normalCoordinates W v i ^ 2 := by
  rw [← LinearIsometryEquiv.norm_map (normalCoordinates W) v, EuclideanSpace.real_norm_sq_eq]

theorem rx5_normalCoordinates_assemble (W : Submodule ℝ (Spatial n))
    (c : Fin (Module.finrank ℝ W.orthogonal) → ℝ) (i : Fin (Module.finrank ℝ W.orthogonal)) :
    normalCoordinates W ((normalCoordinates W).symm (WithLp.toLp 2 c)) i = c i := by
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem rx5_enorm_sq_assemble (W : Submodule ℝ (Spatial n))
    (c : Fin (Module.finrank ℝ W.orthogonal) → ℝ) :
    ‖(normalCoordinates W).symm (WithLp.toLp 2 c)‖ₑ ^ 2 = ∑ i, ‖c i‖ₑ ^ 2 := by
  have h : ‖(normalCoordinates W).symm (WithLp.toLp 2 c)‖ ^ 2 = ∑ i, c i ^ 2 := by
    rw [rx5_norm_sq_eq_sum]
    simp only [rx5_normalCoordinates_assemble]
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

theorem rx5_memLp_assemble {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (W : Submodule ℝ (Spatial n)) (c : Fin (Module.finrank ℝ W.orthogonal) → α → ℝ)
    (hc : ∀ i, MemLp (c i) p μ) :
    MemLp (fun x => (normalCoordinates W).symm (WithLp.toLp 2 (fun i => c i x))) p μ := by
  have hv : MemLp (fun x => (WithLp.toLp 2 (fun i => c i x) :
      Spatial (Module.finrank ℝ W.orthogonal))) p μ := memLp_piLp_iff.2 hc
  exact (normalCoordinates W).symm.lipschitzWith.comp_memLp (map_zero _) hv

/-! ## Translation in ordinary Fourier coordinates -/

theorem rx5_point_fst {m : ℕ} (x : Spatial m) (t : ℝ) : (point x t).1 = x := rfl

theorem rx5_point_snd_val {m : ℕ} (x : Spatial m) (t : ℝ) : (point x t).2.val = t := rfl

/-- At scale one the Fourier similarity is a translation and preserves the volume. -/
theorem rx5_measurePreserving_translation {m : ℕ} (q : Space m) :
    MeasurePreserving (fourierSimilarity q 1 one_pos) (volume : Measure (FourierSpace m))
      volume := by
  have h := measurePreserving_fourierSimilarity q 1 one_pos
  rwa [ENNReal.ofReal_one, one_pow, one_smul] at h

theorem rx5_mem_cylinder_origin_iff {m : ℕ} (r : ℝ) (x : FourierSpace m) :
    x ∈ analyticCylinder (point (0 : Spatial m) 0) r ↔
      ‖(WithLp.ofLp x).1‖ < r ∧ |(WithLp.ofLp x).2| < r ^ 2 := by
  simp only [analyticCylinder, mem_preimage, fourierCoordinatesMeasurableEquiv_apply, mem_prod,
    Metric.mem_ball, mem_Ioo, dist_zero_right, rx5_point_fst, rx5_point_snd_val, zero_sub,
    zero_add, abs_lt]

/-- The translate of the origin cylinder is the cylinder at the centre. -/
theorem rx5_preimage_cylinder {m : ℕ} (q : Space m) (r : ℝ) :
    fourierSimilarity q 1 one_pos ⁻¹' analyticCylinder (point (0 : Spatial m) 0) r =
      analyticCylinder q r := by
  ext x
  rw [mem_preimage, rx5_mem_cylinder_origin_iff, fourierSimilarity_apply, WithLp.ofLp_toLp]
  simp only [analyticCylinder, mem_preimage, fourierCoordinatesMeasurableEquiv_apply, mem_prod,
    Metric.mem_ball, mem_Ioo, dist_eq_norm, inv_one, one_smul, one_pow, one_mul, abs_lt]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩

/-! ## Scalar facts on the origin cylinder -/

theorem rx5_osc_of_cylinder {m : ℕ} {r K : ℝ} {b : FourierSpace m → ℝ}
    (hosc : ∀ (u v : Spatial m) (t t₀ : ℝ), ‖u‖ < r → ‖v‖ < r → |t| < r ^ 2 → |t₀| < r ^ 2 →
      |b (WithLp.toLp 2 (u, t)) - b (WithLp.toLp 2 (v, t₀))| ≤ K)
    {x y : FourierSpace m} (hx : x ∈ analyticCylinder (point (0 : Spatial m) 0) r)
    (hy : y ∈ analyticCylinder (point (0 : Spatial m) 0) r) : |b x - b y| ≤ K := by
  rw [rx5_mem_cylinder_origin_iff] at hx hy
  have h := hosc _ _ _ _ hx.1 hy.1 hx.2 hy.2
  simpa only [Prod.mk.eta, WithLp.toLp_ofLp] using h

/-- A function whose sum with an `L²` function is locally integrable on the origin cylinder,
and whose oscillation there is bounded, is integrable on the cylinder. -/
theorem rx5_integrableOn_of_osc {m : ℕ} {r K : ℝ} (hr : 0 < r) {a b : FourierSpace m → ℝ}
    (ha : MemLp a 2 volume)
    (hab : LocallyIntegrableOn (fun x => a x + b x)
      (analyticCylinder (point (0 : Spatial m) 0) r) volume)
    (hosc : ∀ x ∈ analyticCylinder (point (0 : Spatial m) 0) r,
      ∀ y ∈ analyticCylinder (point (0 : Spatial m) 0) r, |b x - b y| ≤ K) :
    IntegrableOn b (analyticCylinder (point (0 : Spatial m) 0) r) volume := by
  set S := analyticCylinder (point (0 : Spatial m) 0) r
  have h0 : (WithLp.toLp 2 ((0 : Spatial m), (0 : ℝ)) : FourierSpace m) ∈ S := by
    rw [rx5_mem_cylinder_origin_iff, WithLp.ofLp_toLp, norm_zero, abs_zero]
    exact ⟨hr, pow_pos hr 2⟩
  have hmeas : AEStronglyMeasurable b (volume.restrict S) := by
    have h1 := hab.aestronglyMeasurable
    have h2 : AEStronglyMeasurable a (volume.restrict S) := ha.aestronglyMeasurable.restrict
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, add_sub_cancel_left]
  refine IntegrableOn.of_bound (HalfTimeDerivative.tailBase_volume hr).2 hmeas
    (|b (WithLp.toLp 2 ((0 : Spatial m), (0 : ℝ)))| + K) ?_
  filter_upwards [ae_restrict_mem (measurableSet_analyticCylinder _ r)] with x hx
  have h := hosc x hx _ h0
  rw [Real.norm_eq_abs]
  calc |b x| = |(b x - b (WithLp.toLp 2 ((0 : Spatial m), (0 : ℝ)))) +
        b (WithLp.toLp 2 ((0 : Spatial m), (0 : ℝ)))| := by rw [sub_add_cancel]
    _ ≤ |b x - b (WithLp.toLp 2 ((0 : Spatial m), (0 : ℝ)))| +
        |b (WithLp.toLp 2 ((0 : Spatial m), (0 : ℝ)))| := abs_add_le _ _
    _ ≤ |b (WithLp.toLp 2 ((0 : Spatial m), (0 : ℝ)))| + K := by linarith

/-! ## Affine Carleson bounds of a coordinate -/

/-- A pointwise comparison of affine errors (`affineErrorSq_component_le` for one functional) passes to the
affine Carleson bound with the same constant. -/
theorem rx5_hasAffineCarlesonBound_comp_clm {E Y Y' : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] {μ : Measure (E × Time)}
    (ℓ : Y →L[ℝ] Y') {f : E × Time → Y} {B : ℝ}
    (hcomp : ∀ y s, affineErrorSq μ (fun q => ℓ (f q)) y s ≤ affineErrorSq μ f y s)
    (h : HasAffineCarlesonBound μ f B) : HasAffineCarlesonBound μ (fun q => ℓ (f q)) B := by
  refine ⟨h.1, fun z R hR => le_trans ?_ (h.2 z R hR)⟩
  unfold affineCarlesonIntegral
  exact lintegral_mono fun y => lintegral_mono fun s => hcomp y s

/-- The Fourier coordinates of the intrinsic base factor through the parabolic isometry. -/
theorem rx5_subspaceFourierToParabolic_eq (W : Submodule ℝ (Spatial n))
    (x : FourierSpace (Module.finrank ℝ W)) :
    subspaceFourierToParabolic W x =
      (subspaceParabolicIsometry W).symm (fourierToParabolic (Module.finrank ℝ W) x) := by
  rw [fourierToParabolic_apply, ← fourierToParabolicMeasurableEquiv_apply,
    ← subspaceParabolic_fourierToParabolic, IsometryEquiv.symm_apply_apply]

/-! ## One normal component -/

/-- **One normal component of the local decomposition.** In Fourier coordinates, the
`i`-th normal component of `F` is represented on `Φ⁻¹ P(p,r)` by `α + β`, with `α ∈ L²`
controlled by the scalar constant, and `β` integrable there with oscillation `≤ C L`. -/
theorem rx5_component_decomposition
    (hA12c : ∀ {E Y Y' : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] (μ : Measure (E × Time))
      (ℓ : Y →L[ℝ] Y'), ‖ℓ‖ ≤ 1 → ∀ (f : E × Time → Y) (y : E × Time) (s : ℝ),
        affineErrorSq μ (fun q => ℓ (f q)) y s ≤ affineErrorSq μ f y s)
    (W : Submodule ℝ (Spatial n)) (C : ℝ)
    (hs : ∀ (F : FourierSpace (Module.finrank ℝ W) → ℝ) (L B R : ℝ), 0 ≤ L → 0 < R →
      HasCompactSupport F → HalfTimeDerivative.ParabolicLipschitz F L →
      HasAffineCarlesonBound (parabolicVolume (Module.finrank ℝ W))
        (fun z => F ((fourierToParabolic (Module.finrank ℝ W)).symm z)) B →
      ∃ (hF : MemLp F 2 volume) (a b : FourierSpace (Module.finrank ℝ W) → ℝ),
        HalfTimeDerivative.RepHalf hF (fun x => a x + b x)
          (analyticCylinder (point (0 : Spatial (Module.finrank ℝ W)) 0) R) ∧
        MemLp a 2 volume ∧
        ∫⁻ x, ‖a x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * (B + L ^ 2) * R ^ (Module.finrank ℝ W + 2)) ∧
        ∀ (u v : Spatial (Module.finrank ℝ W)) (t t₀ : ℝ), ‖u‖ < R → ‖v‖ < R → |t| < R ^ 2 →
          |t₀| < R ^ 2 → |b (WithLp.toLp 2 (u, t)) - b (WithLp.toLp 2 (v, t₀))| ≤ C * L)
    (F : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (B : ℝ)
    (hc : HasCompactSupport F) (hF : LipschitzWith L F)
    (hcarl : HasAffineCarlesonBound (intrinsicParabolicVolume W) F B)
    (p : SubspaceSpace W) (r : ℝ) (hr : 0 < r) (i : Fin (Module.finrank ℝ W.orthogonal)) :
    ∃ α β : FourierSpace (Module.finrank ℝ W) → ℝ,
      (∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
        HalfTimeDerivative.RepHalf hH (fun x => α x + β x)
          (subspaceFourierToParabolic W ⁻¹' Metric.ball p r)) ∧
      MemLp α 2 volume ∧
      ∫⁻ x, ‖α x‖ₑ ^ 2 ≤
        ENNReal.ofReal (C * (B + (L : ℝ) ^ 2) * r ^ (Module.finrank ℝ W + 2)) ∧
      IntegrableOn β (subspaceFourierToParabolic W ⁻¹' Metric.ball p r) volume ∧
      ∀ x ∈ subspaceFourierToParabolic W ⁻¹' Metric.ball p r,
        ∀ y ∈ subspaceFourierToParabolic W ⁻¹' Metric.ball p r, |β x - β y| ≤ C * L := by
  -- notation: `ι` the parabolic isometry, `q₀ = ι p`, `Θ x = x - x₀`, `ℓ` the coordinate
  have hℓ := rx5_norm_normalCoordinateCLM_le W i
  set ℓ := rx5_normalCoordinateCLM W i with hℓdef
  set q₀ : Space (Module.finrank ℝ W) := subspaceParabolicIsometry W p with hq₀
  have hΘMP := rx5_measurePreserving_translation q₀
  have hΘe : MeasurableEmbedding (fourierSimilarity q₀ 1 one_pos) :=
    (fourierSimilarity q₀ 1 one_pos).measurableEmbedding
  -- the centred component
  obtain ⟨G, hGdef⟩ : ∃ G : FourierSpace (Module.finrank ℝ W) → ℝ,
      G = fun y => normalFourierComponent W F i ((fourierSimilarity q₀ 1 one_pos).symm y) :=
    ⟨_, rfl⟩
  have hGform : ∀ y, G y = ℓ (F ((subspaceParabolicIsometry W).symm
      (fourierToParabolic (Module.finrank ℝ W) ((fourierSimilarity q₀ 1 one_pos).symm y)))) := by
    intro y
    rw [hGdef, hℓdef, rx5_normalCoordinateCLM_apply]
    simp only [normalFourierComponent, rx5_subspaceFourierToParabolic_eq]
  have hGpoint : ∀ (u : Spatial (Module.finrank ℝ W)) (t : ℝ),
      G (WithLp.toLp 2 (u, t)) =
        ℓ (F ((subspaceParabolicIsometry W).symm (point (u + q₀.1) (t + q₀.2.val)))) := by
    intro u t
    rw [hGform, fourierSimilarity_symm_apply, fourierToParabolic_apply]
    simp only [one_smul, one_pow, one_mul]
  have hGΘ : ∀ x, G (fourierSimilarity q₀ 1 one_pos x) = normalFourierComponent W F i x := by
    intro x
    simp only [hGdef, Homeomorph.symm_apply_apply]
  -- compact support
  have hGc : HasCompactSupport G := by
    have hcomp : HasCompactSupport (fun y => ℓ (F (((fourierSimilarity q₀ 1 one_pos).symm.trans
        ((fourierToParabolic (Module.finrank ℝ W)).trans
          (subspaceParabolicIsometry W).symm.toHomeomorph)) y))) :=
      (hc.comp_homeomorph _).comp_left (map_zero ℓ)
    convert hcomp using 1
    funext y
    rw [hGform]
    rfl
  -- parabolic Lipschitz bound
  have hGLip : HalfTimeDerivative.ParabolicLipschitz G (L : ℝ) := by
    intro u v t s
    rw [hGpoint, hGpoint, ← map_sub, ← Real.norm_eq_abs]
    calc ‖ℓ (F ((subspaceParabolicIsometry W).symm (point (u + q₀.1) (t + q₀.2.val))) -
            F ((subspaceParabolicIsometry W).symm (point (v + q₀.1) (s + q₀.2.val))))‖
        ≤ ‖ℓ‖ * ‖F ((subspaceParabolicIsometry W).symm (point (u + q₀.1) (t + q₀.2.val))) -
            F ((subspaceParabolicIsometry W).symm (point (v + q₀.1) (s + q₀.2.val)))‖ :=
          ℓ.le_opNorm _
      _ ≤ 1 * ‖F ((subspaceParabolicIsometry W).symm (point (u + q₀.1) (t + q₀.2.val))) -
            F ((subspaceParabolicIsometry W).symm (point (v + q₀.1) (s + q₀.2.val)))‖ :=
          mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
      _ = dist (F ((subspaceParabolicIsometry W).symm (point (u + q₀.1) (t + q₀.2.val))))
            (F ((subspaceParabolicIsometry W).symm (point (v + q₀.1) (s + q₀.2.val)))) := by
          rw [one_mul, dist_eq_norm]
      _ ≤ (L : ℝ) * dist ((subspaceParabolicIsometry W).symm (point (u + q₀.1) (t + q₀.2.val)))
            ((subspaceParabolicIsometry W).symm (point (v + q₀.1) (s + q₀.2.val))) :=
          hF.dist_le_mul _ _
      _ = (L : ℝ) * max ‖u - v‖ (Real.sqrt |t - s|) := by
          rw [IsometryEquiv.dist_eq, dist_point, add_sub_add_right_eq_sub,
            add_sub_add_right_eq_sub]
  -- affine Carleson bound of the centred component
  have hH₀ : HasAffineCarlesonBound (parabolicVolume (Module.finrank ℝ W))
      (fun z => F ((subspaceParabolicIsometry W).symm z)) B := by
    refine (hasAffineCarlesonBound_comp_subspaceParabolicIsometry_proof W _ B).2 ?_
    convert hcarl using 1
    funext x
    simp only [Function.comp_apply, IsometryEquiv.symm_apply_apply]
  have hT := (similarity_rescale_affine_proof
    (point (-q₀.1) (-q₀.2.val)) 1 one_pos
    (fun z => F ((subspaceParabolicIsometry W).symm z)) L B).2.2 hH₀
  have hT' := rx5_hasAffineCarlesonBound_comp_clm ℓ
    (fun y s => hA12c (parabolicVolume (Module.finrank ℝ W)) ℓ hℓ _ y s) hT
  have hGcarl : HasAffineCarlesonBound (parabolicVolume (Module.finrank ℝ W))
      (fun z => G ((fourierToParabolic (Module.finrank ℝ W)).symm z)) B := by
    convert hT' using 1
    funext z
    rw [hGform, one_smul, similarity_apply, fourierToParabolic_apply,
      fourierSimilarity_symm_apply, fourierToParabolic_symm_apply]
    simp only [rx5_point_fst, rx5_point_snd_val, inv_one, one_smul, one_pow, one_mul,
      sub_neg_eq_add]
  -- the scalar decomposition of the centred component
  obtain ⟨hGm, α', β', hrep', hα'm, hα'E, hosc'⟩ :=
    hs G L B r L.coe_nonneg hr hGc hGLip hGcarl
  -- transport back to the centre
  obtain ⟨hH', hrepΘ⟩ := rx5_repHalf_comp_fourierSimilarity_local q₀ 1 one_pos hGm hrep'
  have hfeq : (fun x => (1 : ℝ) * G (fourierSimilarity q₀ 1 one_pos x)) =
      normalFourierComponent W F i := by
    funext x
    rw [one_mul, hGΘ]
  have hfi : MemLp (normalFourierComponent W F i) 2 volume := hfeq ▸ hH'
  have hset : fourierSimilarity q₀ 1 one_pos ⁻¹'
      analyticCylinder (point (0 : Spatial (Module.finrank ℝ W)) 0) r =
        subspaceFourierToParabolic W ⁻¹' Metric.ball p r := by
    rw [subspaceFourier_preimage_ball W p r hr, rx5_preimage_cylinder]
  have hβcyl := rx5_integrableOn_of_osc hr hα'm hrep'.2.1
    (fun x hx y hy => rx5_osc_of_cylinder hosc' hx hy)
  refine ⟨fun x => α' (fourierSimilarity q₀ 1 one_pos x),
    fun x => β' (fourierSimilarity q₀ 1 one_pos x), ⟨hfi, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [← hset]
    exact (HalfTimeDerivative.repHalf_congr hH' hfi (Filter.EventuallyEq.of_eq hfeq)
      Filter.EventuallyEq.rfl).1 hrepΘ
  · exact hα'm.comp_measurePreserving hΘMP
  · rw [hΘMP.lintegral_comp_emb hΘe (fun y => ‖α' y‖ₑ ^ 2)]
    exact hα'E
  · rw [← hset]
    exact (hΘMP.integrableOn_comp_preimage hΘe).2 hβcyl
  · intro x hx y hy
    rw [← hset] at hx hy
    exact rx5_osc_of_cylinder hosc' hx hy

end ParabolicRectifiability
