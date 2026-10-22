import ParabolicRectifiability.Analysis.RegularExtension.LocalComponent

/-! # Vector local half-time decomposition from the scalar one

`exists_local_halfTime_decomposition_of_scalar_of_component` is the local half-time
decomposition of a vector-valued function, stated in implication form: its first hypothesis
`hA12c` is the coordinate estimate `affineErrorSq_component_le` (at universe `0`), which is
proved in `ComponentError`.

The components (`rx5_component_decomposition`, `LocalComponent`) are assembled with
`(normalCoordinates W)⁻¹`. Parseval gives `∫ ‖a‖² = Σ_i ∫ a_i² ≤ d C (B + L²) r^(m+2)` and
`‖b x - b y‖ ≤ √d C L` on the ball. With `|P(p,r)| = 2ω_m r^(m+2)` and
`B + L² ≤ (L + √B)²`, the constant `C' = √d C + √(d C / (2ω_m))` depends only on `m, d, C`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ}

/-- **Vector local decomposition on one ball** (fixed `W`, constants not yet normalized). -/
theorem rx5_local_decomposition_core
    (hA12c : ∀ {E Y Y' : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] (μ : Measure (E × Time))
      (ℓ : Y →L[ℝ] Y'), ‖ℓ‖ ≤ 1 → ∀ (f : E × Time → Y) (y : E × Time) (s : ℝ),
        affineErrorSq μ (fun q => ℓ (f q)) y s ≤ affineErrorSq μ f y s)
    (W : Submodule ℝ (Spatial n)) (C : ℝ) (hC : 0 ≤ C)
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
    (p : SubspaceSpace W) (r : ℝ) (hr : 0 < r) :
    ∃ a b : SubspaceSpace W → W.orthogonal,
      (∀ i, ∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
        HalfTimeDerivative.RepHalf hH (normalFourierComponent W (fun x => a x + b x) i)
          (subspaceFourierToParabolic W ⁻¹' Metric.ball p r)) ∧
      MemLp a 2 (intrinsicParabolicVolume W) ∧
      ∫⁻ x, ‖a x‖ₑ ^ 2 ∂intrinsicParabolicVolume W ≤
        ENNReal.ofReal ((Module.finrank ℝ W.orthogonal : ℝ) *
          (C * (B + (L : ℝ) ^ 2) * r ^ (Module.finrank ℝ W + 2))) ∧
      IntegrableOn b (Metric.ball p r) (intrinsicParabolicVolume W) ∧
      ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        ‖b x - b y‖ ≤ Real.sqrt (Module.finrank ℝ W.orthogonal) * (C * L) := by
  choose α β hcomp using
    fun i => rx5_component_decomposition hA12c W C hs F L B hc hF hcarl p r hr i
  have hφ : MeasurePreserving (subspaceFourierToParabolic W).symm
      (intrinsicParabolicVolume W) volume :=
    (subspaceFourierToParabolic_measurePreserving W).symm
  have hφe : MeasurableEmbedding (subspaceFourierToParabolic W).symm :=
    (subspaceFourierToParabolic W).symm.measurableEmbedding
  have hball : (subspaceFourierToParabolic W).symm ⁻¹'
      (subspaceFourierToParabolic W ⁻¹' Metric.ball p r) = Metric.ball p r := by
    ext x
    simp only [mem_preimage, MeasurableEquiv.apply_symm_apply]
  have hαμ : ∀ i, MemLp (fun q => α i ((subspaceFourierToParabolic W).symm q)) 2
      (intrinsicParabolicVolume W) := fun i => (hcomp i).2.1.comp_measurePreserving hφ
  refine ⟨fun q => (normalCoordinates W).symm
      (WithLp.toLp 2 (fun i => α i ((subspaceFourierToParabolic W).symm q))),
    fun q => (normalCoordinates W).symm
      (WithLp.toLp 2 (fun i => β i ((subspaceFourierToParabolic W).symm q))),
    ?_, rx5_memLp_assemble W _ hαμ, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hH, hrep⟩ := (hcomp i).1
    refine ⟨hH, (HalfTimeDerivative.repHalf_congr hH hH Filter.EventuallyEq.rfl
      (Filter.EventuallyEq.of_eq ?_)).1 hrep⟩
    funext x
    simp only [normalFourierComponent, map_add, PiLp.add_apply,
      rx5_normalCoordinates_assemble, MeasurableEquiv.symm_apply_apply]
  · calc ∫⁻ x, ‖(normalCoordinates W).symm
          (WithLp.toLp 2 (fun i => α i ((subspaceFourierToParabolic W).symm x)))‖ₑ ^ 2
          ∂intrinsicParabolicVolume W
        = ∫⁻ x, ∑ i, ‖α i ((subspaceFourierToParabolic W).symm x)‖ₑ ^ 2
            ∂intrinsicParabolicVolume W := by
          refine lintegral_congr fun x => ?_
          exact rx5_enorm_sq_assemble W _
      _ = ∑ i, ∫⁻ x, ‖α i ((subspaceFourierToParabolic W).symm x)‖ₑ ^ 2
            ∂intrinsicParabolicVolume W :=
          lintegral_finsetSum' _ fun i _ => (hαμ i).aestronglyMeasurable.enorm.pow_const 2
      _ = ∑ i, ∫⁻ y, ‖α i y‖ₑ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact hφ.lintegral_comp_emb hφe (fun y => ‖α i y‖ₑ ^ 2)
      _ ≤ ∑ _i : Fin (Module.finrank ℝ W.orthogonal),
            ENNReal.ofReal (C * (B + (L : ℝ) ^ 2) * r ^ (Module.finrank ℝ W + 2)) :=
          Finset.sum_le_sum fun i _ => (hcomp i).2.2.1
      _ = ENNReal.ofReal ((Module.finrank ℝ W.orthogonal : ℝ) *
            (C * (B + (L : ℝ) ^ 2) * r ^ (Module.finrank ℝ W + 2))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · rw [IntegrableOn, ← memLp_one_iff_integrable]
    refine rx5_memLp_assemble W _ fun i => ?_
    rw [memLp_one_iff_integrable]
    have h := (hφ.integrableOn_comp_preimage hφe).2 (hcomp i).2.2.2.1
    rw [hball] at h
    exact h
  · intro x hx y hy
    have hx' : (subspaceFourierToParabolic W).symm x ∈
        subspaceFourierToParabolic W ⁻¹' Metric.ball p r := by
      rwa [mem_preimage, MeasurableEquiv.apply_symm_apply]
    have hy' : (subspaceFourierToParabolic W).symm y ∈
        subspaceFourierToParabolic W ⁻¹' Metric.ball p r := by
      rwa [mem_preimage, MeasurableEquiv.apply_symm_apply]
    have hCL : 0 ≤ C * (L : ℝ) := mul_nonneg hC L.coe_nonneg
    have hsq : ‖(normalCoordinates W).symm
          (WithLp.toLp 2 (fun i => β i ((subspaceFourierToParabolic W).symm x))) -
        (normalCoordinates W).symm
          (WithLp.toLp 2 (fun i => β i ((subspaceFourierToParabolic W).symm y)))‖ ^ 2 ≤
        (Real.sqrt (Module.finrank ℝ W.orthogonal) * (C * L)) ^ 2 := by
      rw [rx5_norm_sq_eq_sum, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      calc ∑ i, normalCoordinates W ((normalCoordinates W).symm
              (WithLp.toLp 2 (fun i => β i ((subspaceFourierToParabolic W).symm x))) -
            (normalCoordinates W).symm
              (WithLp.toLp 2 (fun i => β i ((subspaceFourierToParabolic W).symm y)))) i ^ 2
          = ∑ i, (β i ((subspaceFourierToParabolic W).symm x) -
              β i ((subspaceFourierToParabolic W).symm y)) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_sub, PiLp.sub_apply, rx5_normalCoordinates_assemble,
              rx5_normalCoordinates_assemble]
        _ ≤ ∑ _i : Fin (Module.finrank ℝ W.orthogonal), (C * (L : ℝ)) ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) ((hcomp i).2.2.2.2 _ hx' _ hy') 2
        _ = (Module.finrank ℝ W.orthogonal : ℝ) * (C * (L : ℝ)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hCL) two_ne_zero).1 hsq

/-- **Local half-time decomposition in implication form**
(`exists_local_halfTime_decomposition_of_scalar`). The hypothesis `hA12c` is the coordinate
estimate `affineErrorSq_component_le` at universe `0`. -/
theorem exists_local_halfTime_decomposition_of_scalar_of_component
    (hA12c : ∀ {E Y Y' : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] (μ : Measure (E × Time))
      (ℓ : Y →L[ℝ] Y'), ‖ℓ‖ ≤ 1 → ∀ (f : E × Time → Y) (y : E × Time) (s : ℝ),
        affineErrorSq μ (fun q => ℓ (f q)) y s ≤ affineErrorSq μ f y s)
    (m d : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ (F : FourierSpace m → ℝ) (L B R : ℝ), 0 ≤ L → 0 < R → HasCompactSupport F →
      HalfTimeDerivative.ParabolicLipschitz F L →
      HasAffineCarlesonBound (parabolicVolume m) (fun z => F ((fourierToParabolic m).symm z)) B →
      ∃ (hF : MemLp F 2 volume) (a b : FourierSpace m → ℝ),
        HalfTimeDerivative.RepHalf hF (fun x => a x + b x)
          (analyticCylinder (point (0 : Spatial m) 0) R) ∧
        MemLp a 2 volume ∧
        ∫⁻ x, ‖a x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * (B + L ^ 2) * R ^ (m + 2)) ∧
        ∀ (u v : Spatial m) (t t₀ : ℝ), ‖u‖ < R → ‖v‖ < R → |t| < R ^ 2 → |t₀| < R ^ 2 →
          |b (WithLp.toLp 2 (u, t)) - b (WithLp.toLp 2 (v, t₀))| ≤ C * L) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)),
      Module.finrank ℝ W = m → Module.finrank ℝ W.orthogonal = d →
      ∀ (F : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (B : ℝ),
        HasCompactSupport F → LipschitzWith L F →
        HasAffineCarlesonBound (intrinsicParabolicVolume W) F B →
        ∀ (p : SubspaceSpace W) (r : ℝ), 0 < r →
          ∃ a b : SubspaceSpace W → W.orthogonal,
            (∀ i, ∃ hH : MemLp (normalFourierComponent W F i) 2 volume,
              HalfTimeDerivative.RepHalf hH (normalFourierComponent W (fun x => a x + b x) i)
                (subspaceFourierToParabolic W ⁻¹' Metric.ball p r)) ∧
            MemLp a 2 ((intrinsicParabolicVolume W).restrict (Metric.ball p r)) ∧
            ∫ x in Metric.ball p r, ‖a x‖ ^ 2 ∂intrinsicParabolicVolume W ≤
              (C' * ((L : ℝ) + Real.sqrt B)) ^ 2 *
                (intrinsicParabolicVolume W).real (Metric.ball p r) ∧
            IntegrableOn b (Metric.ball p r) (intrinsicParabolicVolume W) ∧
            ∀ᵐ xy ∂((intrinsicParabolicVolume W).restrict (Metric.ball p r)).prod
                ((intrinsicParabolicVolume W).restrict (Metric.ball p r)),
              ‖b xy.1 - b xy.2‖ ≤ C' * L := by
  -- `V = |P(·,1)| = 2 ω_m`, depending only on `m`
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (2 * omega m).toReal := ⟨_, rfl⟩
  have hV : 0 < V := by
    rw [hVdef]
    exact ENNReal.toReal_pos (mul_ne_zero two_ne_zero (omega_pos m).ne')
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne)
  have hdC : 0 ≤ (d : ℝ) * C := mul_nonneg (Nat.cast_nonneg d) hC
  refine ⟨Real.sqrt d * C + Real.sqrt ((d : ℝ) * C / V),
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC) (Real.sqrt_nonneg _), ?_⟩
  intro n W hm hd F L B hc hF hcarl p r hr
  subst hm hd
  have hB : 0 ≤ B := hcarl.1
  obtain ⟨a, b, hrep, ha2, haE, hbI, hbosc⟩ :=
    rx5_local_decomposition_core hA12c W C hC hs F L B hc hF hcarl p r hr
  set C' := Real.sqrt (Module.finrank ℝ W.orthogonal) * C +
    Real.sqrt ((Module.finrank ℝ W.orthogonal : ℝ) * C / V)
  have hC'1 : Real.sqrt (Module.finrank ℝ W.orthogonal) * C ≤ C' :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hC'2 : (Module.finrank ℝ W.orthogonal : ℝ) * C ≤ C' ^ 2 * V := by
    have h1 : Real.sqrt ((Module.finrank ℝ W.orthogonal : ℝ) * C / V) ≤ C' :=
      le_add_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) hC)
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [Real.sq_sqrt (div_nonneg hdC hV.le)] at h2
    calc (Module.finrank ℝ W.orthogonal : ℝ) * C
        = (Module.finrank ℝ W.orthogonal : ℝ) * C / V * V := (div_mul_cancel₀ _ hV.ne').symm
      _ ≤ C' ^ 2 * V := mul_le_mul_of_nonneg_right h2 hV.le
  have hvol : (intrinsicParabolicVolume W).real (Metric.ball p r) =
      V * r ^ (Module.finrank ℝ W + 2) := by
    rw [hVdef, Measure.real_def, intrinsicParabolicVolume_ball W p r hr, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le]
  refine ⟨a, b, hrep, ha2.restrict _, ?_, hbI, ?_⟩
  · -- the `L²` bound on the ball
    have hint : Integrable (fun x => ‖a x‖ ^ 2)
        ((intrinsicParabolicVolume W).restrict (Metric.ball p r)) :=
      (memLp_two_iff_integrable_sq_norm (ha2.restrict _).aestronglyMeasurable).1
        (ha2.restrict _)
    have hX : 0 ≤ (Module.finrank ℝ W.orthogonal : ℝ) *
        (C * (B + (L : ℝ) ^ 2) * r ^ (Module.finrank ℝ W + 2)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hC
        (add_nonneg hB (sq_nonneg _))) (pow_nonneg hr.le _))
    have h1 : ENNReal.ofReal (∫ x in Metric.ball p r, ‖a x‖ ^ 2 ∂intrinsicParabolicVolume W) ≤
        ENNReal.ofReal ((Module.finrank ℝ W.orthogonal : ℝ) *
          (C * (B + (L : ℝ) ^ 2) * r ^ (Module.finrank ℝ W + 2))) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      calc ∫⁻ x in Metric.ball p r, ENNReal.ofReal (‖a x‖ ^ 2) ∂intrinsicParabolicVolume W
          = ∫⁻ x in Metric.ball p r, ‖a x‖ₑ ^ 2 ∂intrinsicParabolicVolume W := by
            refine lintegral_congr fun x => ?_
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        _ ≤ ∫⁻ x, ‖a x‖ₑ ^ 2 ∂intrinsicParabolicVolume W := setLIntegral_le_lintegral _ _
        _ ≤ _ := haE
    have h2 := (ENNReal.ofReal_le_ofReal_iff hX).1 h1
    refine h2.trans ?_
    have hLB : (L : ℝ) ^ 2 + B ≤ ((L : ℝ) + Real.sqrt B) ^ 2 := by
      have := Real.sq_sqrt hB
      nlinarith [Real.sqrt_nonneg B, L.coe_nonneg]
    have hr' : 0 ≤ r ^ (Module.finrank ℝ W + 2) := pow_nonneg hr.le _
    rw [hvol]
    calc (Module.finrank ℝ W.orthogonal : ℝ) *
          (C * (B + (L : ℝ) ^ 2) * r ^ (Module.finrank ℝ W + 2))
        = ((Module.finrank ℝ W.orthogonal : ℝ) * C) *
            (((L : ℝ) ^ 2 + B) * r ^ (Module.finrank ℝ W + 2)) := by ring
      _ ≤ (C' ^ 2 * V) * (((L : ℝ) + Real.sqrt B) ^ 2 * r ^ (Module.finrank ℝ W + 2)) :=
          mul_le_mul hC'2 (mul_le_mul_of_nonneg_right hLB hr')
            (mul_nonneg (add_nonneg (sq_nonneg _) hB) hr')
            (mul_nonneg (sq_nonneg _) hV.le)
      _ = (C' * ((L : ℝ) + Real.sqrt B)) ^ 2 * (V * r ^ (Module.finrank ℝ W + 2)) := by ring
  · -- the pairwise bound almost everywhere on the product of the restricted volumes
    -- `intrinsicParabolicVolume W` is the image of the s-finite `volume.prod volume`
    have : SFinite (intrinsicParabolicVolume W) := by
      unfold intrinsicParabolicVolume
      infer_instance
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_ball.prod measurableSet_ball) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine (hbosc x hx y hy).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hC'1 L.coe_nonneg

end ParabolicRectifiability
