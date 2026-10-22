import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Metric.Similarity

/-! # Similarity transport of the trace error

* `traceErrorSq_similarity_proof`: exact change of variables of the trace error under the
  parabolic similarity `T = similarity x₀ ρ`;
* `similarity_rescale_affine_proof`: the rescaled function `p ↦ ρ H(T p)` keeps the
  Lipschitz constant, compact support and affine Carleson constant of `H`.

Measure transport: `T` is a translation followed by the dilation by `ρ⁻¹`, so
`T_* dp = ρ^(m+2) dp`, and `∫_S φ(T z) dp(z) = ρ^(m+2) ∫_{T S} φ dp` for every set `S` and
every (not necessarily measurable) `φ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-! ## Transport of the parabolic volume -/

/-- Translations preserve the parabolic volume. -/
theorem map_translation_parabolicVolume {n : ℕ} (q : Space n) :
    Measure.map (translationHomeomorph q) (parabolicVolume n) = parabolicVolume n := by
  have hfun : (translationHomeomorph q : Space n → Space n) ∘ (coordinatesHomeomorph n).symm =
      (coordinatesHomeomorph n).symm ∘ (fun y : Coordinates n => y + (-q.1, -q.2.val)) := by
    funext y
    show point (y.1 - q.1) (y.2 - q.2.val) = point (y.1 + -q.1) (y.2 + -q.2.val)
    rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [parabolicVolume, Measure.map_map (translationHomeomorph q).measurable
      (coordinatesHomeomorph n).symm.measurable, hfun,
    ← Measure.map_map (coordinatesHomeomorph n).symm.measurable (measurable_add_const _),
    coordinateVolume, map_add_right_eq_self]

/-- `T_* dp = ρ^(n+2) dp` for the similarity `T = similarity q ρ`. -/
theorem map_similarity_parabolicVolume {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) :
    Measure.map (similarity q a ha) (parabolicVolume n) =
      ENNReal.ofReal a ^ (n + 2) • parabolicVolume n := by
  have hfun : (similarity q a ha : Space n → Space n) = dilate a⁻¹ ∘ translationHomeomorph q :=
    rfl
  rw [hfun, ← Measure.map_map (measurable_dilate a⁻¹) (translationHomeomorph q).measurable,
    map_translation_parabolicVolume, map_dilate_parabolicVolume a⁻¹ (inv_pos.2 ha),
    ENNReal.ofReal_inv_of_pos ha, inv_inv]

/-- Change of variables for lower integrals over arbitrary sets:
`∫_S φ(T z) dp(z) = ρ^(n+2) ∫_{T S} φ dp`. -/
theorem setLIntegral_comp_similarity {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a)
    (S : Set (Space n)) (φ : Space n → ℝ≥0∞) :
    ∫⁻ z in S, φ (similarity q a ha z) ∂parabolicVolume n =
      ENNReal.ofReal a ^ (n + 2) * ∫⁻ w in similarity q a ha '' S, φ w ∂parabolicVolume n := by
  set e := similarityMeasurableEquiv q a ha with he_def
  have he : (e : Space n → Space n) = similarity q a ha := rfl
  calc ∫⁻ z in S, φ (similarity q a ha z) ∂parabolicVolume n
      = ∫⁻ w, φ w ∂(((parabolicVolume n).restrict S).map e) := by
        rw [lintegral_map_equiv, he]
    _ = ∫⁻ w, φ w ∂(((parabolicVolume n).map e).restrict (e '' S)) := by
        rw [e.restrict_map, e.preimage_image]
    _ = _ := by
        rw [he, map_similarity_parabolicVolume, Measure.restrict_smul, lintegral_smul_measure,
          smul_eq_mul]

/-- The base dimension of `ℝ^m × Time` is `m + 2`. -/
private theorem baseDimension_spatial (m : ℕ) : baseDimension (Spatial m) = m + 2 := by
  show Module.finrank ℝ (Spatial m) + 2 = m + 2
  rw [finrank_euclideanSpace_fin]

/-! ## Change of variables of the trace error -/

/-- **Change of variables of the trace error.** With `T = similarity x₀ ρ`, each fit
integral on the left equals `ρ^(-(m+2)) ρ^(-2)` times the fit integral on the right for the
competitor `(v + ρ a - B x₀ₓ, B)`, a bijective reparametrization of the affine maps; the
normalizations `(r/ρ)^(-(m+4))` and `r^(-(m+4))` absorb the factor exactly. Nonpositive
radii give zero on both sides. -/
theorem traceErrorSq_similarity_proof {m : ℕ} (x₀ : Space m) (ρ : ℝ) (hρ : 0 < ρ) {Y : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (K : Set (Space m)) (f : Space m → Y)
    (v : Y) (p : Space m) (r : ℝ) :
    traceErrorSq (parabolicVolume m) (similarity x₀ ρ hρ '' K)
        (fun q => ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - v)) (similarity x₀ ρ hρ p) (r / ρ) =
      traceErrorSq (parabolicVolume m) K f p r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [traceErrorSq, traceErrorSq, affineErrorSq_of_nonpos _ _ _ hr,
      affineErrorSq_of_nonpos _ _ _ (div_nonpos_of_nonpos_of_nonneg hr hρ.le)]
  have hρk0 : ENNReal.ofReal ρ ^ (m + 2) ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.2 hρ)
  have hρkt : ENNReal.ofReal ρ ^ (m + 2) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hc0 : (ENNReal.ofReal ρ ^ (m + 2))⁻¹ * ENNReal.ofReal ρ⁻¹ ^ 2 ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 hρkt)
      (pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 hρ)))
  have hct : (ENNReal.ofReal ρ ^ (m + 2))⁻¹ * ENNReal.ofReal ρ⁻¹ ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hρk0) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hfit : ∀ (a : Y) (B : Spatial m →L[ℝ] Y),
      affineFitIntegral ((parabolicVolume m).restrict (similarity x₀ ρ hρ '' K))
          (fun q => ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - v)) a B
          (similarity x₀ ρ hρ p) (r / ρ) =
        (ENNReal.ofReal ρ ^ (m + 2))⁻¹ * ENNReal.ofReal ρ⁻¹ ^ 2 *
          affineFitIntegral ((parabolicVolume m).restrict K) f (v + ρ • a - B x₀.1) B p r := by
    intro a B
    simp only [affineFitIntegral]
    rw [Measure.restrict_restrict measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
    have hset : Metric.ball (similarity x₀ ρ hρ p) (r / ρ) ∩ similarity x₀ ρ hρ '' K =
        similarity x₀ ρ hρ '' (Metric.ball p r ∩ K) := by
      rw [Set.image_inter (similarity x₀ ρ hρ).injective, image_similarity_ball]
    rw [hset]
    have h := setLIntegral_comp_similarity x₀ ρ hρ (Metric.ball p r ∩ K)
      (fun q => ‖ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - v) - (a + B q.1)‖ₑ ^ 2)
    have hpt : ∀ z : Space m,
        ‖ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm (similarity x₀ ρ hρ z)) - v) -
            (a + B (similarity x₀ ρ hρ z).1)‖ₑ ^ 2 =
          ENNReal.ofReal ρ⁻¹ ^ 2 * ‖f z - (v + ρ • a - B x₀.1 + B z.1)‖ₑ ^ 2 := by
      intro z
      have h1 : (similarity x₀ ρ hρ z).1 = ρ⁻¹ • (z.1 - x₀.1) := by
        rw [similarity_apply]
        rfl
      have h2 : ρ⁻¹ • (f z - v) - (a + B (ρ⁻¹ • (z.1 - x₀.1))) =
          ρ⁻¹ • (f z - (v + ρ • a - B x₀.1 + B z.1)) := by
        rw [map_smul, map_sub]
        simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
        abel
      rw [Homeomorph.symm_apply_apply, h1, h2, enorm_smul,
        Real.enorm_eq_ofReal (inv_nonneg.2 hρ.le), mul_pow]
    simp only [hpt] at h
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)] at h
    calc ∫⁻ q in similarity x₀ ρ hρ '' (Metric.ball p r ∩ K),
          ‖ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - v) - (a + B q.1)‖ₑ ^ 2 ∂parabolicVolume m
        = (ENNReal.ofReal ρ ^ (m + 2))⁻¹ * (ENNReal.ofReal ρ ^ (m + 2) *
            ∫⁻ q in similarity x₀ ρ hρ '' (Metric.ball p r ∩ K),
              ‖ρ⁻¹ • (f ((similarity x₀ ρ hρ).symm q) - v) - (a + B q.1)‖ₑ ^ 2
                ∂parabolicVolume m) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hρk0 hρkt, one_mul]
      _ = (ENNReal.ofReal ρ ^ (m + 2))⁻¹ * (ENNReal.ofReal ρ⁻¹ ^ 2 *
            ∫⁻ q in Metric.ball p r ∩ K, ‖f q - (v + ρ • a - B x₀.1 + B q.1)‖ₑ ^ 2
              ∂parabolicVolume m) := by rw [h]
      _ = _ := by rw [mul_assoc]
  rw [traceErrorSq, traceErrorSq, affineErrorSq_of_pos _ _ _ (div_pos hr hρ),
    affineErrorSq_of_pos _ _ _ hr, baseDimension_spatial]
  simp only [hfit]
  have hinf : (⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
        (ENNReal.ofReal ρ ^ (m + 2))⁻¹ * ENNReal.ofReal ρ⁻¹ ^ 2 *
          affineFitIntegral ((parabolicVolume m).restrict K) f (v + ρ • a - B x₀.1) B p r) =
      (ENNReal.ofReal ρ ^ (m + 2))⁻¹ * ENNReal.ofReal ρ⁻¹ ^ 2 *
        ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
          affineFitIntegral ((parabolicVolume m).restrict K) f a B p r := by
    rw [ENNReal.mul_iInf_of_ne hc0 hct]
    simp_rw [ENNReal.mul_iInf_of_ne hc0 hct]
    refine le_antisymm (le_iInf₂ fun a B => ?_) (le_iInf₂ fun a B => ?_)
    · have hae : v + ρ • (ρ⁻¹ • (a - v + B x₀.1)) - B x₀.1 = a := by
        rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
        abel
      refine iInf₂_le_of_le (ρ⁻¹ • (a - v + B x₀.1)) B ?_
      rw [hae]
    · exact iInf₂_le _ _
  rw [hinf, ← mul_assoc]
  congr 1
  have e1 : (ENNReal.ofReal (r / ρ))⁻¹ ^ (m + 2 + 2) = ENNReal.ofReal ((ρ / r) ^ (m + 2 + 2)) := by
    rw [← ENNReal.ofReal_inv_of_pos (div_pos hr hρ), inv_div,
      ENNReal.ofReal_pow (div_pos hρ hr).le]
  have e2 : (ENNReal.ofReal ρ ^ (m + 2))⁻¹ = ENNReal.ofReal ((ρ ^ (m + 2))⁻¹) := by
    rw [← ENNReal.ofReal_pow hρ.le, ENNReal.ofReal_inv_of_pos (pow_pos hρ _)]
  have e3 : ENNReal.ofReal ρ⁻¹ ^ 2 = ENNReal.ofReal (ρ⁻¹ ^ 2) :=
    (ENNReal.ofReal_pow (inv_nonneg.2 hρ.le) 2).symm
  have e4 : (ENNReal.ofReal r)⁻¹ ^ (m + 2 + 2) = ENNReal.ofReal (r⁻¹ ^ (m + 2 + 2)) := by
    rw [← ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_pow (inv_nonneg.2 hr.le)]
  rw [e1, e2, e3, e4, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-! ## Rescaling preserves the Lipschitz, support and Carleson data -/

/-- The scale measure `ds/s` is invariant under `s ↦ c s`, `c > 0` (local copy). -/
private theorem scaleMeasure_map_mul_left_aux {c : ℝ} (hc : 0 < c) :
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

/-- Change of scale `t = c s` for `ds/s`, valid for every function (local copy). -/
private theorem setLIntegral_scaleMeasure_comp_mul_left_aux {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℝ≥0∞) (T : Set ℝ) :
    ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure = ∫⁻ t in T, f t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  symm
  calc
    ∫⁻ t in T, f t ∂scaleMeasure = ∫⁻ t in T, f t ∂(Measure.map e scaleMeasure) := by
      rw [he, scaleMeasure_map_mul_left_aux hc]
    _ = ∫⁻ t, f t ∂((scaleMeasure.restrict (e ⁻¹' T)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, f (e s) ∂(scaleMeasure.restrict (e ⁻¹' T)) := lintegral_map_equiv f e
    _ = ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure := by
      rw [he]

/-- **Rescaling** at the Lipschitz–Carleson level. For
`H_ρ = ρ H∘T`: `dist(H_ρ p, H_ρ q) = ρ dist(H(Tp), H(Tq)) ≤ ρ L ρ⁻¹ dist(p,q)`; the support
of `H_ρ` lies in `T⁻¹(supp H)`; and by `traceErrorSq_similarity_proof` with `K = univ`, `v = 0`,
`κ_{H_ρ}(y,s)² = κ_H(Ty, s/ρ)²`, so substituting `u = s/ρ` and `y' = Ty` gives
`Carl_{H_ρ}(z,R) = ρ^(m+2) Carl_H(Tz, R/ρ) ≤ ρ^(m+2) B (R/ρ)^(m+2) = B R^(m+2)`. -/
theorem similarity_rescale_affine_proof {m : ℕ} (x₀ : Space m) (ρ : ℝ) (hρ : 0 < ρ)
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (H : Space m → Y) (L : ℝ≥0)
    (B : ℝ) :
    (LipschitzWith L H → LipschitzWith L (fun p => ρ • H (similarity x₀ ρ hρ p))) ∧
    (HasCompactSupport H → HasCompactSupport (fun p => ρ • H (similarity x₀ ρ hρ p))) ∧
    (HasAffineCarlesonBound (parabolicVolume m) H B →
      HasAffineCarlesonBound (parabolicVolume m) (fun p => ρ • H (similarity x₀ ρ hρ p)) B) := by
  refine ⟨fun hH => ?_, fun hH => ?_, fun hH => ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [dist_smul₀, Real.norm_of_nonneg hρ.le]
    calc ρ * dist (H (similarity x₀ ρ hρ p)) (H (similarity x₀ ρ hρ q))
        ≤ ρ * (L * dist (similarity x₀ ρ hρ p) (similarity x₀ ρ hρ q)) :=
          mul_le_mul_of_nonneg_left (hH.dist_le_mul _ _) hρ.le
      _ = L * (ρ * ρ⁻¹) * dist p q := by rw [dist_similarity]; ring
      _ = L * dist p q := by rw [mul_inv_cancel₀ hρ.ne', mul_one]
  · refine (hH.comp_homeomorph (similarity x₀ ρ hρ)).mono fun p hp => ?_
    simp only [Function.mem_support, Function.comp_apply] at hp ⊢
    intro h0
    exact hp (by rw [h0, smul_zero])
  · obtain ⟨hB, hC⟩ := hH
    refine ⟨hB, fun z R hR => ?_⟩
    have hκ : ∀ y s, affineErrorSq (parabolicVolume m) (fun p => ρ • H (similarity x₀ ρ hρ p))
        y s = affineErrorSq (parabolicVolume m) H (similarity x₀ ρ hρ y) (ρ⁻¹ * s) := by
      intro y s
      have h := traceErrorSq_similarity_proof x₀ ρ hρ univ
        (fun p => ρ • H (similarity x₀ ρ hρ p)) 0 y s
      simp only [traceErrorSq, Set.image_univ_of_surjective (similarity x₀ ρ hρ).surjective,
        Measure.restrict_univ, sub_zero, Homeomorph.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ hρ.ne', one_smul] at h
      rw [← h, div_eq_inv_mul s ρ]
    have hpre : (fun s => ρ⁻¹ * s) ⁻¹' Ioo 0 (R / ρ) = Ioo 0 R := by
      ext s
      simp only [mem_preimage, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨pos_of_mul_pos_right h1 (inv_pos.2 hρ).le, ?_⟩
        rw [div_eq_inv_mul] at h2
        exact lt_of_mul_lt_mul_left h2 (inv_pos.2 hρ).le
      · rintro ⟨h1, h2⟩
        refine ⟨mul_pos (inv_pos.2 hρ) h1, ?_⟩
        rw [div_eq_inv_mul]
        exact mul_lt_mul_of_pos_left h2 (inv_pos.2 hρ)
    have hR' : 0 < R / ρ := div_pos hR hρ
    calc affineCarlesonIntegral (parabolicVolume m) (fun p => ρ • H (similarity x₀ ρ hρ p)) z R
        = ∫⁻ y in Metric.ball z R, (fun w => ∫⁻ u in Ioo 0 (R / ρ),
            affineErrorSq (parabolicVolume m) H w u ∂scaleMeasure) (similarity x₀ ρ hρ y)
              ∂parabolicVolume m := by
          unfold affineCarlesonIntegral
          refine lintegral_congr fun y => ?_
          simp only [hκ]
          rw [← hpre, setLIntegral_scaleMeasure_comp_mul_left_aux (inv_pos.2 hρ)
            (fun u => affineErrorSq (parabolicVolume m) H (similarity x₀ ρ hρ y) u)]
      _ = ENNReal.ofReal ρ ^ (m + 2) * ∫⁻ w in similarity x₀ ρ hρ '' Metric.ball z R,
            ∫⁻ u in Ioo 0 (R / ρ), affineErrorSq (parabolicVolume m) H w u ∂scaleMeasure
              ∂parabolicVolume m :=
          setLIntegral_comp_similarity x₀ ρ hρ (Metric.ball z R) (fun w =>
            ∫⁻ u in Ioo 0 (R / ρ), affineErrorSq (parabolicVolume m) H w u ∂scaleMeasure)
      _ = ENNReal.ofReal ρ ^ (m + 2) *
            affineCarlesonIntegral (parabolicVolume m) H (similarity x₀ ρ hρ z) (R / ρ) := by
          rw [image_similarity_ball]
          rfl
      _ ≤ ENNReal.ofReal ρ ^ (m + 2) *
            ENNReal.ofReal (B * (R / ρ) ^ baseDimension (Spatial m)) :=
          mul_le_mul_right (hC _ _ hR') _
      _ = ENNReal.ofReal (B * R ^ baseDimension (Spatial m)) := by
          rw [baseDimension_spatial, ← ENNReal.ofReal_pow hρ.le,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_pow, mul_div_assoc', mul_div_assoc',
            mul_div_cancel_left₀ _ (pow_ne_zero _ hρ.ne')]

end ParabolicRectifiability
