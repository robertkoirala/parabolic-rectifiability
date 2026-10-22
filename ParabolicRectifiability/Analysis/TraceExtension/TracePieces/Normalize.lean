import ParabolicRectifiability.Analysis.TraceExtension.Similarity
import ParabolicRectifiability.Analysis.TraceExtension.Cutoff

/-! # Extension from one buffered, normalized trace piece

One compact piece `F ⊆ K ∩ P̄(x₀,ρ)`, `0 < ρ ≤ 1/64`, whose points have half base density
in `K` up to radius `ρ` and trace energy `∫_0^2 γ_K(p,r)^2 dr/r ≤ B₀`, is extended as follows. With `T = similarity x₀ ρ`, the normalized source
`E' = T(K ∩ P̄(x₀,4ρ))`, the retained set `F' = T F` and the trace
`f' = ρ⁻¹ (f ∘ T⁻¹ - f(p*))`, `p* ∈ F`, satisfy the hypotheses of the buffered exterior
source (see `Cutoff`): restriction monotonicity and the exact change of
variables (see `Similarity`) give the normalized energy up to `2/ρ`.
The source extension and the compact cutoff (on `P(0,2) ⊇ F'`), taken here as
hypotheses, give `c + H`. Undoing the normalization at
the Lipschitz–Carleson level gives `c_F = f(p*) + ρ c`, `H_F = ρ H ∘ T`.

Constants: with `(c₃, C₃)` from the buffered exterior source, `C_m` from the source extension at density
`c₃`, and `C_cut`,
`C = 1 + C_cut C_m + C_cut (C_m (1 + C₃) + C_m^2)` depends only on `m`; then
`C_cut C_m ≤ C` and `C_cut (C_m (L^2 + B₀ + C₃ L^2) + C_m^2 L^2) ≤ (C (L + √B₀))^2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u

/-! ## Elementary transport and monotonicity facts -/

/-- The affine Carleson bound is monotone in its constant. -/
theorem HasAffineCarlesonBound.mono_const {E Y : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {μ : Measure (E × Time)} {f : E × Time → Y} {B B' : ℝ}
    (h : HasAffineCarlesonBound μ f B) (hB : B ≤ B') : HasAffineCarlesonBound μ f B' :=
  ⟨h.1.trans hB, fun z R hR => (h.2 z R hR).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hB (pow_nonneg hR.le _)))⟩

/-- Restriction monotonicity of the trace error: a smaller trace set has smaller error. -/
theorem traceErrorSq_mono_set {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (μ : Measure (E × Time)) {K₁ K₂ : Set (E × Time)} (h : K₁ ⊆ K₂) (f : E × Time → Y)
    (p : E × Time) (r : ℝ) : traceErrorSq μ K₁ f p r ≤ traceErrorSq μ K₂ f p r :=
  affineErrorSq_mono_measure (Measure.restrict_mono h le_rfl) f p r

/-- The scale measure `ds/s` is invariant under `s ↦ c s`, `c > 0`
(a copy of the private lemma of `Similarity`). -/
theorem scaleMeasure_map_const_mul {c : ℝ} (hc : 0 < c) :
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

/-- Change of scale `t = c s` for `ds/s` on `(0, R/c)`, valid for every function. -/
theorem setLIntegral_Ioo_scaleMeasure_comp_const_mul {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ≥0∞)
    (R : ℝ) :
    ∫⁻ s in Ioo 0 (R / c), g (c * s) ∂scaleMeasure = ∫⁻ t in Ioo 0 R, g t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  have hpre : e ⁻¹' Ioo 0 R = Ioo 0 (R / c) := by
    ext s
    rw [he]
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hc.le, (lt_div_iff₀ hc).2 (by linarith)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hc h1, by rw [lt_div_iff₀ hc] at h2; linarith⟩
  symm
  calc
    ∫⁻ t in Ioo 0 R, g t ∂scaleMeasure = ∫⁻ t in Ioo 0 R, g t ∂(Measure.map e scaleMeasure) := by
      rw [he, scaleMeasure_map_const_mul hc]
    _ = ∫⁻ t, g t ∂((scaleMeasure.restrict (e ⁻¹' Ioo 0 R)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, g (e s) ∂(scaleMeasure.restrict (e ⁻¹' Ioo 0 R)) := lintegral_map_equiv g e
    _ = ∫⁻ s in Ioo 0 (R / c), g (c * s) ∂scaleMeasure := by
      rw [hpre, he]

/-- Volumes scale under the similarity: `|A| = ρ^(m+2) |T A|` for every set `A`. -/
theorem parabolicVolume_eq_mul_image_similarity {m : ℕ} (x₀ : Space m) {ρ : ℝ} (hρ : 0 < ρ)
    (A : Set (Space m)) :
    parabolicVolume m A = ENNReal.ofReal ρ ^ (m + 2) * parabolicVolume m (similarity x₀ ρ hρ '' A) := by
  have h := setLIntegral_comp_similarity x₀ ρ hρ A (fun _ => 1)
  simp only [setLIntegral_one] at h
  exact h

/-- The real arithmetic of the piece constants. -/
theorem trace_piece_constant_le {a b c₃ l s C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc₃ : 0 ≤ c₃)
    (hl : 0 ≤ l) (hs : 0 ≤ s) (hC : 1 + a * b + a * (b * (1 + c₃) + b ^ 2) ≤ C) :
    a * (b * (l ^ 2 + (s ^ 2 + c₃ * l ^ 2)) + (b * l) ^ 2) ≤ (C * (l + s)) ^ 2 := by
  have hbK : b ≤ b * (1 + c₃) + b ^ 2 := by nlinarith [mul_nonneg hb hc₃, sq_nonneg b]
  have hX : 0 ≤ a * (b * (1 + c₃) + b ^ 2) := mul_nonneg ha (hb.trans hbK)
  have haK : a * (b * (1 + c₃) + b ^ 2) ≤ C := by nlinarith [mul_nonneg ha hb]
  have hC1 : 1 ≤ C := by nlinarith [mul_nonneg ha hb]
  have hls : 0 ≤ l ^ 2 + s ^ 2 := by positivity
  calc a * (b * (l ^ 2 + (s ^ 2 + c₃ * l ^ 2)) + (b * l) ^ 2)
      = a * (b * (1 + c₃) + b ^ 2) * l ^ 2 + a * b * s ^ 2 := by ring
    _ ≤ a * (b * (1 + c₃) + b ^ 2) * l ^ 2 + a * (b * (1 + c₃) + b ^ 2) * s ^ 2 :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbK ha) (sq_nonneg s))
    _ = a * (b * (1 + c₃) + b ^ 2) * (l ^ 2 + s ^ 2) := by ring
    _ ≤ C * (l ^ 2 + s ^ 2) := mul_le_mul_of_nonneg_right haK hls
    _ ≤ C ^ 2 * (l ^ 2 + s ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hls
        nlinarith
    _ ≤ C ^ 2 * (l + s) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        nlinarith [mul_nonneg hl hs]
    _ = (C * (l + s)) ^ 2 := by ring

end ParabolicRectifiability
