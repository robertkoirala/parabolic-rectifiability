import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound

/-! # The main term of the transfer bound

We prove `d2_main_term_proof : MainTermStatement`, the statement type.

**Proof idea.** Fix `w ∈ Γ ∩ P(c,ρ)`. For `z ∈ P(c,ρ)`, `d(z,Γ) ≤ d(z,w) < 2ρ`, so
`κ_z`-a.e. transported centre lies in `P(c,(1+2C_disp)ρ)`. For each `z`, Tonelli in `(r,v)` and
the dilation invariance of `dr/r` turn the inner integral into `∫ S^{Λρ}_σ dκ_z`, restricted to
`P(c,(1+2C_disp)ρ)`. The outer integral is `∫ … d((μ⌊P(c,ρ)).bind κ)`, and
`(μ⌊P(c,ρ)).bind κ ≤ (μ⌊P(c,2ρ)).bind κ ≤ D₀ σ` (the second `D₀`). With
`M = max(2+2C_disp, Λ)`, `P(c,(1+2C_disp)ρ) ⊆ P(w,Mρ)`, `S^{Λρ} ≤ S^{Mρ}`, and the root
supremum at `(w, Mρ)` gives `∫_{P(w,Mρ)} S^{Mρ}_σ dσ ≤ C_ref (Mρ)^k`. Hence
`Cm = D₀ C_ref M^k`.

Only the outer inequality `∫_{μ⊗ν} ≤ ∫∫` (`lintegral_prod_le`) is used, so no measurability of
the kernel average on the product is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

open ParabolicRectifiability.Foundations

/-- The scale measure `ds/s` is invariant under `s ↦ c s`, `c > 0` (a copy of the base lemma
`map_const_mul_scaleMeasure`, kept local to
avoid importing the trace-extension chain). -/
theorem d2main_map_const_mul_scaleMeasure {c : ℝ} (hc : 0 < c) :
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

/-- Dilation of `dr/r` on `(0,ρ)`: `∫_0^ρ g(c s) ds/s = ∫_0^{cρ} g(t) dt/t`, `c > 0`, for every
function `g`. -/
theorem d2main_setLIntegral_Ioo_comp_const_mul {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ≥0∞) (ρ : ℝ) :
    ∫⁻ s in Ioo 0 ρ, g (c * s) ∂scaleMeasure = ∫⁻ t in Ioo 0 (c * ρ), g t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  have hpre : e ⁻¹' Ioo 0 (c * ρ) = Ioo 0 ρ := by
    ext s
    rw [he]
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hc.le, lt_of_mul_lt_mul_left h2 hc.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hc h1, mul_lt_mul_of_pos_left h2 hc⟩
  symm
  calc
    ∫⁻ t in Ioo 0 (c * ρ), g t ∂scaleMeasure
        = ∫⁻ t in Ioo 0 (c * ρ), g t ∂(Measure.map e scaleMeasure) := by
      rw [he, d2main_map_const_mul_scaleMeasure hc]
    _ = ∫⁻ t, g t ∂((scaleMeasure.restrict (e ⁻¹' Ioo 0 (c * ρ))).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, g (e s) ∂(scaleMeasure.restrict (e ⁻¹' Ioo 0 (c * ρ))) := lintegral_map_equiv g e
    _ = ∫⁻ s in Ioo 0 ρ, g (c * s) ∂scaleMeasure := by
      rw [hpre, he]

/-- Transported centres stay near the model ball: if `w ∈ Γ ∩ P(c,ρ)`, `z ∈ P(c,ρ)`,
`0 ≤ C_disp` and `d(z,v) ≤ C_disp d(z,Γ)`, then `v ∈ P(c,(1+2C_disp)ρ)`. -/
theorem d2main_mem_ball_of_displacement {n : ℕ} {Γ : Set (Space n)} {c w z v : Space n}
    {ρ Cdisp : ℝ} (hCdisp : 0 ≤ Cdisp) (hwΓ : w ∈ Γ) (hw : w ∈ Metric.ball c ρ)
    (hz : z ∈ Metric.ball c ρ) (hv : dist z v ≤ Cdisp * Metric.infDist z Γ) :
    v ∈ Metric.ball c ((1 + 2 * Cdisp) * ρ) := by
  rw [Metric.mem_ball] at hw hz ⊢
  have h1 : Metric.infDist z Γ ≤ dist z w := Metric.infDist_le_dist_of_mem hwΓ
  have h2 : dist z w ≤ dist z c + dist w c := dist_triangle_right z w c
  have h3 : dist v c ≤ dist z v + dist z c := by
    rw [dist_comm z v]
    exact dist_triangle v z c
  have h4 : Cdisp * Metric.infDist z Γ ≤ Cdisp * (2 * ρ) :=
    mul_le_mul_of_nonneg_left (by linarith) hCdisp
  have h5 : (1 + 2 * Cdisp) * ρ = ρ + Cdisp * (2 * ρ) := by ring
  rw [h5]
  linarith

/-- The enlarged ball recentred at a reference point: `P(c,(1+2C_disp)ρ) ⊆ P(w,Mρ)` for
`w ∈ P(c,ρ)` and `2 + 2C_disp ≤ M`. -/
theorem d2main_ball_subset {n : ℕ} {c w : Space n} {ρ Cdisp M : ℝ}
    (hw : w ∈ Metric.ball c ρ) (hM : 2 + 2 * Cdisp ≤ M) (hρ : 0 < ρ) :
    Metric.ball c ((1 + 2 * Cdisp) * ρ) ⊆ Metric.ball w (M * ρ) := by
  intro v hv
  rw [Metric.mem_ball] at hw hv ⊢
  have h1 : dist v w ≤ dist v c + dist w c := dist_triangle_right v w c
  have h2 : (2 + 2 * Cdisp) * ρ ≤ M * ρ := mul_le_mul_of_nonneg_right hM hρ.le
  have h3 : (2 + 2 * Cdisp) * ρ = (1 + 2 * Cdisp) * ρ + ρ := by ring
  linarith

/-- The root supremum at one centre and radius: for `a ∈ S` and `R > 0`,
`∫_{P(a,R)} f(R,·) dσ ≤ R^k · sup`. -/
theorem d2main_le_of_rootCarlesonSup {n : ℕ} {S : Set (Space n)} {σ : Measure (Space n)}
    {k : ℕ} {f : ℝ → Space n → ℝ≥0∞} {C : ℝ≥0∞} (hsup : rootCarlesonSup S σ k f ≤ C)
    {a : Space n} (ha : a ∈ S) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in Metric.ball a R, f R z ∂σ ≤ ENNReal.ofReal R ^ k * C := by
  have h1 : (ENNReal.ofReal R)⁻¹ ^ k * ∫⁻ z in Metric.ball a R, f R z ∂σ ≤
      rootCarlesonSup S σ k f := by
    unfold rootCarlesonSup
    exact le_iSup₂_of_le a ha (le_iSup₂_of_le R hR le_rfl)
  have h2 := h1.trans hsup
  rw [← ENNReal.inv_pow] at h2
  have hne0 : ENNReal.ofReal R ^ k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hR).ne'
  have hnetop : ENNReal.ofReal R ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.inv_mul_le_iff hne0 hnetop).1 h2

/-- **The main term** of  (`MainTermStatement`, the type of the statement
`d2_main_term`), with `Cm = D₀ C_ref max(2 + 2C_disp, Λ)^k`. -/
theorem d2_main_term_proof : MainTermStatement := by
  intro n _hn k _hk _hkn Cdisp D₀ Λ Cref hCdisp hD₀ hΛ hCref
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max (2 + 2 * Cdisp) Λ := ⟨_, rfl⟩
  have hΛM : Λ ≤ M := by rw [hMdef]; exact le_max_right _ _
  have h2M : 2 + 2 * Cdisp ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hM0 : 0 < M := lt_of_lt_of_le hΛ0 hΛM
  refine ⟨D₀ * Cref * M ^ k, mul_pos (mul_pos hD₀ hCref) (pow_pos hM0 k), ?_⟩
  intro μ hμf _hμr T Γ σ hσf hroot κ hκ hdisp c ρ hρ hmeet hbind
  have : SigmaFinite μ := source_sigmaFinite μ
  obtain ⟨w, hwB, hwΓ⟩ := hmeet
  have hMρ : 0 < M * ρ := mul_pos hM0 hρ
  have hSmeas : Measurable ((Metric.ball c ((1 + 2 * Cdisp) * ρ)).indicator
      (squareEnergy σ k T (Λ * ρ))) :=
    (measurable_squareEnergy σ k T (Λ * ρ)).indicator measurableSet_ball
  -- Step 1: for a fixed testing centre `z ∈ P(c,ρ)`: Tonelli in `(r,v)`, dilation of `dr/r`,
  -- and the displacement bound.
  have hinner : ∀ z ∈ Metric.ball c ρ,
      ∫⁻ r, ∫⁻ v, betaSq σ k T v (Λ * r) ∂(κ z) ∂(scaleMeasure.restrict (Ioo 0 ρ)) ≤
        ∫⁻ v, (Metric.ball c ((1 + 2 * Cdisp) * ρ)).indicator
          (squareEnergy σ k T (Λ * ρ)) v ∂(κ z) := by
    intro z hz
    have hswap : ∫⁻ r, ∫⁻ v, betaSq σ k T v (Λ * r) ∂(κ z) ∂(scaleMeasure.restrict (Ioo 0 ρ)) =
        ∫⁻ v, ∫⁻ r in Ioo 0 ρ, betaSq σ k T v (Λ * r) ∂scaleMeasure ∂(κ z) := by
      refine lintegral_lintegral_swap ?_
      exact ((measurable_betaSq σ k T).comp
        (measurable_snd.prodMk (measurable_fst.const_mul Λ))).aemeasurable
    have hdil : ∀ v, ∫⁻ r in Ioo 0 ρ, betaSq σ k T v (Λ * r) ∂scaleMeasure =
        squareEnergy σ k T (Λ * ρ) v := fun v =>
      d2main_setLIntegral_Ioo_comp_const_mul hΛ0 (fun t => betaSq σ k T v t) ρ
    rw [hswap, lintegral_congr hdil]
    refine le_of_eq (lintegral_congr_ae ?_)
    filter_upwards [hdisp z] with v hv
    rw [indicator_of_mem
      (d2main_mem_ball_of_displacement (by linarith) hwΓ hwB hz hv)]
  -- Step 2: integrate the testing centres; the second factor `D₀`; recentre.
  have hsub : Metric.ball c ρ ⊆ Metric.ball c (2 * ρ) :=
    Metric.ball_subset_ball (by linarith)
  have hSmono : ∀ v, squareEnergy σ k T (Λ * ρ) v ≤ squareEnergy σ k T (M * ρ) v := by
    intro v
    unfold squareEnergy
    exact lintegral_mono_set (Ioo_subset_Ioo_right (mul_le_mul_of_nonneg_right hΛM hρ.le))
  have hrec : ∫⁻ v in Metric.ball c ((1 + 2 * Cdisp) * ρ), squareEnergy σ k T (Λ * ρ) v ∂σ ≤
      ENNReal.ofReal (M * ρ) ^ k * ENNReal.ofReal Cref :=
    calc
      ∫⁻ v in Metric.ball c ((1 + 2 * Cdisp) * ρ), squareEnergy σ k T (Λ * ρ) v ∂σ
          ≤ ∫⁻ v in Metric.ball c ((1 + 2 * Cdisp) * ρ), squareEnergy σ k T (M * ρ) v ∂σ :=
        setLIntegral_mono' measurableSet_ball fun v _ => hSmono v
      _ ≤ ∫⁻ v in Metric.ball w (M * ρ), squareEnergy σ k T (M * ρ) v ∂σ :=
        lintegral_mono_set (d2main_ball_subset hwB h2M hρ)
      _ ≤ ENNReal.ofReal (M * ρ) ^ k * ENNReal.ofReal Cref :=
        d2main_le_of_rootCarlesonSup (f := fun R z => squareEnergy σ k T R z) hroot hwΓ hMρ
  calc
    ∫⁻ p in Metric.ball c ρ ×ˢ Ioo 0 ρ, ∫⁻ v, betaSq σ k T v (Λ * p.2) ∂(κ p.1)
        ∂(pointScaleMeasure μ)
        = ∫⁻ p, ∫⁻ v, betaSq σ k T v (Λ * p.2) ∂(κ p.1)
            ∂((μ.restrict (Metric.ball c ρ)).prod (scaleMeasure.restrict (Ioo 0 ρ))) := by
      rw [pointScaleMeasure, Measure.prod_restrict]
    _ ≤ ∫⁻ z, ∫⁻ r, ∫⁻ v, betaSq σ k T v (Λ * r) ∂(κ z) ∂(scaleMeasure.restrict (Ioo 0 ρ))
          ∂(μ.restrict (Metric.ball c ρ)) :=
      lintegral_prod_le _
    _ ≤ ∫⁻ z in Metric.ball c ρ, ∫⁻ v, (Metric.ball c ((1 + 2 * Cdisp) * ρ)).indicator
          (squareEnergy σ k T (Λ * ρ)) v ∂(κ z) ∂μ :=
      setLIntegral_mono' measurableSet_ball hinner
    _ ≤ ∫⁻ z in Metric.ball c (2 * ρ), ∫⁻ v, (Metric.ball c ((1 + 2 * Cdisp) * ρ)).indicator
          (squareEnergy σ k T (Λ * ρ)) v ∂(κ z) ∂μ :=
      lintegral_mono_set hsub
    _ = ∫⁻ v, (Metric.ball c ((1 + 2 * Cdisp) * ρ)).indicator (squareEnergy σ k T (Λ * ρ)) v
          ∂((μ.restrict (Metric.ball c (2 * ρ))).bind κ) :=
      (Measure.lintegral_bind κ.measurable.aemeasurable hSmeas.aemeasurable).symm
    _ ≤ ∫⁻ v, (Metric.ball c ((1 + 2 * Cdisp) * ρ)).indicator (squareEnergy σ k T (Λ * ρ)) v
          ∂(ENNReal.ofReal D₀ • σ) :=
      lintegral_mono' hbind le_rfl
    _ = ENNReal.ofReal D₀ *
          ∫⁻ v in Metric.ball c ((1 + 2 * Cdisp) * ρ), squareEnergy σ k T (Λ * ρ) v ∂σ := by
      rw [lintegral_smul_measure, lintegral_indicator measurableSet_ball, smul_eq_mul]
    _ ≤ ENNReal.ofReal D₀ * (ENNReal.ofReal (M * ρ) ^ k * ENNReal.ofReal Cref) :=
      mul_le_mul' le_rfl hrec
    _ = ENNReal.ofReal (D₀ * Cref * M ^ k * ρ ^ k) := by
      rw [← ENNReal.ofReal_pow hMρ.le, ← ENNReal.ofReal_mul (pow_nonneg hMρ.le k),
        ← ENNReal.ofReal_mul hD₀.le, mul_pow]
      congr 1
      ring

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
