import ParabolicRectifiability.Analysis.TraceExtension.Whitney.MacroTransfer

/-! # Recentering into node Carleson control

Put `C₂ = 1 + 3D/a`, `C₃ = C₂ + D` and assume `a ≥ 2`.

* *Scale invariance.* The measure `ds/s` is invariant under `s ↦ c s`, `c > 0`, so
  `∫_{c⁻¹T} f(c s) ds/s = ∫_T f(t) dt/t` for every (not necessarily measurable) `f`.
* *Ball comparison.* If `P(y,r) ⊆ P(x,r')`, `0 < r ≤ r'`, then
  `α(y,r)^2 ≤ (r'/r)^(k+2) α(x,r')^2` for the constrained error against any measure.
* *Cells.* For `y ∈ Q_i` and `d_P(y,F₀) ≤ 2s`, `a r_i ≤ 2s` gives `r_i ≤ s`, hence
  `P(y,C₂s) ⊆ P(p_i,C₃s)` and `α(y,C₂s)^2 ≤ (C₃/C₂)^(k+2) α(p_i,C₃s)^2`. Integrating
  in `s` first and substituting `t = C₃ s` gives a scale range inside `(r_i, C₃R)`.
  The cell volume is `r_i^k`, and `p_i ∈ P(z,C₃R)` whenever the scale range is
  nonempty.
* *Retained set.* For `y ∈ F₀` substitute `t = C₂ s`; the range lies in `(0, C₃R)`.

The constants are `C = (C₃/C₂)^(k+2) ≥ 1` and `C' = C₃`. The ball `P(z,R)` is split
into `F₀` and the countably many measurable cell pieces; only countable
subadditivity of the lower integral is used, and the order of the `y` and `s`
integrals is never exchanged. No regularity of `g` is needed.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

universe u v

section ScaleInvariance

/-- The scale measure `ds/s` is invariant under multiplication by `c > 0`. -/
theorem map_const_mul_scaleMeasure {c : ℝ} (hc : 0 < c) :
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

/-- Change of scale `t = c s` for `ds/s`, valid for every function. -/
theorem setLIntegral_scaleMeasure_comp_const_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞)
    (T : Set ℝ) :
    ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure = ∫⁻ t in T, f t ∂scaleMeasure := by
  set e := MeasurableEquiv.mulLeft₀ c hc.ne' with he_def
  have he : ⇑e = fun s => c * s := MeasurableEquiv.coe_mulLeft₀ hc.ne'
  symm
  calc
    ∫⁻ t in T, f t ∂scaleMeasure = ∫⁻ t in T, f t ∂(Measure.map e scaleMeasure) := by
      rw [he, map_const_mul_scaleMeasure hc]
    _ = ∫⁻ t, f t ∂((scaleMeasure.restrict (e ⁻¹' T)).map e) := by
      rw [e.measurableEmbedding.restrict_map]
    _ = ∫⁻ s, f (e s) ∂(scaleMeasure.restrict (e ⁻¹' T)) := lintegral_map_equiv f e
    _ = ∫⁻ s in (fun s => c * s) ⁻¹' T, f (c * s) ∂scaleMeasure := by
      rw [he]

end ScaleInvariance

section BallComparison

variable {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Ball comparison for the constrained error:
`P(y,r) ⊆ P(x,r')`, `0 < r ≤ r'` give `α(y,r)^2 ≤ (r'/r)^(k+2) α(x,r')^2`. -/
theorem constrainedAffineErrorSq_le_of_ball_subset (ν : Measure (Space m))
    (g : Space m → Y) (L : ℝ≥0) {x y : Space m} {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r')
    (hsub : Metric.ball y r ⊆ Metric.ball x r') :
    constrainedAffineErrorSq ν g L y r ≤
      ENNReal.ofReal ((r' / r) ^ (m + 4)) * constrainedAffineErrorSq ν g L x r' := by
  have hr' : 0 < r' := hr.trans_le hrr
  have hC : 0 < r' / r := div_pos hr' hr
  simp only [constrainedAffineErrorSq, hr, hr', ↓reduceIte]
  rw [baseDimension_spatial_add_two, ← mul_assoc]
  have hT : ENNReal.ofReal ((r' / r) ^ (m + 4)) * (ENNReal.ofReal r')⁻¹ ^ (m + 4) =
      (ENNReal.ofReal r)⁻¹ ^ (m + 4) := by
    have h := ofReal_pow_mul_inv_ofReal_mul_pow (s := r) hC (m + 4)
    rwa [div_mul_cancel₀ r' hr.ne'] at h
  rw [hT]
  refine mul_le_mul_right ?_ _
  refine iInf_mono fun c => iInf_mono fun B => iInf_mono fun _ => ?_
  unfold affineFitIntegral
  exact lintegral_mono_set hsub

end BallComparison

section Recentering

variable {m : ℕ} {ι : Type*} [Countable ι] {F₀ : Set (Space m)} {D a : ℝ}
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The recentering estimate with the explicit constants `C = (C₃/C₂)^(k+2)` and
`C' = C₃`, `C₂ = 1 + 3D/a`, `C₃ = C₂ + D`. -/
theorem WhitneyData.recentering_le (W : WhitneyData m ι F₀ D a) (hF₀ : IsClosed F₀)
    (ha : 2 ≤ a) (g : Space m → Y) (L : ℝ≥0) (z : Space m) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
        constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s)
          ∂scaleMeasure ∂parabolicVolume m ≤
      ENNReal.ofReal (((1 + 3 * D / a + D) / (1 + 3 * D / a)) ^ (m + 4)) *
        W.nodeCarlesonIntegral g L z ((1 + 3 * D / a + D) * R) := by
  have ha0 : 0 < a := by linarith
  have hD : 1 ≤ D := W.one_le_D
  obtain ⟨C₂, hC₂d⟩ : ∃ x : ℝ, x = 1 + 3 * D / a := ⟨_, rfl⟩
  rw [← hC₂d]
  obtain ⟨C₃, hC₃d⟩ : ∃ x : ℝ, x = C₂ + D := ⟨_, rfl⟩
  rw [← hC₃d]
  have h3D : 0 ≤ 3 * D / a := div_nonneg (by linarith) ha0.le
  have hC₂1 : 1 ≤ C₂ := by rw [hC₂d]; linarith
  have hC₂0 : 0 < C₂ := by linarith
  have hC₃C₂ : C₂ ≤ C₃ := by rw [hC₃d]; linarith
  have hC₃1 : 1 < C₃ := by rw [hC₃d]; linarith
  have hC₃0 : 0 < C₃ := by linarith
  have hC₃R : R ≤ C₃ * R := le_mul_of_one_le_left hR.le hC₃1.le
  have hDR : (1 + D) * R ≤ C₃ * R := mul_le_mul_of_nonneg_right (by rw [hC₃d]; linarith) hR.le
  obtain ⟨C, hCd⟩ : ∃ x : ℝ, x = (C₃ / C₂) ^ (m + 4) := ⟨_, rfl⟩
  rw [← hCd]
  have hC1 : 1 ≤ C := by
    rw [hCd]
    exact one_le_pow₀ ((one_le_div₀ hC₂0).mpr hC₃C₂)
  have hS : ∀ y : Space m, MeasurableSet (Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}) :=
    fun _ => measurableSet_Ioo.inter (measurableSet_le measurable_const
      (measurable_const.mul measurable_id))
  rw [WhitneyData.nodeCarlesonIntegral]
  -- decomposition of the ball
  have hcover : Metric.ball z R ⊆ (Metric.ball z R ∩ F₀) ∪ ⋃ i, Metric.ball z R ∩ W.cell i := by
    intro y hy
    by_cases hyF : y ∈ F₀
    · exact Or.inl ⟨hy, hyF⟩
    · obtain ⟨i, hi⟩ := W.exists_mem_cell hyF
      exact Or.inr (mem_iUnion.mpr ⟨i, hy, hi⟩)
  -- the retained part
  have hF0 : ∫⁻ y in Metric.ball z R ∩ F₀, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
        constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure ∂parabolicVolume m ≤
      ENNReal.ofReal C * ∫⁻ p in F₀ ∩ Metric.ball z (C₃ * R), ∫⁻ t in Ioo 0 (C₃ * R),
        constrainedAffineErrorSq W.nodeMeasure g L p t ∂scaleMeasure ∂parabolicVolume m := by
    have hpt : ∀ y : Space m, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
        constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure ≤
        ENNReal.ofReal C * ∫⁻ t in Ioo 0 (C₃ * R),
          constrainedAffineErrorSq W.nodeMeasure g L y t ∂scaleMeasure := by
      intro y
      have hsub : Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s} ⊆
          (fun s => C₂ * s) ⁻¹' Ioo 0 (C₃ * R) := fun s hs => by
        have h1 : 0 < s := hs.1.1
        have h2 : s < R := hs.1.2
        refine ⟨mul_pos hC₂0 h1, ?_⟩
        calc
          C₂ * s < C₂ * R := mul_lt_mul_of_pos_left h2 hC₂0
          _ ≤ C₃ * R := mul_le_mul_of_nonneg_right hC₃C₂ hR.le
      calc
        _ ≤ ∫⁻ s in (fun s => C₂ * s) ⁻¹' Ioo 0 (C₃ * R),
            constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure :=
          lintegral_mono_set hsub
        _ = ∫⁻ t in Ioo 0 (C₃ * R), constrainedAffineErrorSq W.nodeMeasure g L y t
              ∂scaleMeasure :=
          setLIntegral_scaleMeasure_comp_const_mul hC₂0
            (fun t => constrainedAffineErrorSq W.nodeMeasure g L y t) _
        _ ≤ _ := le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.mpr hC1)
    calc
      _ ≤ ∫⁻ y in Metric.ball z R ∩ F₀, ENNReal.ofReal C * ∫⁻ t in Ioo 0 (C₃ * R),
            constrainedAffineErrorSq W.nodeMeasure g L y t ∂scaleMeasure ∂parabolicVolume m :=
        setLIntegral_mono' (measurableSet_ball.inter hF₀.measurableSet) fun y _ => hpt y
      _ ≤ ∫⁻ y in F₀ ∩ Metric.ball z (C₃ * R), ENNReal.ofReal C * ∫⁻ t in Ioo 0 (C₃ * R),
            constrainedAffineErrorSq W.nodeMeasure g L y t ∂scaleMeasure ∂parabolicVolume m :=
        lintegral_mono_set fun y hy => ⟨hy.2, Metric.ball_subset_ball hC₃R hy.1⟩
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- the cell pieces
  have hcell : ∀ i, ∫⁻ y in Metric.ball z R ∩ W.cell i,
        ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
          constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure
            ∂parabolicVolume m ≤
      ENNReal.ofReal C * ((Metric.ball z (C₃ * R)).indicator
        (fun _ => ENNReal.ofReal (W.radius i ^ (m + 2))) (W.center i) *
          ∫⁻ t in Ioo (W.radius i) (C₃ * R),
            constrainedAffineErrorSq W.nodeMeasure g L (W.center i) t ∂scaleMeasure) := by
    intro i
    have hri := W.radius_pos i
    -- scales in range satisfy `r_i ≤ s`
    have hscale : ∀ y ∈ W.cell i, ∀ s ∈ Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
        W.radius i ≤ s := by
      intro y hy s hs
      have h1 : a * W.radius i ≤ Metric.infDist y F₀ := W.le_infDist i y hy
      have h2 : Metric.infDist y F₀ ≤ 2 * s := hs.2
      have h3 : 2 * W.radius i ≤ a * W.radius i := mul_le_mul_of_nonneg_right ha hri.le
      linarith
    have hpt : ∀ y ∈ Metric.ball z R ∩ W.cell i,
        ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
          constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure ≤
        (Metric.ball z (C₃ * R)).indicator (fun _ => ENNReal.ofReal C *
          ∫⁻ t in Ioo (W.radius i) (C₃ * R),
            constrainedAffineErrorSq W.nodeMeasure g L (W.center i) t ∂scaleMeasure)
          (W.center i) := by
      intro y hy
      have hyc : dist y (W.center i) ≤ D * W.radius i := W.dist_center_le hy.2
      by_cases hp : W.center i ∈ Metric.ball z (C₃ * R)
      · rw [indicator_of_mem hp]
        have hrec : ∀ s ∈ Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
            constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ≤
              ENNReal.ofReal C * constrainedAffineErrorSq W.nodeMeasure g L (W.center i)
                (C₃ * s) := by
          intro s hs
          have hs0 : 0 < s := hs.1.1
          have hrs := hscale y hy.2 s hs
          have hsub : Metric.ball y (C₂ * s) ⊆ Metric.ball (W.center i) (C₃ * s) := by
            intro q hq
            rw [Metric.mem_ball] at hq ⊢
            have hDs : D * W.radius i ≤ D * s := mul_le_mul_of_nonneg_left hrs (by linarith)
            calc
              dist q (W.center i) ≤ dist q y + dist y (W.center i) := dist_triangle _ _ _
              _ < C₂ * s + D * s := by linarith
              _ = C₃ * s := by rw [hC₃d]; ring
          have h := constrainedAffineErrorSq_le_of_ball_subset W.nodeMeasure g L
            (mul_pos hC₂0 hs0) (mul_le_mul_of_nonneg_right hC₃C₂ hs0.le) hsub
          rwa [mul_div_mul_right C₃ C₂ hs0.ne', ← hCd] at h
        have hsub : Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s} ⊆
            (fun s => C₃ * s) ⁻¹' Ioo (W.radius i) (C₃ * R) := fun s hs => by
          have h1 : 0 < s := hs.1.1
          have h2 : s < R := hs.1.2
          have hrs := hscale y hy.2 s hs
          refine ⟨?_, mul_lt_mul_of_pos_left h2 hC₃0⟩
          calc
            W.radius i ≤ s := hrs
            _ < C₃ * s := lt_mul_of_one_lt_left h1 hC₃1
        calc
          _ ≤ ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}, ENNReal.ofReal C *
                constrainedAffineErrorSq W.nodeMeasure g L (W.center i) (C₃ * s)
                  ∂scaleMeasure :=
            setLIntegral_mono' (hS y) hrec
          _ ≤ ∫⁻ s in (fun s => C₃ * s) ⁻¹' Ioo (W.radius i) (C₃ * R), ENNReal.ofReal C *
                constrainedAffineErrorSq W.nodeMeasure g L (W.center i) (C₃ * s)
                  ∂scaleMeasure :=
            lintegral_mono_set hsub
          _ = ENNReal.ofReal C * ∫⁻ s in (fun s => C₃ * s) ⁻¹' Ioo (W.radius i) (C₃ * R),
                constrainedAffineErrorSq W.nodeMeasure g L (W.center i) (C₃ * s)
                  ∂scaleMeasure :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ = _ := by
            rw [setLIntegral_scaleMeasure_comp_const_mul hC₃0
              (fun t => constrainedAffineErrorSq W.nodeMeasure g L (W.center i) t)]
      · rw [indicator_of_notMem hp]
        have hempty : Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s} = ∅ := by
          refine eq_empty_of_forall_notMem fun s hs => hp ?_
          have h2 : s < R := hs.1.2
          have hrs := hscale y hy.2 s hs
          have hyz : dist y z < R := Metric.mem_ball.mp hy.1
          have hDr : D * W.radius i ≤ D * R :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
          rw [Metric.mem_ball]
          calc
            dist (W.center i) z ≤ dist (W.center i) y + dist y z := dist_triangle _ _ _
            _ < D * R + R := by rw [dist_comm]; linarith
            _ = (1 + D) * R := by ring
            _ ≤ C₃ * R := hDR
        rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    calc
      _ ≤ ∫⁻ _ in Metric.ball z R ∩ W.cell i, (Metric.ball z (C₃ * R)).indicator
            (fun _ => ENNReal.ofReal C * ∫⁻ t in Ioo (W.radius i) (C₃ * R),
              constrainedAffineErrorSq W.nodeMeasure g L (W.center i) t ∂scaleMeasure)
            (W.center i) ∂parabolicVolume m :=
        setLIntegral_mono' (measurableSet_ball.inter (W.measurableSet_cell i)) hpt
      _ = (Metric.ball z (C₃ * R)).indicator
            (fun _ => ENNReal.ofReal C * ∫⁻ t in Ioo (W.radius i) (C₃ * R),
              constrainedAffineErrorSq W.nodeMeasure g L (W.center i) t ∂scaleMeasure)
            (W.center i) * parabolicVolume m (Metric.ball z R ∩ W.cell i) :=
        setLIntegral_const _ _
      _ ≤ (Metric.ball z (C₃ * R)).indicator
            (fun _ => ENNReal.ofReal C * ∫⁻ t in Ioo (W.radius i) (C₃ * R),
              constrainedAffineErrorSq W.nodeMeasure g L (W.center i) t ∂scaleMeasure)
            (W.center i) * parabolicVolume m (W.cell i) :=
        mul_le_mul_right (measure_mono inter_subset_right) _
      _ = _ := by
        rw [W.volume_cell i]
        by_cases hp : W.center i ∈ Metric.ball z (C₃ * R)
        · rw [indicator_of_mem hp, indicator_of_mem hp]
          ring
        · rw [indicator_of_notMem hp, indicator_of_notMem hp, zero_mul, zero_mul, mul_zero]
  calc
    _ ≤ ∫⁻ y in (Metric.ball z R ∩ F₀) ∪ ⋃ i, Metric.ball z R ∩ W.cell i,
          ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
            constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure
              ∂parabolicVolume m :=
      lintegral_mono_set hcover
    _ ≤ (∫⁻ y in Metric.ball z R ∩ F₀, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
            constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure
              ∂parabolicVolume m) +
          ∑' i, ∫⁻ y in Metric.ball z R ∩ W.cell i,
            ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
              constrainedAffineErrorSq W.nodeMeasure g L y (C₂ * s) ∂scaleMeasure
                ∂parabolicVolume m :=
      (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_iUnion_le _ _))
    _ ≤ ENNReal.ofReal C * (∫⁻ p in F₀ ∩ Metric.ball z (C₃ * R), ∫⁻ t in Ioo 0 (C₃ * R),
            constrainedAffineErrorSq W.nodeMeasure g L p t ∂scaleMeasure ∂parabolicVolume m) +
          ∑' i, ENNReal.ofReal C * ((Metric.ball z (C₃ * R)).indicator
            (fun _ => ENNReal.ofReal (W.radius i ^ (m + 2))) (W.center i) *
              ∫⁻ t in Ioo (W.radius i) (C₃ * R),
                constrainedAffineErrorSq W.nodeMeasure g L (W.center i) t ∂scaleMeasure) :=
      add_le_add hF0 (ENNReal.tsum_le_tsum hcell)
    _ = _ := by rw [ENNReal.tsum_mul_left, ← mul_add]

end Recentering

/-- **Recentering into node Carleson control**, with
`C = (C₃/C₂)^(k+2)`, `C' = C₃`, `C₂ = 1 + 3D/a`, `C₃ = C₂ + D`. -/
theorem whitney_recentering_le_proof (m : ℕ) (D a : ℝ) (ha : 2 ≤ a) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 1 ≤ C' ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ →
      ∀ {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (g : Space m → Y)
        (L : ℝ≥0) (z : Space m) (R : ℝ), 0 < R →
        ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
            constrainedAffineErrorSq W.nodeMeasure g L y ((1 + 3 * D / a) * s)
              ∂scaleMeasure ∂parabolicVolume m ≤
          ENNReal.ofReal C * W.nodeCarlesonIntegral g L z (C' * R) := by
  by_cases hD : 1 ≤ D
  · have ha0 : 0 < a := by linarith
    have h3D : 0 ≤ 3 * D / a := div_nonneg (by linarith) ha0.le
    refine ⟨((1 + 3 * D / a + D) / (1 + 3 * D / a)) ^ (m + 4), 1 + 3 * D / a + D,
      pow_nonneg (div_nonneg (by linarith) (by linarith)) _, by linarith, ?_⟩
    intro ι _ F₀ W hF₀ Y _ _ g L z R hR
    exact W.recentering_le hF₀ ha g L z hR
  · exact ⟨0, 1, le_rfl, le_rfl, fun W _ => absurd W.one_le_D hD⟩

end ParabolicRectifiability
