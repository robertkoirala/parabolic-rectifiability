import ParabolicRectifiability.Analysis.TraceExtension.Cutoff
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! # The affine Carleson bound of a compact cutoff

* `cutoff_affineCarleson_proof`: for a cutoff `χ`
  with parabolic `C^{2,1}` bounds `K` at scale `R₀` and values in `[0,1]`, supported in
  `P(z₀,4R₀)`, the function `H = χ (F - F(z₀))` has affine Carleson constant at most
  `C (B + L^2)`.
* `exists_compact_cutoff_affineCarleson_proof`: the cutoff lemma, with `c = F(z₀)` and
  `H = χ (F - c)`, combining `exists_parabolic_cutoff`, `cutoff_lipschitz` and the bound
  above.

Proof of the Carleson bound. Write `y = (u_y, t_y)`, `D = ∇_u χ(·, t_y)(u_y)` and
`ρ(q) = χ(q) - χ(y) - D(u - u_y)`; the `C^{2,1}` bounds give
`|ρ(q)| ≤ K R₀^{-2} (|u - u_y|^2 + |t - t_y|)`. For every spatial affine map `A` the map
`A_H = χ(y) (A - c) + D(· - u_y) (F(y) - c)` is again spatial affine, and
`H - A_H = χ(y) (F - A) + D(u - u_y) (F - F(y)) + ρ (F - c)`.
On a ball `P(y,s)`, `s ≤ R₀`, that meets the support, `|F - c| ≤ 6 L R₀`, so
`|H - A_H| ≤ |F - A| + 13 K L s^2/R₀`. Hence, for every competitor `A`, the fit of `H`
is at most twice that of `F` plus `338 K^2 L^2 |P(y,s)| s^4 / R₀^2`; taking the infimum,
`κ_H(y,s)^2 ≤ 2 κ_F(y,s)^2 + 338 v K^2 L^2 (s/R₀)^2`. No best fit is used, so the values
may lie in an incomplete inner-product space. For `s ≥ R₀` the zero comparison and `|H| ≤ 4 L R₀` on `P(z₀,4R₀)` give
`κ_H(y,s)^2 ≤ 16 v 4^k L^2 R₀^2 s^{-2}`. The resulting scale bound depends on `s` only and
has `dr/r`-integral at most `(338 v K^2 + 8 v 4^k) L^2`; integrating over the testing ball
gives the Carleson bound with `C = 2 + (338 v K^2 + 8 v 4^k) v`, `v = 2 ω_m`, `k = m + 2`.
Only the pointwise comparison and the explicit measurable scale bound are integrated, so no
measurability of the affine errors is needed.

The section `Completion` proves the completion invariance of the affine fitting infimum
(replacing the values by their completion does not change it) when the testing ball is a
measurable set, in particular for a Borel spatial factor. For an arbitrary measurable
structure on `E` this invariance can fail; the cutoff proof above does not use it.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace CutoffCarleson

/-! ## Elementary comparison of fitting integrals -/

/-- `(x + d)^2 ≤ (1 + η) x^2 + (1 + η⁻¹) d^2` for `η > 0`. -/
theorem sq_add_le_of_pos (x d : ℝ) {η : ℝ} (hη : 0 < η) :
    (x + d) ^ 2 ≤ (1 + η) * x ^ 2 + (1 + η⁻¹) * d ^ 2 := by
  have h : (1 + η) * x ^ 2 + (1 + η⁻¹) * d ^ 2 = (x + d) ^ 2 + (η * x - d) ^ 2 / η := by
    field_simp
    ring
  rw [h]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hη.le)

theorem enorm_sq_le_of_norm_le_add {Y Z : Type*} [SeminormedAddCommGroup Y]
    [SeminormedAddCommGroup Z] {v : Y} {w : Z} {d η : ℝ} (hη : 0 < η)
    (h : ‖v‖ ≤ ‖w‖ + d) :
    ‖v‖ₑ ^ 2 ≤ ENNReal.ofReal (1 + η) * ‖w‖ₑ ^ 2 + ENNReal.ofReal ((1 + η⁻¹) * d ^ 2) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg (by have := inv_pos.2 hη; linarith) (sq_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖v‖ ^ 2 ≤ (‖w‖ + d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ _ := sq_add_le_of_pos _ _ hη

/-- A pointwise comparison of two affine residuals on a measurable ball compares their
fitting integrals; no measurability of the functions is needed. -/
theorem affineFitIntegral_le_of_norm_le {E Y Z : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] {μ : Measure (E × Time)}
    {f : E × Time → Y} {g : E × Time → Z} {a : Y} {B : E →L[ℝ] Y} {a' : Z} {B' : E →L[ℝ] Z}
    {y : E × Time} {s d η : ℝ} (hball : MeasurableSet (Metric.ball y s)) (hη : 0 < η) (h : ∀ q ∈ Metric.ball y s, ‖f q - (a + B q.1)‖ ≤ ‖g q - (a' + B' q.1)‖ + d) :
    affineFitIntegral μ f a B y s ≤
      ENNReal.ofReal (1 + η) * affineFitIntegral μ g a' B' y s +
        ENNReal.ofReal ((1 + η⁻¹) * d ^ 2) * μ (Metric.ball y s) := by
  unfold affineFitIntegral
  calc ∫⁻ q in Metric.ball y s, ‖f q - (a + B q.1)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ q in Metric.ball y s, (ENNReal.ofReal (1 + η) * ‖g q - (a' + B' q.1)‖ₑ ^ 2 +
          ENNReal.ofReal ((1 + η⁻¹) * d ^ 2)) ∂μ :=
        setLIntegral_mono' hball fun q hq => enorm_sq_le_of_norm_le_add hη (h q hq)
    _ = ENNReal.ofReal (1 + η) * ∫⁻ q in Metric.ball y s, ‖g q - (a' + B' q.1)‖ₑ ^ 2 ∂μ +
          ENNReal.ofReal ((1 + η⁻¹) * d ^ 2) * μ (Metric.ball y s) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]

/-! ## Completion invariance of the fitting infimum -/

section Completion

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Affine coefficients in the completion are approximated by coefficients in `Y`, the
linear part uniformly on the unit ball (finitely many basis values). -/
theorem exists_approx_coeff (ah : UniformSpace.Completion Y)
    (Bh : E →L[ℝ] UniformSpace.Completion Y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : Y) (B : E →L[ℝ] Y), ‖ah - (a : UniformSpace.Completion Y)‖ ≤ δ ∧
      ∀ u : E, ‖Bh u - (B u : UniformSpace.Completion Y)‖ ≤ δ * ‖u‖ := by
  obtain ⟨a, ha⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt ah hδ
  let v := Module.finBasis ℝ E
  obtain ⟨C, hC, hCv⟩ := v.exists_opNorm_le (F := UniformSpace.Completion Y)
  have hδC : 0 < δ / C := div_pos hδ hC
  choose b hb using fun i => UniformSpace.Completion.denseRange_coe.exists_dist_lt (Bh (v i)) hδC
  refine ⟨a, v.constrL b, by rw [← dist_eq_norm]; exact ha.le, fun u => ?_⟩
  set U : E →L[ℝ] UniformSpace.Completion Y :=
    Bh - (UniformSpace.Completion.toComplL : Y →L[ℝ] UniformSpace.Completion Y).comp (v.constrL b) with hU
  have hUi : ∀ i, ‖U (v i)‖ ≤ δ / C := by
    intro i
    rw [hU, sub_apply, ContinuousLinearMap.comp_apply, Module.Basis.constrL_basis,
      UniformSpace.Completion.coe_toComplL, ← dist_eq_norm]
    exact (hb i).le
  have hUn : ‖U‖ ≤ δ := (hCv hδC.le hUi).trans_eq (by field_simp)
  have hUu : Bh u - ((v.constrL b u : Y) : UniformSpace.Completion Y) = U u := by
    rw [hU, sub_apply, ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL]
  rw [hUu]
  exact (U.le_opNorm u).trans (mul_le_mul_of_nonneg_right hUn (norm_nonneg u))

variable [MeasurableSpace E]

/-- Completion invariance of the affine fitting infimum when the testing ball is
measurable and has finite measure. -/
theorem affineErrorSq_completion_of_measurableSet_ball (μ : Measure (E × Time))
    (f : E × Time → Y) (y : E × Time) (s : ℝ) (hball : MeasurableSet (Metric.ball y s))
    (hμ : μ (Metric.ball y s) < ⊤) :
    affineErrorSq μ (fun q => (f q : UniformSpace.Completion Y)) y s = affineErrorSq μ f y s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [affineErrorSq_of_nonpos _ _ _ hs, affineErrorSq_of_nonpos _ _ _ hs]
  rw [affineErrorSq_of_pos _ _ _ hs, affineErrorSq_of_pos _ _ _ hs]
  congr 1
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun a B => (iInf₂_le (a : UniformSpace.Completion Y)
      ((UniformSpace.Completion.toComplL : Y →L[ℝ] UniformSpace.Completion Y).comp B)).trans (le_of_eq ?_)
    refine lintegral_congr fun q => ?_
    rw [ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL,
      ← UniformSpace.Completion.coe_add, ← UniformSpace.Completion.coe_sub, ← ofReal_norm,
      ← ofReal_norm, UniformSpace.Completion.norm_coe]
  · refine le_iInf₂ fun ah Bh => ?_
    rcases eq_or_ne (affineFitIntegral μ (fun q => (f q : UniformSpace.Completion Y)) ah Bh y s) ⊤
      with hXt | hXt
    · rw [hXt]
      exact le_top
    obtain ⟨Xr, hXr, hXeq⟩ : ∃ r : ℝ, 0 ≤ r ∧
        affineFitIntegral μ (fun q => (f q : UniformSpace.Completion Y)) ah Bh y s =
          ENNReal.ofReal r :=
      ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hXt).symm⟩
    obtain ⟨M, hM, hMeq⟩ : ∃ r : ℝ, 0 ≤ r ∧ μ (Metric.ball y s) = ENNReal.ofReal r :=
      ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hμ.ne).symm⟩
    rw [hXeq]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
    obtain ⟨η, hη, hηX⟩ : ∃ η : ℝ, 0 < η ∧ η * Xr ≤ ε / 2 := by
      refine ⟨ε / (2 * (Xr + 1)), by positivity, ?_⟩
      have hX1 : Xr + 1 ≠ 0 := by positivity
      calc ε / (2 * (Xr + 1)) * Xr = ε / 2 * (Xr / (Xr + 1)) := by field_simp
        _ ≤ ε / 2 * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 (by linarith))
            (by positivity)
        _ = ε / 2 := mul_one _
    have hlim : Tendsto (fun δ : ℝ => (1 + η⁻¹) * (δ * (‖y.1‖ + s + 1)) ^ 2 * M) (𝓝[>] 0)
        (𝓝 0) := by
      have h0 : Tendsto (fun δ : ℝ => (1 + η⁻¹) * (δ * (‖y.1‖ + s + 1)) ^ 2 * M) (𝓝 0)
          (𝓝 ((1 + η⁻¹) * (0 * (‖y.1‖ + s + 1)) ^ 2 * M)) :=
        ((continuous_const.mul ((continuous_id.mul continuous_const).pow 2)).mul
          continuous_const).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hδsmall, hδ⟩ :=
      ((hlim.eventually (gt_mem_nhds (half_pos hε'))).and self_mem_nhdsWithin).exists
    have hδ0 : 0 < δ := hδ
    obtain ⟨a, B, ha, hB⟩ := exists_approx_coeff ah Bh hδ0
    have hpt : ∀ q ∈ Metric.ball y s, ‖f q - (a + B q.1)‖ ≤
        ‖(f q : UniformSpace.Completion Y) - (ah + Bh q.1)‖ + δ * (‖y.1‖ + s + 1) := by
      intro q hq
      have hq1 : ‖q.1‖ ≤ ‖y.1‖ + s := by
        have h1 : dist q.1 y.1 ≤ dist q y := by
          rw [Prod.dist_eq]
          exact le_max_left _ _
        have h2 := Metric.mem_ball.1 hq
        have h3 := norm_sub_norm_le q.1 y.1
        rw [← dist_eq_norm] at h3
        linarith
      calc ‖f q - (a + B q.1)‖
          = ‖((f q - (a + B q.1) : Y) : UniformSpace.Completion Y)‖ :=
            (UniformSpace.Completion.norm_coe _).symm
        _ = ‖((f q : UniformSpace.Completion Y) - (ah + Bh q.1)) +
              ((ah - (a : UniformSpace.Completion Y)) +
                (Bh q.1 - (B q.1 : UniformSpace.Completion Y)))‖ := by
            rw [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_add]
            congr 1
            abel
        _ ≤ ‖(f q : UniformSpace.Completion Y) - (ah + Bh q.1)‖ +
              (‖ah - (a : UniformSpace.Completion Y)‖ +
                ‖Bh q.1 - (B q.1 : UniformSpace.Completion Y)‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ ‖(f q : UniformSpace.Completion Y) - (ah + Bh q.1)‖ + (δ + δ * (‖y.1‖ + s)) := by
            gcongr
            exact (hB q.1).trans (mul_le_mul_of_nonneg_left hq1 hδ0.le)
        _ = ‖(f q : UniformSpace.Completion Y) - (ah + Bh q.1)‖ + δ * (‖y.1‖ + s + 1) := by
            ring
    have hfit := affineFitIntegral_le_of_norm_le (μ := μ) hball hη hpt
    rw [hXeq, hMeq] at hfit
    have h1 : ⨅ (a' : Y) (B' : E →L[ℝ] Y), affineFitIntegral μ f a' B' y s ≤
        affineFitIntegral μ f a B y s := iInf_le_of_le a (iInf_le_of_le B le_rfl)
    refine h1.trans (le_trans hfit ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_add hXr hε'.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsmall : (1 + η⁻¹) * (δ * (‖y.1‖ + s + 1)) ^ 2 * M < ε / 2 := hδsmall
    nlinarith [hηX, hsmall]

/-- Completion invariance of the affine fitting infimum for a Borel spatial factor. -/
theorem affineErrorSq_completion_of_borelSpace [BorelSpace E] (μ : Measure (E × Time))
    (f : E × Time → Y) (y : E × Time) (s : ℝ) (hμ : μ (Metric.ball y s) < ⊤) :
    affineErrorSq μ (fun q => (f q : UniformSpace.Completion Y)) y s = affineErrorSq μ f y s :=
  affineErrorSq_completion_of_measurableSet_ball μ f y s measurableSet_ball hμ

end Completion

/-! ## Taylor expansion of the cutoff -/

section Taylor

variable {m : ℕ} {χ : Space m → ℝ} {K R₀ : ℝ}

theorem nonneg_of_hasParabolicDerivBounds (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀) :
    0 ≤ K := by
  have h := (norm_nonneg _).trans (hχ.spatial_le 0 0)
  rwa [le_div_iff₀ hR, zero_mul] at h

/-- The spatial affine Taylor remainder of a cutoff at `y`:
`|χ(q) - χ(y) - D(u - u_y)| ≤ K R₀^{-2} (|u - u_y|^2 + |t - t_y|)`. -/
theorem abs_taylor_remainder_le (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀)
    (y q : Space m) :
    |χ q - χ y - fderiv ℝ (fun v => χ (point v y.2.val)) y.1 (q.1 - y.1)| ≤
      K / R₀ ^ 2 * (‖q.1 - y.1‖ ^ 2 + |q.2.val - y.2.val|) := by
  have hK := nonneg_of_hasParabolicDerivBounds hR hχ
  have hc2 : ∀ t : ℝ, ContDiff ℝ 2 (fun v : Spatial m => χ (point v t)) := fun t =>
    hχ.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hds : ∀ t : ℝ, Differentiable ℝ (fun v : Spatial m => χ (point v t)) := fun t =>
    (hc2 t).differentiable two_ne_zero
  have hdds : ∀ t : ℝ, Differentiable ℝ (fderiv ℝ (fun v : Spatial m => χ (point v t))) :=
    fun t => ((hc2 t).fderiv_right (m := 1) one_add_one_eq_two.le).differentiable one_ne_zero
  have hdt : ∀ u : Spatial m, Differentiable ℝ (fun s : ℝ => χ (point u s)) := fun u =>
    (hχ.contDiff.comp (contDiff_const.prodMk contDiff_id)).differentiable two_ne_zero
  set t₀ := y.2.val with ht₀
  set D := fderiv ℝ (fun v => χ (point v t₀)) y.1 with hD
  have htime : |χ (point q.1 q.2.val) - χ (point q.1 t₀)| ≤ K / R₀ ^ 2 * |q.2.val - t₀| := by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun s _ => (hdt q.1) s) (fun s _ => by
        rw [Real.norm_eq_abs]; exact hχ.time_le q.1 s) (mem_univ t₀) (mem_univ q.2.val)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hDv : ∀ v : Spatial m,
      ‖fderiv ℝ (fun w => χ (point w t₀)) v - D‖ ≤ K / R₀ ^ 2 * ‖v - y.1‖ := fun v =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => (hdds t₀) w) (fun w _ => hχ.spatial₂_le w t₀) (mem_univ y.1) (mem_univ v)
  set r := ‖q.1 - y.1‖ with hr
  have hspace : |χ (point q.1 t₀) - χ (point y.1 t₀) - D (q.1 - y.1)| ≤ K / R₀ ^ 2 * r ^ 2 := by
    let g : Spatial m → ℝ := fun v => χ (point v t₀) - D v
    have hg : ∀ v, HasFDerivAt g (fderiv ℝ (fun w => χ (point w t₀)) v - D) v := fun v =>
      ((hds t₀) v).hasFDerivAt.sub D.hasFDerivAt
    have hgd : ∀ v ∈ Metric.closedBall y.1 r, ‖fderiv ℝ g v‖ ≤ K / R₀ ^ 2 * r := by
      intro v hv
      rw [(hg v).fderiv]
      refine (hDv v).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [← dist_eq_norm]
      exact hv
    have h := (convex_closedBall y.1 r).norm_image_sub_le_of_norm_fderiv_le
      (fun v _ => (hg v).differentiableAt) hgd (Metric.mem_closedBall_self (norm_nonneg _))
      (Metric.mem_closedBall.2 (le_of_eq (dist_eq_norm _ _)))
    have e : g q.1 - g y.1 = χ (point q.1 t₀) - χ (point y.1 t₀) - D (q.1 - y.1) := by
      simp only [g, map_sub]
      ring
    rw [← e, ← Real.norm_eq_abs]
    calc ‖g q.1 - g y.1‖ ≤ K / R₀ ^ 2 * r * ‖q.1 - y.1‖ := h
      _ = K / R₀ ^ 2 * r ^ 2 := by rw [← hr]; ring
  have e1 : χ q = χ (point q.1 q.2.val) := rfl
  have e2 : χ y = χ (point y.1 t₀) := rfl
  calc |χ q - χ y - D (q.1 - y.1)|
      = |(χ (point q.1 q.2.val) - χ (point q.1 t₀)) +
          (χ (point q.1 t₀) - χ (point y.1 t₀) - D (q.1 - y.1))| := by
        rw [e1, e2]
        congr 1
        ring
    _ ≤ |χ (point q.1 q.2.val) - χ (point q.1 t₀)| +
          |χ (point q.1 t₀) - χ (point y.1 t₀) - D (q.1 - y.1)| := abs_add_le _ _
    _ ≤ K / R₀ ^ 2 * |q.2.val - t₀| + K / R₀ ^ 2 * r ^ 2 := add_le_add htime hspace
    _ = K / R₀ ^ 2 * (r ^ 2 + |q.2.val - t₀|) := by ring

end Taylor

/-! ## Pointwise bounds for the affine error of the cutoff -/

theorem baseDimension_spatial_eq (m : ℕ) : baseDimension (Spatial m) = m + 2 := by
  simp [baseDimension]

section Pointwise

variable {m : ℕ} {χ : Space m → ℝ} {K R₀ : ℝ} {z₀ : Space m}
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Small scales `s ≤ R₀`: `κ_H(y,s)^2 ≤ 2 κ_F(y,s)^2 + 338 v K^2 L^2 s/R₀`. -/
theorem affineErrorSq_cutoff_le_small (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀)
    (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hsupp : tsupport χ ⊆ Metric.ball z₀ (4 * R₀))
    (F : Space m → Y) (L : ℝ≥0) (hF : LipschitzWith L F) (y : Space m) {s : ℝ}
    (hs : 0 < s) (hsR : s ≤ R₀) :
    affineErrorSq (parabolicVolume m) (fun p => χ p • (F p - F z₀)) y s ≤
      2 * affineErrorSq (parabolicVolume m) F y s +
        ENNReal.ofReal (338 * (2 * omega m).toReal * K ^ 2 * (L : ℝ) ^ 2 * (s / R₀)) := by
  have hK := nonneg_of_hasParabolicDerivBounds hR hχ
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  rw [affineErrorSq_of_pos _ _ _ hs, affineErrorSq_of_pos _ _ _ hs]
  by_cases hmeet : ∃ p ∈ Metric.ball y s, p ∈ Metric.ball z₀ (4 * R₀)
  swap
  · simp only [not_exists, not_and] at hmeet
    have hzero : ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
        affineFitIntegral (parabolicVolume m) (fun p => χ p • (F p - F z₀)) a B y s = 0 := by
      refine le_antisymm ((iInf₂_le 0 0).trans (le_of_eq ?_)) zero_le
      unfold affineFitIntegral
      refine (setLIntegral_congr_fun measurableSet_ball (g := fun _ => 0)
        fun q hq => ?_).trans lintegral_zero
      have hq0 : χ q = 0 := image_eq_zero_of_notMem_tsupport fun h => hmeet q hq (hsupp h)
      simp [hq0]
    rw [hzero, mul_zero]
    exact zero_le
  obtain ⟨p, hpy, hpz⟩ := hmeet
  have h6 : ∀ q ∈ Metric.ball y s, dist q z₀ ≤ 6 * R₀ := by
    intro q hq
    have h1 := Metric.mem_ball.1 hq
    have h2 := Metric.mem_ball.1 hpy
    have h3 := Metric.mem_ball.1 hpz
    have h4 := dist_triangle4 q y p z₀
    rw [dist_comm y p] at h4
    linarith
  set t₀ := y.2.val with ht₀
  set D := fderiv ℝ (fun v => χ (point v t₀)) y.1 with hD
  have hDn : ‖D‖ ≤ K / R₀ := hχ.spatial_le y.1 t₀
  have hs0 : s ≠ 0 := hs.ne'
  have hR0 : R₀ ≠ 0 := hR.ne'
  set e := 13 * K * L * s ^ 2 / R₀ with he
  have hfit : ∀ (a : Y) (B : Spatial m →L[ℝ] Y),
      affineFitIntegral (parabolicVolume m) (fun p => χ p • (F p - F z₀))
          (χ y • (a - F z₀) - D y.1 • (F y - F z₀)) (χ y • B + D.smulRight (F y - F z₀)) y s ≤
        ENNReal.ofReal (1 + 1) * affineFitIntegral (parabolicVolume m) F a B y s +
          ENNReal.ofReal ((1 + 1⁻¹) * e ^ 2) * parabolicVolume m (Metric.ball y s) := by
    intro a B
    refine affineFitIntegral_le_of_norm_le measurableSet_ball one_pos fun q hq => ?_
    have hq' := Metric.mem_ball.1 hq
    have hpq : dist q y = max ‖q.1 - y.1‖ (Real.sqrt |q.2.val - y.2.val|) :=
      dist_point q.1 y.1 q.2.val y.2.val
    rw [hpq, max_lt_iff] at hq'
    have hx : ‖q.1 - y.1‖ ≤ s := hq'.1.le
    have ht : |q.2.val - y.2.val| ≤ s ^ 2 := (Real.sqrt_le_left hs.le).1 hq'.2.le
    set ρ := χ q - χ y - D (q.1 - y.1) with hρ
    have hρb : |ρ| ≤ K / R₀ ^ 2 * (s ^ 2 + s ^ 2) :=
      (abs_taylor_remainder_le hR hχ y q).trans (mul_le_mul_of_nonneg_left
        (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hx 2) ht) (by positivity))
    have hχy : |χ y| ≤ 1 := by
      rw [abs_of_nonneg (h01 y).1]
      exact (h01 y).2
    have hDl : |D (q.1 - y.1)| ≤ K / R₀ * s := by
      rw [← Real.norm_eq_abs]
      exact (D.le_opNorm _).trans (mul_le_mul hDn hx (norm_nonneg _) (by positivity))
    have hFy : ‖F q - F y‖ ≤ L * s := by
      rw [← dist_eq_norm]
      refine (hF.dist_le_mul q y).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [hpq]
      exact max_le hx (by rw [Real.sqrt_le_left hs.le]; exact ht)
    have hFz : ‖F q - F z₀‖ ≤ L * (6 * R₀) := by
      rw [← dist_eq_norm]
      exact (hF.dist_le_mul q z₀).trans (mul_le_mul_of_nonneg_left (h6 q hq) hL)
    have hid : χ q • (F q - F z₀) - ((χ y • (a - F z₀) - D y.1 • (F y - F z₀)) +
          (χ y • B + D.smulRight (F y - F z₀)) q.1) =
        χ y • (F q - (a + B q.1)) + D (q.1 - y.1) • (F q - F y) + ρ • (F q - F z₀) := by
      have hχq : χ q = χ y + D (q.1 - y.1) + ρ := by rw [hρ]; ring
      rw [hχq]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, map_sub]
      module
    rw [hid]
    calc ‖χ y • (F q - (a + B q.1)) + D (q.1 - y.1) • (F q - F y) + ρ • (F q - F z₀)‖
        ≤ ‖χ y • (F q - (a + B q.1))‖ + ‖D (q.1 - y.1) • (F q - F y)‖ +
            ‖ρ • (F q - F z₀)‖ := norm_add₃_le
      _ = |χ y| * ‖F q - (a + B q.1)‖ + |D (q.1 - y.1)| * ‖F q - F y‖ +
            |ρ| * ‖F q - F z₀‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖F q - (a + B q.1)‖ + K / R₀ * s * (L * s) +
            K / R₀ ^ 2 * (s ^ 2 + s ^ 2) * (L * (6 * R₀)) := by
          gcongr
      _ = ‖F q - (a + B q.1)‖ + e := by
          rw [he]
          field_simp
          ring
  have hinf : ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
        affineFitIntegral (parabolicVolume m) (fun p => χ p • (F p - F z₀)) a B y s ≤
      2 * (⨅ (a : Y) (B : Spatial m →L[ℝ] Y), affineFitIntegral (parabolicVolume m) F a B y s) +
        ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s) := by
    rw [ENNReal.mul_iInf_of_ne two_ne_zero (by norm_num), ENNReal.iInf_add]
    refine le_iInf fun a => ?_
    rw [ENNReal.mul_iInf_of_ne two_ne_zero (by norm_num), ENNReal.iInf_add]
    refine le_iInf fun B => ?_
    refine (iInf₂_le _ _).trans ((hfit a B).trans (le_of_eq ?_))
    norm_num
  have hnorm : (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
      (ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s)) ≤
      ENNReal.ofReal (338 * (2 * omega m).toReal * K ^ 2 * (L : ℝ) ^ 2 * (s / R₀)) := by
    rw [TraceExtension.parabolicVolume_ball_eq_ofReal y hs, baseDimension_spatial_eq,
      ← ENNReal.ofReal_inv_of_pos hs, ← ENNReal.ofReal_pow (inv_nonneg.2 hs.le),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsR' : s / R₀ ≤ 1 := (div_le_one hR).2 hsR
    have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
    have key : s⁻¹ ^ (m + 2 + 2) * s ^ (m + 2) = s⁻¹ ^ 2 := by
      rw [pow_add, mul_right_comm, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, one_mul]
    calc s⁻¹ ^ (m + 2 + 2) * (2 * e ^ 2 * ((2 * omega m).toReal * s ^ (m + 2)))
        = 2 * e ^ 2 * (2 * omega m).toReal * (s⁻¹ ^ (m + 2 + 2) * s ^ (m + 2)) := by ring
      _ = 338 * (2 * omega m).toReal * K ^ 2 * (L : ℝ) ^ 2 * (s / R₀) * (s / R₀) := by
          rw [key, he]
          field_simp
          ring
      _ ≤ 338 * (2 * omega m).toReal * K ^ 2 * (L : ℝ) ^ 2 * (s / R₀) * 1 :=
          mul_le_mul_of_nonneg_left hsR' (by positivity)
      _ = 338 * (2 * omega m).toReal * K ^ 2 * (L : ℝ) ^ 2 * (s / R₀) := mul_one _
  calc (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
        ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
          affineFitIntegral (parabolicVolume m) (fun p => χ p • (F p - F z₀)) a B y s
      ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
          (2 * (⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
              affineFitIntegral (parabolicVolume m) F a B y s) +
            ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s)) :=
        mul_le_mul' le_rfl hinf
    _ = 2 * ((ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
          ⨅ (a : Y) (B : Spatial m →L[ℝ] Y), affineFitIntegral (parabolicVolume m) F a B y s) +
          (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
            (ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s)) := by
        ring
    _ ≤ _ := add_le_add le_rfl hnorm

/-- Large scales `s ≥ R₀`: the zero comparison, `κ_H(y,s)^2 ≤ 16 v 4^k L^2 R₀^2 s^{-2}`. -/
theorem affineErrorSq_cutoff_le_large (hR : 0 < R₀) (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1)
    (hsupp : tsupport χ ⊆ Metric.ball z₀ (4 * R₀)) (F : Space m → Y) (L : ℝ≥0)
    (hF : LipschitzWith L F) (y : Space m) {s : ℝ} (hRs : R₀ ≤ s) :
    affineErrorSq (parabolicVolume m) (fun p => χ p • (F p - F z₀)) y s ≤
      ENNReal.ofReal (16 * (2 * omega m).toReal * 4 ^ (m + 2) * (L : ℝ) ^ 2 * R₀ ^ 2) *
        (ENNReal.ofReal s)⁻¹ ^ 2 := by
  have hs : 0 < s := hR.trans_le hRs
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
  have hpt : ∀ q, ‖χ q • (F q - F z₀) - (0 + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2 ≤
      (Metric.ball z₀ (4 * R₀)).indicator (fun _ => ENNReal.ofReal (4 * L * R₀) ^ 2) q := by
    intro q
    by_cases hq : q ∈ Metric.ball z₀ (4 * R₀)
    · rw [Set.indicator_of_mem hq, zero_apply, add_zero, sub_zero]
      refine pow_le_pow_left₀ zero_le ?_ 2
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (h01 q).1, ← dist_eq_norm]
      have hq4 := (Metric.mem_ball.1 hq).le
      calc χ q * dist (F q) (F z₀) ≤ 1 * (L * dist q z₀) :=
            mul_le_mul (h01 q).2 (hF.dist_le_mul q z₀) dist_nonneg zero_le_one
        _ ≤ 1 * (L * (4 * R₀)) := by gcongr
        _ = 4 * L * R₀ := by ring
    · have hq0 : χ q = 0 := image_eq_zero_of_notMem_tsupport fun h => hq (hsupp h)
      rw [Set.indicator_of_notMem hq]
      simp [hq0]
  have hfitInt : affineFitIntegral (parabolicVolume m) (fun p => χ p • (F p - F z₀)) 0 0 y s ≤
      ENNReal.ofReal (16 * (L : ℝ) ^ 2 * R₀ ^ 2 * ((2 * omega m).toReal * (4 * R₀) ^ (m + 2))) := by
    calc affineFitIntegral (parabolicVolume m) (fun p => χ p • (F p - F z₀)) 0 0 y s
        ≤ ∫⁻ q, ‖χ q • (F q - F z₀) - (0 + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2
            ∂parabolicVolume m := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ q, (Metric.ball z₀ (4 * R₀)).indicator
            (fun _ => ENNReal.ofReal (4 * L * R₀) ^ 2) q ∂parabolicVolume m := lintegral_mono hpt
      _ = ENNReal.ofReal (4 * L * R₀) ^ 2 * parabolicVolume m (Metric.ball z₀ (4 * R₀)) :=
          lintegral_indicator_const measurableSet_ball _
      _ = _ := by
          rw [TraceExtension.parabolicVolume_ball_eq_ofReal z₀ (by positivity),
            ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine (affineErrorSq_le_fitIntegral _ _ _ hs 0 0).trans ?_
  refine (mul_le_mul' le_rfl hfitInt).trans ?_
  rw [baseDimension_spatial_eq, ← ENNReal.ofReal_inv_of_pos hs,
    ← ENNReal.ofReal_pow (inv_nonneg.2 hs.le), ← ENNReal.ofReal_pow (inv_nonneg.2 hs.le),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq : (R₀ * s⁻¹) ^ (m + 2) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [← div_eq_mul_inv]; exact (div_le_one hs).2 hRs)
  calc s⁻¹ ^ (m + 2 + 2) *
        (16 * (L : ℝ) ^ 2 * R₀ ^ 2 * ((2 * omega m).toReal * (4 * R₀) ^ (m + 2)))
      = 16 * (2 * omega m).toReal * 4 ^ (m + 2) * (L : ℝ) ^ 2 * R₀ ^ 2 * s⁻¹ ^ 2 *
          (R₀ * s⁻¹) ^ (m + 2) := by ring
    _ ≤ 16 * (2 * omega m).toReal * 4 ^ (m + 2) * (L : ℝ) ^ 2 * R₀ ^ 2 * s⁻¹ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

end Pointwise

/-! ## The scale bound and its `dr/r` integral -/

/-- The explicit scale bound `c₁ s/R₀` on `(0,R₀]` plus `c₂ s^{-2}` on `(R₀,∞)`. -/
def scaleBound (R₀ c₁ c₂ : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal c₁ * (Ioc 0 R₀).indicator (fun s => ENNReal.ofReal (s / R₀)) s +
    ENNReal.ofReal c₂ * (Ioi R₀).indicator (fun s => (ENNReal.ofReal s)⁻¹ ^ 2) s

theorem measurable_scaleBound (R₀ c₁ c₂ : ℝ) : Measurable (scaleBound R₀ c₁ c₂) :=
  (((measurable_id'.div_const R₀).ennreal_ofReal.indicator measurableSet_Ioc).const_mul _).add
    (((measurable_inv_pow_ofReal 2).indicator measurableSet_Ioi).const_mul _)

theorem lintegral_Ioc_div_scaleMeasure {R₀ : ℝ} (hR : 0 < R₀) :
    ∫⁻ s in Ioc 0 R₀, ENNReal.ofReal (s / R₀) ∂scaleMeasure = 1 := by
  rw [setLIntegral_scaleMeasure measurableSet_Ioc (fun s hs => hs.1) _
    (measurable_id'.div_const R₀).ennreal_ofReal]
  rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => ENNReal.ofReal (1 / R₀))
    fun s hs => by
      have hs0 : 0 < s := hs.1
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp]
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
    one_div, inv_mul_cancel₀ hR.ne', ENNReal.ofReal_one]

theorem lintegral_scaleBound {R₀ c₁ c₂ : ℝ} (hR : 0 < R₀) (hc₂ : 0 ≤ c₂) :
    ∫⁻ s, scaleBound R₀ c₁ c₂ s ∂scaleMeasure = ENNReal.ofReal c₁ + ENNReal.ofReal (c₂ / (2 * R₀ ^ 2)) := by
  unfold scaleBound
  rw [lintegral_add_left (((measurable_id'.div_const R₀).ennreal_ofReal.indicator
      measurableSet_Ioc).const_mul _),
    lintegral_const_mul _ ((measurable_id'.div_const R₀).ennreal_ofReal.indicator measurableSet_Ioc),
    lintegral_const_mul _ ((measurable_inv_pow_ofReal 2).indicator measurableSet_Ioi),
    lintegral_indicator measurableSet_Ioc, lintegral_indicator measurableSet_Ioi,
    lintegral_Ioc_div_scaleMeasure hR, lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos hR, mul_one,
    ← ENNReal.ofReal_mul hc₂]
  congr 2
  push_cast
  field_simp

/-! ## The cutoff Carleson bound and the compact cutoff -/

end CutoffCarleson

open CutoffCarleson in
/-- **Carleson bound of a cutoff.** The
affine Carleson constant of `H = χ (F - F(z₀))` is at most `C (B + L^2)`. -/
theorem cutoff_affineCarleson_proof (m : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z₀ : Space m) (R₀ : ℝ), 0 < R₀ → ∀ χ : Space m → ℝ,
      HasParabolicDerivBounds χ K R₀ → (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) →
      (∀ p ∈ Metric.ball z₀ R₀, χ p = 1) → tsupport χ ⊆ Metric.ball z₀ (4 * R₀) →
      ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (F : Space m → Y)
        (L : ℝ≥0) (B : ℝ), LipschitzWith L F → HasAffineCarlesonBound (parabolicVolume m) F B →
        HasAffineCarlesonBound (parabolicVolume m) (fun p => χ p • (F p - F z₀))
          (C * (B + (L : ℝ) ^ 2)) := by
  refine ⟨2 + (338 * (2 * omega m).toReal * K ^ 2 + 8 * (2 * omega m).toReal * 4 ^ (m + 2)) *
    (2 * omega m).toReal, by positivity, ?_⟩
  intro z₀ R₀ hR χ hχ h01 _ hsupp Y _ _ F L B hF hFB
  obtain ⟨hB0, hFB⟩ := hFB
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hR0 : R₀ ≠ 0 := hR.ne'
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = 338 * (2 * omega m).toReal * K ^ 2 * (L : ℝ) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ,
      c = 16 * (2 * omega m).toReal * 4 ^ (m + 2) * (L : ℝ) ^ 2 * R₀ ^ 2 := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  have hpt : ∀ y s, 0 < s →
      affineErrorSq (parabolicVolume m) (fun p => χ p • (F p - F z₀)) y s ≤
        2 * affineErrorSq (parabolicVolume m) F y s + scaleBound R₀ c₁ c₂ s := by
    intro y s hs
    rcases le_or_gt s R₀ with hsR | hsR
    · refine (affineErrorSq_cutoff_le_small hR hχ h01 hsupp F L hF y hs hsR).trans
        (add_le_add le_rfl (le_of_eq ?_))
      have hmem : s ∈ Ioc 0 R₀ := ⟨hs, hsR⟩
      have hnot : s ∉ Ioi R₀ := not_lt.2 hsR
      rw [scaleBound, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, mul_zero,
        add_zero, ← ENNReal.ofReal_mul hc₁0, hc₁]
    · refine (affineErrorSq_cutoff_le_large hR h01 hsupp F L hF y hsR.le).trans ?_
      have hmem : s ∈ Ioi R₀ := hsR
      rw [scaleBound, Set.indicator_of_mem hmem, hc₂]
      exact le_add_left le_add_self
  refine ⟨mul_nonneg (by positivity) (add_nonneg hB0 (sq_nonneg _)), fun z R hRpos => ?_⟩
  have hint : ∫⁻ s in Ioo 0 R, scaleBound R₀ c₁ c₂ s ∂scaleMeasure ≤
      ENNReal.ofReal ((338 * (2 * omega m).toReal * K ^ 2 +
        8 * (2 * omega m).toReal * 4 ^ (m + 2)) * (L : ℝ) ^ 2) := by
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
    rw [lintegral_scaleBound hR hc₂0, ← ENNReal.ofReal_add hc₁0 (by positivity), hc₁, hc₂]
    congr 1
    field_simp
    ring
  have hvol := (TraceExtension.parabolicVolume_ball_eq_ofReal z hRpos).le
  calc affineCarlesonIntegral (parabolicVolume m) (fun p => χ p • (F p - F z₀)) z R
      = ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R,
          affineErrorSq (parabolicVolume m) (fun p => χ p • (F p - F z₀)) y s
            ∂scaleMeasure ∂parabolicVolume m := rfl
    _ ≤ ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R,
          (2 * affineErrorSq (parabolicVolume m) F y s + scaleBound R₀ c₁ c₂ s)
            ∂scaleMeasure ∂parabolicVolume m :=
        lintegral_mono fun y => setLIntegral_mono' measurableSet_Ioo fun s hs => hpt y s hs.1
    _ = ∫⁻ y in Metric.ball z R, (2 * ∫⁻ s in Ioo 0 R,
            affineErrorSq (parabolicVolume m) F y s ∂scaleMeasure +
          ∫⁻ s in Ioo 0 R, scaleBound R₀ c₁ c₂ s ∂scaleMeasure) ∂parabolicVolume m := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_add_right _ (measurable_scaleBound R₀ c₁ c₂),
          lintegral_const_mul' _ _ (by norm_num)]
    _ = 2 * affineCarlesonIntegral (parabolicVolume m) F z R +
          (∫⁻ s in Ioo 0 R, scaleBound R₀ c₁ c₂ s ∂scaleMeasure) *
            parabolicVolume m (Metric.ball z R) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
          setLIntegral_const]
        rfl
    _ ≤ 2 * ENNReal.ofReal (B * R ^ baseDimension (Spatial m)) +
          ENNReal.ofReal ((338 * (2 * omega m).toReal * K ^ 2 +
            8 * (2 * omega m).toReal * 4 ^ (m + 2)) * (L : ℝ) ^ 2) *
            ENNReal.ofReal ((2 * omega m).toReal * R ^ (m + 2)) :=
        add_le_add (mul_le_mul' le_rfl (hFB z R hRpos)) (mul_le_mul' hint hvol)
    _ = ENNReal.ofReal (2 * (B * R ^ (m + 2)) +
          (338 * (2 * omega m).toReal * K ^ 2 + 8 * (2 * omega m).toReal * 4 ^ (m + 2)) *
            (L : ℝ) ^ 2 * ((2 * omega m).toReal * R ^ (m + 2))) := by
        rw [baseDimension_spatial_eq, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((2 + (338 * (2 * omega m).toReal * K ^ 2 +
          8 * (2 * omega m).toReal * 4 ^ (m + 2)) * (2 * omega m).toReal) *
          (B + (L : ℝ) ^ 2) * R ^ baseDimension (Spatial m)) := by
        rw [baseDimension_spatial_eq]
        refine ENNReal.ofReal_le_ofReal ?_
        have hextra : 0 ≤ (2 * (L : ℝ) ^ 2 + (338 * (2 * omega m).toReal * K ^ 2 +
            8 * (2 * omega m).toReal * 4 ^ (m + 2)) * (2 * omega m).toReal * B) *
            R ^ (m + 2) := by positivity
        nlinarith [hextra]

/-- **Cutoff lemma.** An `L`-Lipschitz `F` with
affine Carleson constant `B` agrees on `P(z₀,R₀)` with `G = c + H`, `H` compactly supported,
`Lip G ≤ C L` and affine Carleson constant of `H` at most `C (B + L^2)`. Combines
`exists_parabolic_cutoff`, `cutoff_lipschitz` and `cutoff_affineCarleson_proof`. -/
theorem exists_compact_cutoff_affineCarleson_proof (m : ℕ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
      (F : Space m → Y) (L : ℝ≥0) (B : ℝ), LipschitzWith L F →
      HasAffineCarlesonBound (parabolicVolume m) F B →
      ∀ (z₀ : Space m) (R₀ : ℝ), 0 < R₀ →
        ∃ (c : Y) (H : Space m → Y), (∀ p ∈ Metric.ball z₀ R₀, c + H p = F p) ∧
          HasCompactSupport H ∧ LipschitzWith (C * L) (fun p => c + H p) ∧
          HasAffineCarlesonBound (parabolicVolume m) H (C * (B + (L : ℝ) ^ 2)) := by
  obtain ⟨K, -, hcut⟩ := TraceExtension.exists_parabolic_cutoff m
  obtain ⟨C₁, hC₁⟩ := TraceExtension.cutoff_lipschitz m K
  obtain ⟨C₂, -, hC₂⟩ := cutoff_affineCarleson_proof m K
  refine ⟨max (max C₁ (Real.toNNReal C₂)) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro Y _ _ F L B hF hFB z₀ R₀ hR
  obtain ⟨χ, hχ, h01, hone, hsupp⟩ := hcut z₀ R₀ hR
  obtain ⟨hLip, hcs⟩ := hC₁ z₀ R₀ hR χ hχ h01 hsupp F L hF
  have hCarl := hC₂ z₀ R₀ hR χ hχ h01 hone hsupp F L B hF hFB
  refine ⟨F z₀, fun p => χ p • (F p - F z₀), fun p hp => ?_, hcs, ?_, ?_⟩
  · simp [hone p hp]
  · have hle : C₁ * L ≤ max (max C₁ (Real.toNNReal C₂)) 1 * L :=
      mul_le_mul' ((le_max_left _ _).trans (le_max_left _ _)) le_rfl
    refine (LipschitzWith.of_dist_le_mul fun p q => ?_).weaken hle
    rw [dist_add_left]
    exact hLip.dist_le_mul p q
  · obtain ⟨hB0, -⟩ := hFB
    have hBL : 0 ≤ B + (L : ℝ) ^ 2 := add_nonneg hB0 (sq_nonneg _)
    refine ⟨mul_nonneg (NNReal.coe_nonneg _) hBL, fun z R hRpos =>
      (hCarl.2 z R hRpos).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hBL) (by positivity)
    calc C₂ ≤ (Real.toNNReal C₂ : ℝ) := Real.le_coe_toNNReal C₂
      _ ≤ _ := NNReal.coe_le_coe.2 ((le_max_right _ _).trans (le_max_left _ _))

end ParabolicRectifiability
