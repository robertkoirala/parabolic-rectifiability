import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Analysis.TraceExtension.Cutoff
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! # Pointwise affine-error comparison for a smooth cutoff

Part of the proof of `affineEnergy_cutoff_le_proof` (localization of the affine energy).

Let `χ` be a cutoff with parabolic `C^{2,1}` bounds `K` at scale `R₀`
(`HasParabolicDerivBounds χ K R₀`), values in `[0,1]` and nonzero only on `P(z₀,4R₀)`.
Let `G` be parabolic `L`-Lipschitz and `c` a constant with `|G - c| ≤ 7 L R₀` on
`P̄(z₀,6R₀)`; in the application, `c` is the mean of `F` over `P(0,R₀)`.

* **Small scales** (`rx4_affineErrorSq_cutoff_le_small`), for `0 < s ≤ R₀`:
  `κ_H(y,s)^2 ≤ 1_{P(z₀,5R₀)}(y) (2 κ_G(y,s)^2 + 450 v K^2 L^2 (s/R₀)^2)`, `H = χ (G - c)`,
  `v = 2ω_m`. For every spatial affine `A` the competitor
  `A_H = χ(y) (A - c) + D(· - u_y) (G(y) - c)`, `D = ∇_u χ(·, t_y)(u_y)`, satisfies
  `H - A_H = χ(y)(G - A) + D(u - u_y)(G - G(y)) + ρ (G - c)` with the Taylor remainder
  `|ρ| ≤ K R₀^{-2}(|u - u_y|^2 + |t - t_y|)`; hence `|H - A_H| ≤ |G - A| + 15 K L s^2/R₀`.
  No best fit is selected.
* **All scales, zero competitor** (`rx4_affineErrorSq_cutoff_le_zero`), for `s > 0`:
  `κ_H(y,s)^2 ≤ 1_{P(z₀,4R₀+s)}(y) 49 L^2 R₀^2 |P(z₀,4R₀)| s^{-k-2}`.

The elementary lemmas `rx4_sq_add_le_of_pos`, `rx4_enorm_sq_le_of_norm_le_add`,
`rx4_affineFitIntegral_le_of_norm_le`, `rx4_nonneg_of_hasParabolicDerivBounds`,
`rx4_abs_taylor_remainder_le` and `rx4_baseDimension_spatial_eq` are the same as in
`TraceExtension.CutoffCarleson`. The two comparison theorems adapt
`affineErrorSq_cutoff_le_small`/`_large` there to an arbitrary constant `c` and to the
indicator form needed for global integration.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-! ## Elementary comparison of fitting integrals -/

/-- `(x + d)^2 ≤ (1 + η) x^2 + (1 + η⁻¹) d^2` for `η > 0`. -/
theorem rx4_sq_add_le_of_pos (x d : ℝ) {η : ℝ} (hη : 0 < η) :
    (x + d) ^ 2 ≤ (1 + η) * x ^ 2 + (1 + η⁻¹) * d ^ 2 := by
  have h : (1 + η) * x ^ 2 + (1 + η⁻¹) * d ^ 2 = (x + d) ^ 2 + (η * x - d) ^ 2 / η := by
    field_simp
    ring
  rw [h]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hη.le)

theorem rx4_enorm_sq_le_of_norm_le_add {Y Z : Type*} [SeminormedAddCommGroup Y]
    [SeminormedAddCommGroup Z] {v : Y} {w : Z} {d η : ℝ} (hη : 0 < η)
    (h : ‖v‖ ≤ ‖w‖ + d) :
    ‖v‖ₑ ^ 2 ≤ ENNReal.ofReal (1 + η) * ‖w‖ₑ ^ 2 + ENNReal.ofReal ((1 + η⁻¹) * d ^ 2) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg (by have := inv_pos.2 hη; linarith) (sq_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖v‖ ^ 2 ≤ (‖w‖ + d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ _ := rx4_sq_add_le_of_pos _ _ hη

/-- A pointwise comparison of two affine residuals on a measurable ball compares their
fitting integrals; no measurability of the functions is needed. -/
theorem rx4_affineFitIntegral_le_of_norm_le {E Y Z : Type*} [NormedAddCommGroup E]
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
        setLIntegral_mono' hball fun q hq => rx4_enorm_sq_le_of_norm_le_add hη (h q hq)
    _ = ENNReal.ofReal (1 + η) * ∫⁻ q in Metric.ball y s, ‖g q - (a' + B' q.1)‖ₑ ^ 2 ∂μ +
          ENNReal.ofReal ((1 + η⁻¹) * d ^ 2) * μ (Metric.ball y s) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]

/-! ## Taylor expansion of the cutoff -/

section Taylor

variable {m : ℕ} {χ : Space m → ℝ} {K R₀ : ℝ}

theorem rx4_nonneg_of_hasParabolicDerivBounds (hR : 0 < R₀)
    (hχ : HasParabolicDerivBounds χ K R₀) : 0 ≤ K := by
  have h := (norm_nonneg _).trans (hχ.spatial_le 0 0)
  rwa [le_div_iff₀ hR, zero_mul] at h

/-- The spatial affine Taylor remainder of a cutoff at `y`:
`|χ(q) - χ(y) - D(u - u_y)| ≤ K R₀^{-2} (|u - u_y|^2 + |t - t_y|)`. -/
theorem rx4_abs_taylor_remainder_le (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀)
    (y q : Space m) :
    |χ q - χ y - fderiv ℝ (fun v => χ (point v y.2.val)) y.1 (q.1 - y.1)| ≤
      K / R₀ ^ 2 * (‖q.1 - y.1‖ ^ 2 + |q.2.val - y.2.val|) := by
  have hK := rx4_nonneg_of_hasParabolicDerivBounds hR hχ
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

theorem rx4_baseDimension_spatial_eq (m : ℕ) : baseDimension (Spatial m) = m + 2 := by
  simp [baseDimension]

/-! ## Pointwise bounds for the affine error of the cutoff -/

section Pointwise

variable {m : ℕ} {χ : Space m → ℝ} {K R₀ : ℝ} {z₀ : Space m}
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- **Small scales.** For `0 < s ≤ R₀`,
`κ_H(y,s)^2 ≤ 1_{P(z₀,5R₀)}(y) (2 κ_G(y,s)^2 + 450 v K^2 L^2 (s/R₀)^2)` for
`H = χ (G - c)`, `v = 2ω_m`. Balls `P(y,s)` that miss `P(z₀,4R₀)` have zero error. -/
theorem rx4_affineErrorSq_cutoff_le_small (hR : 0 < R₀) (hχ : HasParabolicDerivBounds χ K R₀)
    (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hsupp : ∀ p, χ p ≠ 0 → p ∈ Metric.ball z₀ (4 * R₀))
    (G : Space m → Y) (c : Y) {L : ℝ} (hL : 0 ≤ L)
    (hG : ∀ p q, ‖G p - G q‖ ≤ L * dist p q)
    (hc : ∀ q, dist q z₀ ≤ 6 * R₀ → ‖G q - c‖ ≤ 7 * L * R₀)
    (y : Space m) {s : ℝ} (hs : 0 < s) (hsR : s ≤ R₀) :
    affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s ≤
      (Metric.ball z₀ (5 * R₀)).indicator (fun y' =>
        2 * affineErrorSq (parabolicVolume m) G y' s +
          ENNReal.ofReal (450 * (2 * omega m).toReal * K ^ 2 * L ^ 2 * (s / R₀) ^ 2)) y := by
  have hK := rx4_nonneg_of_hasParabolicDerivBounds hR hχ
  by_cases hmeet : ∃ p ∈ Metric.ball y s, p ∈ Metric.ball z₀ (4 * R₀)
  swap
  · simp only [not_exists, not_and] at hmeet
    rw [affineErrorSq_of_pos _ _ _ hs]
    have hzero : ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
        affineFitIntegral (parabolicVolume m) (fun p => χ p • (G p - c)) a B y s = 0 := by
      refine le_antisymm ((iInf₂_le 0 0).trans (le_of_eq ?_)) zero_le
      unfold affineFitIntegral
      refine (setLIntegral_congr_fun measurableSet_ball (g := fun _ => 0)
        fun q hq => ?_).trans lintegral_zero
      have hq0 : χ q = 0 := by
        by_contra h
        exact hmeet q hq (hsupp q h)
      simp [hq0]
    rw [hzero, mul_zero]
    exact zero_le
  obtain ⟨p, hpy, hpz⟩ := hmeet
  have hy5 : y ∈ Metric.ball z₀ (5 * R₀) := by
    have h1 := Metric.mem_ball.1 hpy
    have h2 := Metric.mem_ball.1 hpz
    have h3 := dist_triangle y p z₀
    rw [dist_comm] at h1
    exact Metric.mem_ball.2 (by linarith)
  rw [Set.indicator_of_mem hy5, affineErrorSq_of_pos _ _ _ hs, affineErrorSq_of_pos _ _ _ hs]
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
  set e := 15 * K * L * s ^ 2 / R₀ with he
  have hfit : ∀ (a : Y) (B : Spatial m →L[ℝ] Y),
      affineFitIntegral (parabolicVolume m) (fun p => χ p • (G p - c))
          (χ y • (a - c) - D y.1 • (G y - c)) (χ y • B + D.smulRight (G y - c)) y s ≤
        ENNReal.ofReal (1 + 1) * affineFitIntegral (parabolicVolume m) G a B y s +
          ENNReal.ofReal ((1 + 1⁻¹) * e ^ 2) * parabolicVolume m (Metric.ball y s) := by
    intro a B
    refine rx4_affineFitIntegral_le_of_norm_le measurableSet_ball one_pos fun q hq => ?_
    have hq' := Metric.mem_ball.1 hq
    have hpq : dist q y = max ‖q.1 - y.1‖ (Real.sqrt |q.2.val - y.2.val|) :=
      dist_point q.1 y.1 q.2.val y.2.val
    rw [hpq, max_lt_iff] at hq'
    have hx : ‖q.1 - y.1‖ ≤ s := hq'.1.le
    have ht : |q.2.val - y.2.val| ≤ s ^ 2 := (Real.sqrt_le_left hs.le).1 hq'.2.le
    set ρ := χ q - χ y - D (q.1 - y.1) with hρ
    have hρb : |ρ| ≤ K / R₀ ^ 2 * (s ^ 2 + s ^ 2) :=
      (rx4_abs_taylor_remainder_le hR hχ y q).trans (mul_le_mul_of_nonneg_left
        (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hx 2) ht) (by positivity))
    have hχy : |χ y| ≤ 1 := by
      rw [abs_of_nonneg (h01 y).1]
      exact (h01 y).2
    have hDl : |D (q.1 - y.1)| ≤ K / R₀ * s := by
      rw [← Real.norm_eq_abs]
      exact (D.le_opNorm _).trans (mul_le_mul hDn hx (norm_nonneg _) (by positivity))
    have hFy : ‖G q - G y‖ ≤ L * s := by
      refine (hG q y).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [hpq]
      exact max_le hx (by rw [Real.sqrt_le_left hs.le]; exact ht)
    have hFz : ‖G q - c‖ ≤ 7 * L * R₀ := hc q (h6 q hq)
    have hid : χ q • (G q - c) - ((χ y • (a - c) - D y.1 • (G y - c)) +
          (χ y • B + D.smulRight (G y - c)) q.1) =
        χ y • (G q - (a + B q.1)) + D (q.1 - y.1) • (G q - G y) + ρ • (G q - c) := by
      have hχq : χ q = χ y + D (q.1 - y.1) + ρ := by rw [hρ]; ring
      rw [hχq]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, map_sub]
      module
    rw [hid]
    calc ‖χ y • (G q - (a + B q.1)) + D (q.1 - y.1) • (G q - G y) + ρ • (G q - c)‖
        ≤ ‖χ y • (G q - (a + B q.1))‖ + ‖D (q.1 - y.1) • (G q - G y)‖ +
            ‖ρ • (G q - c)‖ := norm_add₃_le
      _ = |χ y| * ‖G q - (a + B q.1)‖ + |D (q.1 - y.1)| * ‖G q - G y‖ +
            |ρ| * ‖G q - c‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖G q - (a + B q.1)‖ + K / R₀ * s * (L * s) +
            K / R₀ ^ 2 * (s ^ 2 + s ^ 2) * (7 * L * R₀) := by
          gcongr
      _ = ‖G q - (a + B q.1)‖ + e := by
          rw [he]
          field_simp
          ring
  have hinf : ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
        affineFitIntegral (parabolicVolume m) (fun p => χ p • (G p - c)) a B y s ≤
      2 * (⨅ (a : Y) (B : Spatial m →L[ℝ] Y), affineFitIntegral (parabolicVolume m) G a B y s) +
        ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s) := by
    rw [ENNReal.mul_iInf_of_ne two_ne_zero (by norm_num), ENNReal.iInf_add]
    refine le_iInf fun a => ?_
    rw [ENNReal.mul_iInf_of_ne two_ne_zero (by norm_num), ENNReal.iInf_add]
    refine le_iInf fun B => ?_
    refine (iInf₂_le _ _).trans ((hfit a B).trans (le_of_eq ?_))
    norm_num
  have hnorm : (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
      (ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s)) ≤
      ENNReal.ofReal (450 * (2 * omega m).toReal * K ^ 2 * L ^ 2 * (s / R₀) ^ 2) := by
    rw [TraceExtension.parabolicVolume_ball_eq_ofReal y hs, rx4_baseDimension_spatial_eq,
      ← ENNReal.ofReal_inv_of_pos hs, ← ENNReal.ofReal_pow (inv_nonneg.2 hs.le),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have key : s⁻¹ ^ (m + 2 + 2) * s ^ (m + 2) = s⁻¹ ^ 2 := by
      rw [pow_add, mul_right_comm, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, one_mul]
    calc s⁻¹ ^ (m + 2 + 2) * (2 * e ^ 2 * ((2 * omega m).toReal * s ^ (m + 2)))
        = 2 * e ^ 2 * (2 * omega m).toReal * (s⁻¹ ^ (m + 2 + 2) * s ^ (m + 2)) := by ring
      _ = 450 * (2 * omega m).toReal * K ^ 2 * L ^ 2 * (s / R₀) ^ 2 := by
          rw [key, he]
          field_simp
          ring
  calc (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
        ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
          affineFitIntegral (parabolicVolume m) (fun p => χ p • (G p - c)) a B y s
      ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
          (2 * (⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
              affineFitIntegral (parabolicVolume m) G a B y s) +
            ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s)) :=
        mul_le_mul' le_rfl hinf
    _ = 2 * ((ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
          ⨅ (a : Y) (B : Spatial m →L[ℝ] Y), affineFitIntegral (parabolicVolume m) G a B y s) +
          (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
            (ENNReal.ofReal (2 * e ^ 2) * parabolicVolume m (Metric.ball y s)) := by
        ring
    _ ≤ _ := add_le_add le_rfl hnorm

/-- **Zero comparison at every scale.** For `s > 0`,
`κ_H(y,s)^2 ≤ 1_{P(z₀,4R₀+s)}(y) 49 L^2 R₀^2 |P(z₀,4R₀)| s^{-k-2}`: test with the zero
affine map; `|H| ≤ 7 L R₀` on `P(z₀,4R₀)` and `H = 0` outside. -/
theorem rx4_affineErrorSq_cutoff_le_zero (hR : 0 < R₀)
    (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hsupp : ∀ p, χ p ≠ 0 → p ∈ Metric.ball z₀ (4 * R₀))
    (G : Space m → Y) (c : Y) {L : ℝ} (hL : 0 ≤ L)
    (hc : ∀ q, dist q z₀ ≤ 6 * R₀ → ‖G q - c‖ ≤ 7 * L * R₀)
    (y : Space m) {s : ℝ} (hs : 0 < s) :
    affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s ≤
      (Metric.ball z₀ (4 * R₀ + s)).indicator (fun _ =>
        ENNReal.ofReal (49 * L ^ 2 * R₀ ^ 2 * ((2 * omega m).toReal * (4 * R₀) ^ (m + 2))) *
          (ENNReal.ofReal s)⁻¹ ^ (m + 4)) y := by
  have hpt : ∀ q, ‖χ q • (G q - c) - (0 + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2 ≤
      (Metric.ball z₀ (4 * R₀)).indicator (fun _ => ENNReal.ofReal (7 * L * R₀) ^ 2) q := by
    intro q
    by_cases hq : q ∈ Metric.ball z₀ (4 * R₀)
    · rw [Set.indicator_of_mem hq, zero_apply, add_zero, sub_zero]
      refine pow_le_pow_left₀ zero_le ?_ 2
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (h01 q).1]
      have hq4 : dist q z₀ ≤ 6 * R₀ := by
        have := (Metric.mem_ball.1 hq).le
        linarith
      calc χ q * ‖G q - c‖ ≤ 1 * (7 * L * R₀) :=
            mul_le_mul (h01 q).2 (hc q hq4) (norm_nonneg _) zero_le_one
        _ = 7 * L * R₀ := one_mul _
    · have hq0 : χ q = 0 := by
        by_contra h
        exact hq (hsupp q h)
      rw [Set.indicator_of_notMem hq]
      simp [hq0]
  by_cases hy : y ∈ Metric.ball z₀ (4 * R₀ + s)
  · rw [Set.indicator_of_mem hy]
    have hfitInt :
        affineFitIntegral (parabolicVolume m) (fun p => χ p • (G p - c)) 0 0 y s ≤
          ENNReal.ofReal (49 * L ^ 2 * R₀ ^ 2 * ((2 * omega m).toReal * (4 * R₀) ^ (m + 2))) := by
      calc affineFitIntegral (parabolicVolume m) (fun p => χ p • (G p - c)) 0 0 y s
          ≤ ∫⁻ q, ‖χ q • (G q - c) - (0 + (0 : Spatial m →L[ℝ] Y) q.1)‖ₑ ^ 2
              ∂parabolicVolume m := setLIntegral_le_lintegral _ _
        _ ≤ ∫⁻ q, (Metric.ball z₀ (4 * R₀)).indicator
              (fun _ => ENNReal.ofReal (7 * L * R₀) ^ 2) q ∂parabolicVolume m :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (7 * L * R₀) ^ 2 * parabolicVolume m (Metric.ball z₀ (4 * R₀)) :=
            lintegral_indicator_const measurableSet_ball _
        _ = _ := by
            rw [TraceExtension.parabolicVolume_ball_eq_ofReal z₀ (by positivity),
              ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    refine (affineErrorSq_le_fitIntegral _ _ _ hs 0 0).trans ?_
    rw [rx4_baseDimension_spatial_eq, mul_comm]
    exact mul_le_mul' hfitInt le_rfl
  · rw [Set.indicator_of_notMem hy, affineErrorSq_of_pos _ _ _ hs]
    have hzero : ⨅ (a : Y) (B : Spatial m →L[ℝ] Y),
        affineFitIntegral (parabolicVolume m) (fun p => χ p • (G p - c)) a B y s = 0 := by
      refine le_antisymm ((iInf₂_le 0 0).trans (le_of_eq ?_)) zero_le
      unfold affineFitIntegral
      refine (setLIntegral_congr_fun measurableSet_ball (g := fun _ => 0)
        fun q hq => ?_).trans lintegral_zero
      have hq0 : χ q = 0 := by
        by_contra h
        apply hy
        have h1 := Metric.mem_ball.1 (hsupp q h)
        have h2 := Metric.mem_ball.1 hq
        have h3 := dist_triangle y q z₀
        rw [dist_comm] at h2
        exact Metric.mem_ball.2 (by linarith)
      simp [hq0]
    rw [hzero, mul_zero]

end Pointwise

end ParabolicRectifiability
