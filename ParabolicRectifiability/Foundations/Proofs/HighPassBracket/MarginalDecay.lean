import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel

/-! # The spatial marginal of a mean-zero test kernel has an `|t|^{-5/2}` tail

Proof of `fhpa_spatialIntegral_testKernel_decay`, as
`fhpa_spatialIntegral_testKernel_decay_proof`.

For a compactly supported Schwartz test `ψ` (later `ψ = realCompactTest φ`), write
`K = testKernel ψ`, `A = spatialTestSupport ψ` (compact) and `ψ̄(s) = ∫ ψ(u,s) du`
(`fhpab4_marginal`).

1. **Checkpoint 1 (Fubini in `(u,h)` at fixed `t`).** The kernel integrand is dominated by
   `1_A(u) · testKernelControl ψ · cancellationWeight h` (the spatial indicator is essential),
   so it is integrable on `ℝ^m × ℝ` (`fhpab4_integrable_prod`), and
   `∫ K(u,t) du = κ ∫ |h|^{-3/2} (ψ̄(t) - ψ̄(t-h)) dh` (`fhpab4_marginal_kernel_eq`).
   Only the test-kernel difference integrand is interchanged; no product with a growing
   coefficient is integrated.
2. **Checkpoint 2 (cancellation).** If `|t| > 2S` (time support in `[-S,S]`), then `ψ̄(t) = 0`
   and `∫ ψ̄ = ∫ ψ = 0`, so
   `∫ K(u,t) du = κ ∫ (|t|^{-3/2} - |h|^{-3/2}) ψ̄(t-h) dh`; on the support `|t-h| ≤ S` the
   mean-value bound `||t|^{-3/2} - |h|^{-3/2}| ≤ (3/2) (|t|/2)^{-5/2} S` gives the tail
   (`fhpab4_tail`). The global bound is `vol(A) · sup ‖K‖` (`fhpab4_norm_marginal_kernel_le`).
   Measurability is parameter integration of the jointly strongly measurable kernel.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-! ## Spatial sections, supports and indicator bounds -/

theorem fhpab4_continuous_toLp (s : ℝ) :
    Continuous fun u : Spatial m => (WithLp.toLp 2 (u, s) : FourierSpace m) :=
  (WithLp.prod_continuous_toLp 2 (Spatial m) ℝ).comp (continuous_id.prodMk continuous_const)

/-- The test vanishes on every time line over a point outside the spatial projection. -/
theorem fhpab4_eq_zero_of_notMem (ψ : 𝓢(FourierSpace m, ℂ)) {u : Spatial m}
    (hu : u ∉ spatialTestSupport ψ) (s : ℝ) : ψ (WithLp.toLp 2 (u, s)) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  exact hu ⟨WithLp.toLp 2 (u, s), hs, rfl⟩

/-- The test vanishes at times outside its time-support bound. -/
theorem fhpab4_eq_zero_of_time (ψ : 𝓢(FourierSpace m, ℂ)) {S : ℝ}
    (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S) (u : Spatial m) {s : ℝ}
    (hsS : S < |s|) : ψ (WithLp.toLp 2 (u, s)) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => (not_le.mpr hsS) (by simpa using hs _ h)

theorem fhpab4_norm_le_indicator {A : Set (Spatial m)} {f : Spatial m → ℂ} {B : ℝ}
    (hb : ∀ u ∈ A, ‖f u‖ ≤ B) (hz : ∀ u ∉ A, f u = 0) (u : Spatial m) :
    ‖f u‖ ≤ A.indicator (fun _ => B) u := by
  by_cases hu : u ∈ A
  · rw [indicator_of_mem hu]
    exact hb u hu
  · rw [indicator_of_notMem hu, hz u hu, norm_zero]

theorem fhpab4_integrable_indicator {A : Set (Spatial m)} (hA : IsCompact A) (B : ℝ) :
    Integrable (A.indicator fun _ : Spatial m => B) volume :=
  (integrableOn_const hA.measure_ne_top).integrable_indicator hA.measurableSet

/-- A function bounded by `B` on a compact set and zero off it has integral at most
`vol(A) · B`. -/
theorem fhpab4_norm_integral_le {A : Set (Spatial m)} (hA : IsCompact A)
    {f : Spatial m → ℂ} {B : ℝ} (hb : ∀ u ∈ A, ‖f u‖ ≤ B) (hz : ∀ u ∉ A, f u = 0) :
    ‖∫ u, f u‖ ≤ volume.real A * B := by
  have h := norm_integral_le_of_norm_le (fhpab4_integrable_indicator hA B)
    (Eventually.of_forall (fhpab4_norm_le_indicator hb hz))
  rwa [integral_indicator_const _ hA.measurableSet, smul_eq_mul] at h

theorem fhpab4_integrable_of_le {A : Set (Spatial m)} (hA : IsCompact A)
    {f : Spatial m → ℂ} {B : ℝ} (hf : AEStronglyMeasurable f volume)
    (hb : ∀ u ∈ A, ‖f u‖ ≤ B) (hz : ∀ u ∉ A, f u = 0) : Integrable f volume :=
  (fhpab4_integrable_indicator hA B).mono' hf
    (Eventually.of_forall (fhpab4_norm_le_indicator hb hz))

/-- Every spatial slice of a compact test is integrable. -/
theorem fhpab4_integrable_slice (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (s : ℝ) : Integrable (fun u : Spatial m => ψ (WithLp.toLp 2 (u, s))) volume :=
  fhpab4_integrable_of_le (isCompact_spatialTestSupport ψ hc)
    (ψ.continuous.comp (fhpab4_continuous_toLp s)).aestronglyMeasurable
    (B := SchwartzMap.seminorm ℝ 0 0 ψ) (fun _ _ => ψ.norm_le_seminorm ℝ _)
    (fun _ hu => fhpab4_eq_zero_of_notMem ψ hu s)

/-! ## The spatial marginal `ψ̄` -/

/-- The spatial marginal `ψ̄(s) = ∫ ψ(u,s) du`. -/
def fhpab4_marginal (ψ : 𝓢(FourierSpace m, ℂ)) (s : ℝ) : ℂ :=
  ∫ u : Spatial m, ψ (WithLp.toLp 2 (u, s))

/-- The uniform bound `vol(A) · sup ‖ψ‖` for the marginal. -/
def fhpab4_marginalBound (ψ : 𝓢(FourierSpace m, ℂ)) : ℝ :=
  volume.real (spatialTestSupport ψ) * SchwartzMap.seminorm ℝ 0 0 ψ

theorem fhpab4_marginalBound_nonneg (ψ : 𝓢(FourierSpace m, ℂ)) :
    0 ≤ fhpab4_marginalBound ψ :=
  mul_nonneg measureReal_nonneg (apply_nonneg _ _)

theorem fhpab4_norm_marginal_le (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (s : ℝ) : ‖fhpab4_marginal ψ s‖ ≤ fhpab4_marginalBound ψ :=
  fhpab4_norm_integral_le (isCompact_spatialTestSupport ψ hc)
    (fun _ _ => ψ.norm_le_seminorm ℝ _) (fun _ hu => fhpab4_eq_zero_of_notMem ψ hu s)

theorem fhpab4_marginal_eq_zero (ψ : 𝓢(FourierSpace m, ℂ)) {S : ℝ}
    (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S) {s : ℝ} (hsS : S < |s|) :
    fhpab4_marginal ψ s = 0 := by
  have hz : ∀ u : Spatial m, ψ (WithLp.toLp 2 (u, s)) = 0 :=
    fun u => fhpab4_eq_zero_of_time ψ hs u hsS
  simp only [fhpab4_marginal, hz, integral_zero]

/-- The test in ordinary coordinates is integrable for the product volume. -/
theorem fhpab4_integrable_coordinates (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ) :
    Integrable (fun p : Spatial m × ℝ => ψ (WithLp.toLp 2 p))
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
  rw [← volume_coordinates_eq_prod]
  exact (integrable_fourierCoordinates_symm_iff (ψ : FourierSpace m → ℂ)).mpr
    (ψ.continuous.integrable_of_hasCompactSupport hc)

theorem fhpab4_integrable_marginal (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ) :
    Integrable (fhpab4_marginal ψ) volume :=
  (fhpab4_integrable_coordinates ψ hc).integral_prod_right

/-- The marginal has the total integral of the test. -/
theorem fhpab4_integral_marginal (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ) :
    ∫ s, fhpab4_marginal ψ s = ∫ x, ψ x := by
  calc ∫ s, fhpab4_marginal ψ s = ∫ p : Coordinates m, ψ (WithLp.toLp 2 p) := by
        rw [volume_coordinates_eq_prod]
        exact (integral_prod_symm _ (fhpab4_integrable_coordinates ψ hc)).symm
    _ = ∫ x, ψ x := integral_fourierCoordinates_symm (ψ : FourierSpace m → ℂ)

/-! ## Checkpoint 1: product integrability and Fubini at fixed time -/

theorem fhpab4_integrand_eq (ψ : 𝓢(FourierSpace m, ℂ)) (u : Spatial m) (t h : ℝ) :
    testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h =
      ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
        (ψ (WithLp.toLp 2 (u, t)) - ψ (WithLp.toLp 2 (u, t - h))) := by
  rw [testKernelIntegrand, timeShift_toLp]

theorem fhpab4_integrand_eq_zero (ψ : 𝓢(FourierSpace m, ℂ)) {u : Spatial m}
    (hu : u ∉ spatialTestSupport ψ) (t h : ℝ) :
    testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h = 0 := by
  rw [fhpab4_integrand_eq, fhpab4_eq_zero_of_notMem ψ hu, fhpab4_eq_zero_of_notMem ψ hu,
    sub_self, mul_zero]

/-- **Checkpoint 1a.** At every fixed time the kernel integrand is integrable in `(u,h)`:
it is dominated by `1_A(u) · testKernelControl ψ · cancellationWeight h`. -/
theorem fhpab4_integrable_prod (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (t : ℝ) :
    Integrable (fun p : Spatial m × ℝ => testKernelIntegrand ψ (WithLp.toLp 2 (p.1, t)) p.2)
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
  have hA := isCompact_spatialTestSupport ψ hc
  have hmeas : Measurable fun p : Spatial m × ℝ =>
      ((WithLp.toLp 2 (p.1, t) : FourierSpace m), p.2) :=
    ((fourierCoordinatesMeasurableEquiv m).symm.measurable.comp
      (measurable_fst.prodMk measurable_const)).prodMk measurable_snd
  refine ((fhpab4_integrable_indicator hA (testKernelControl ψ)).mul_prod
    integrable_cancellationWeight).mono'
    ((stronglyMeasurable_testKernelIntegrand ψ).comp_measurable hmeas).aestronglyMeasurable ?_
  refine Eventually.of_forall fun p => ?_
  by_cases hp : p.1 ∈ spatialTestSupport ψ
  · rw [indicator_of_mem hp]
    exact norm_testKernelIntegrand_le ψ _ p.2
  · rw [indicator_of_notMem hp, zero_mul, fhpab4_integrand_eq_zero ψ hp, norm_zero]

/-- The inner spatial integral of the kernel integrand. -/
theorem fhpab4_integral_inner (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (t h : ℝ) :
    ∫ u : Spatial m, testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h =
      ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (fhpab4_marginal ψ t - fhpab4_marginal ψ (t - h)) := by
  simp_rw [fhpab4_integrand_eq]
  rw [integral_const_mul, integral_sub (fhpab4_integrable_slice ψ hc t)
    (fhpab4_integrable_slice ψ hc (t - h))]
  rfl

/-- **Checkpoint 1b. The Fubini identity for the spatial marginal**:
`∫ K(u,t) du = κ ∫ |h|^{-3/2} (ψ̄(t) - ψ̄(t-h)) dh`. -/
theorem fhpab4_marginal_kernel_eq (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (t : ℝ) :
    ∫ u : Spatial m, testKernel ψ (WithLp.toLp 2 (u, t)) =
      (FractionalKernel.kappa : ℂ) * ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
        (fhpab4_marginal ψ t - fhpab4_marginal ψ (t - h)) := by
  have hswap : (∫ u : Spatial m, ∫ h : ℝ, testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h) =
      ∫ h : ℝ, ∫ u : Spatial m, testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h :=
    integral_integral_swap (fhpab4_integrable_prod ψ hc t)
  calc ∫ u : Spatial m, testKernel ψ (WithLp.toLp 2 (u, t))
      = ∫ u : Spatial m, (FractionalKernel.kappa : ℂ) *
          ∫ h : ℝ, testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h := rfl
    _ = (FractionalKernel.kappa : ℂ) *
          ∫ u : Spatial m, ∫ h : ℝ, testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h :=
        integral_const_mul _ _
    _ = (FractionalKernel.kappa : ℂ) *
          ∫ h : ℝ, ∫ u : Spatial m, testKernelIntegrand ψ (WithLp.toLp 2 (u, t)) h := by
        rw [hswap]
    _ = _ := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun h => fhpab4_integral_inner ψ hc t h)

/-- The time integrand of the Fubini identity is integrable (it is the marginal of an
integrable product function). -/
theorem fhpab4_integrable_bracket (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (t : ℝ) :
    Integrable (fun h : ℝ => ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
      (fhpab4_marginal ψ t - fhpab4_marginal ψ (t - h))) volume :=
  (fhpab4_integrable_prod ψ hc t).integral_prod_right.congr
    (Eventually.of_forall fun h => fhpab4_integral_inner ψ hc t h)

/-! ## Checkpoint 2: global bound, cancellation tail and measurability -/

/-- The global bound: `‖∫ K(u,t) du‖ ≤ vol(A) · κ · testKernelControl ψ · ∫ cancellationWeight`. -/
theorem fhpab4_norm_marginal_kernel_le (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (t : ℝ) :
    ‖∫ u : Spatial m, testKernel ψ (WithLp.toLp 2 (u, t))‖ ≤
      volume.real (spatialTestSupport ψ) *
        (FractionalKernel.kappa * testKernelControl ψ * ∫ h, cancellationWeight h) :=
  fhpab4_norm_integral_le (isCompact_spatialTestSupport ψ hc)
    (fun _ _ => norm_testKernel_le ψ _)
    (fun _ hu => testKernel_eq_zero_of_notMem_spatialTestSupport ψ hu t)

/-- The mean-value bound for `x ↦ x^{-3/2}` on `[a, ∞)`. -/
theorem fhpab4_rpow_sub_le {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |x ^ (-3 / 2 : ℝ) - y ^ (-3 / 2 : ℝ)| ≤ (3 / 2 * a ^ (-5 / 2 : ℝ)) * |x - y| := by
  have hd : ∀ z ∈ Ici a, DifferentiableAt ℝ (fun z : ℝ => z ^ (-3 / 2 : ℝ)) z :=
    fun z hz => (Real.hasDerivAt_rpow_const (Or.inl (ha.trans_le hz).ne')).differentiableAt
  have hb : ∀ z ∈ Ici a, ‖deriv (fun z : ℝ => z ^ (-3 / 2 : ℝ)) z‖ ≤
      3 / 2 * a ^ (-5 / 2 : ℝ) := by
    intro z hz
    have hz0 : 0 < z := ha.trans_le hz
    have he : (-3 / 2 : ℝ) - 1 = -5 / 2 := by norm_num
    have h32 : |(-3 / 2 : ℝ)| = 3 / 2 := by
      rw [abs_of_neg (by norm_num)]
      norm_num
    rw [Real.deriv_rpow_const, he, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hz0 _), h32]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hz (by norm_num))
      (by norm_num)
  have h := (convex_Ici a).norm_image_sub_le_of_norm_deriv_le hd hb hy hx
  simpa only [Real.norm_eq_abs] using h

/-- The constant of the `|t|^{-5/2}` tail (`2^{5/2} = 1 / 2^{-5/2}`). -/
def fhpab4_tailConstant (ψ : 𝓢(FourierSpace m, ℂ)) (S : ℝ) : ℝ :=
  FractionalKernel.kappa * (2 * S) * (3 / 2 / (2 : ℝ) ^ (-5 / 2 : ℝ)) * S *
    fhpab4_marginalBound ψ

/-- **Checkpoint 2. The cancellation tail.** For a mean-zero compact test with time support
in `[-S,S]` and `|t| > 2S`, `‖∫ K(u,t) du‖ ≤ fhpab4_tailConstant ψ S · |t|^{-5/2}`. -/
theorem fhpab4_tail (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    (h0 : ∫ x, ψ x = 0) {S : ℝ} (hS : 0 < S)
    (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S) {t : ℝ} (ht : 2 * S < |t|) :
    ‖∫ u : Spatial m, testKernel ψ (WithLp.toLp 2 (u, t))‖ ≤
      fhpab4_tailConstant ψ S * |t| ^ (-5 / 2 : ℝ) := by
  have hSt : S < |t| := by linarith
  have hgt : fhpab4_marginal ψ t = 0 := fhpab4_marginal_eq_zero ψ hs hSt
  -- the vanishing term `|t|^{-3/2} ∫ ψ̄(t-h) dh = |t|^{-3/2} ∫ ψ = 0`
  have hH : Integrable (fun h : ℝ => ((|t| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
      fhpab4_marginal ψ (t - h)) volume :=
    ((fhpab4_integrable_marginal ψ hc).comp_sub_left t).const_mul _
  have hHz : ∫ h : ℝ, ((|t| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * fhpab4_marginal ψ (t - h) = 0 := by
    rw [integral_const_mul, integral_sub_left_eq_self (fhpab4_marginal ψ) volume t,
      fhpab4_integral_marginal ψ hc, h0, mul_zero]
  have hsplit : ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
        (fhpab4_marginal ψ t - fhpab4_marginal ψ (t - h)) =
      ∫ h : ℝ, ((|t| ^ (-3 / 2 : ℝ) - |h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
        fhpab4_marginal ψ (t - h) := by
    calc ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
          (fhpab4_marginal ψ t - fhpab4_marginal ψ (t - h))
        = (∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
            (fhpab4_marginal ψ t - fhpab4_marginal ψ (t - h))) +
          ∫ h : ℝ, ((|t| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * fhpab4_marginal ψ (t - h) := by
          rw [hHz, add_zero]
      _ = ∫ h : ℝ, (((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
            (fhpab4_marginal ψ t - fhpab4_marginal ψ (t - h)) +
          ((|t| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * fhpab4_marginal ψ (t - h)) :=
          (integral_add (fhpab4_integrable_bracket ψ hc t) hH).symm
      _ = _ := by
          congr 1
          funext h
          simp only [hgt, Complex.ofReal_sub]
          ring
  -- the pointwise bound on the support `|t - h| ≤ S`
  have hbound : ∀ h : ℝ,
      ‖((|t| ^ (-3 / 2 : ℝ) - |h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * fhpab4_marginal ψ (t - h)‖ ≤
        (Icc (t - S) (t + S)).indicator
          (fun _ => 3 / 2 * (|t| / 2) ^ (-5 / 2 : ℝ) * S * fhpab4_marginalBound ψ) h := by
    intro h
    by_cases hh : h ∈ Icc (t - S) (t + S)
    · rw [indicator_of_mem hh, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hth : |t - h| ≤ S := abs_le.mpr ⟨by linarith [hh.2], by linarith [hh.1]⟩
      have hh2 : |t| / 2 ≤ |h| := by
        have := abs_sub_abs_le_abs_sub t h
        linarith
      have hmvt := fhpab4_rpow_sub_le (by linarith : 0 < |t| / 2)
        (by linarith : |t| / 2 ≤ |t|) hh2
      have hdiff : |(|t| - |h|)| ≤ S := (abs_abs_sub_abs_le_abs_sub t h).trans hth
      calc |(|t| ^ (-3 / 2 : ℝ) - |h| ^ (-3 / 2 : ℝ))| * ‖fhpab4_marginal ψ (t - h)‖
          ≤ (3 / 2 * (|t| / 2) ^ (-5 / 2 : ℝ) * S) * fhpab4_marginalBound ψ := by
            apply mul_le_mul _ (fhpab4_norm_marginal_le ψ hc _) (norm_nonneg _)
              (by positivity)
            exact hmvt.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))
        _ = _ := by ring
    · rw [indicator_of_notMem hh]
      have hth : S < |t - h| := by
        by_contra hn
        have he := abs_le.mp (le_of_not_gt hn)
        exact hh ⟨by linarith [he.2], by linarith [he.1]⟩
      rw [fhpab4_marginal_eq_zero ψ hs hth, mul_zero, norm_zero]
  have hI := norm_integral_le_of_norm_le
    ((integrableOn_const (μ := (volume : Measure ℝ)) (s := Icc (t - S) (t + S))
      (C := 3 / 2 * (|t| / 2) ^ (-5 / 2 : ℝ) * S * fhpab4_marginalBound ψ)
      measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc)
    (Eventually.of_forall hbound)
  rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
    Real.volume_real_Icc_of_le (by linarith)] at hI
  rw [fhpab4_marginal_kernel_eq ψ hc t, hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos FractionalKernel.kappa_pos]
  calc FractionalKernel.kappa * ‖∫ h : ℝ, ((|t| ^ (-3 / 2 : ℝ) - |h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
        fhpab4_marginal ψ (t - h)‖
      ≤ FractionalKernel.kappa * ((t + S - (t - S)) *
          (3 / 2 * (|t| / 2) ^ (-5 / 2 : ℝ) * S * fhpab4_marginalBound ψ)) :=
        mul_le_mul_of_nonneg_left hI FractionalKernel.kappa_pos.le
    _ = fhpab4_tailConstant ψ S * |t| ^ (-5 / 2 : ℝ) := by
        rw [Real.div_rpow (abs_nonneg t) zero_le_two]
        unfold fhpab4_tailConstant
        ring

/-- Measurability of the marginal by parameter integration. -/
theorem fhpab4_stronglyMeasurable_marginal_kernel (ψ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable fun t : ℝ => ∫ u : Spatial m, testKernel ψ (WithLp.toLp 2 (u, t)) :=
  ((stronglyMeasurable_testKernel ψ).comp_measurable
    (fourierCoordinatesMeasurableEquiv m).symm.measurable).integral_prod_left'

/-! ## The statement -/

/-- **The marginal decay** (the type of `fhpa_spatialIntegral_testKernel_decay`): the spatially
integrated kernel of a
mean-zero real compact smooth test is a.e. strongly measurable, bounded, and has an
`|t|^{-5/2}` tail. -/
theorem fhpa_spatialIntegral_testKernel_decay_proof {m : ℕ} (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (h0 : ∫ x, φ x = 0) :
    AEStronglyMeasurable (fun t : ℝ => ∫ u : Spatial m,
        testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))) ∧
      ∃ C S : ℝ, 0 < S ∧
        (∀ t : ℝ, ‖∫ u : Spatial m,
          testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))‖ ≤ C) ∧
        ∀ t : ℝ, S < |t| →
          ‖∫ u : Spatial m, testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))‖ ≤
            C * |t| ^ (-5 / 2 : ℝ) := by
  have hcψ : HasCompactSupport (realCompactTest φ hφ hc) := by
    change IsCompact (tsupport (realCompactTest φ hφ hc))
    rw [tsupport_realCompactTest]
    exact hc
  have h0ψ : ∫ x, realCompactTest φ hφ hc x = 0 := by
    simp only [realCompactTest_apply]
    rw [integral_complex_ofReal, h0, Complex.ofReal_zero]
  obtain ⟨S, hS, hs⟩ := exists_time_support_bound (realCompactTest φ hφ hc) hcψ
  refine ⟨(fhpab4_stronglyMeasurable_marginal_kernel _).aestronglyMeasurable,
    max (volume.real (spatialTestSupport (realCompactTest φ hφ hc)) *
      (FractionalKernel.kappa * testKernelControl (realCompactTest φ hφ hc) *
        ∫ h, cancellationWeight h))
      (fhpab4_tailConstant (realCompactTest φ hφ hc) S),
    2 * S, by linarith, fun t => ?_, fun t ht => ?_⟩
  · exact (fhpab4_norm_marginal_kernel_le _ hcψ t).trans (le_max_left _ _)
  · exact (fhpab4_tail _ hcψ h0ψ hS hs ht).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg t) _))

end ParabolicRectifiability.Foundations
