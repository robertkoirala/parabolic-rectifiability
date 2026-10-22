import ParabolicRectifiability.Analysis.FourierAffine.Kernel
import ParabolicRectifiability.Analysis.HalfTimeDerivative.LocalRepresentation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-! # The Fourier symbol of the scale kernel and its square-function lower bound

The Fourier transform is mathlib's
unitary one, `𝓕 g ζ = ∫ 𝐞(-⟪z, ζ⟫) g z dz`, i.e. kernel `e^{-2πi(u·ξ + tτ)}`.
With `Ψ ζ = Dφ̂(ζ)(ξ, 2τ) = ξ·∇_ξ φ̂ + 2τ ∂_τ φ̂` one has `ψ̂_r(ζ) = Ψ(rξ, r²τ)`.

The lower bound uses a direct `r`-window instead of continuity and compactness of
`J`: along the curve `r ↦ (rξ, r²τ)` the function `φ̂` moves from `1` to at most
`1/2` in modulus before `r = R₁ / λ`, `λ² = |ξ|² + |τ|`, and the AM–GM inequality
converts this change into `∫ |ψ̂_r|² dr/r³ ≥ λ² / (16 R₁²)`. The constant depends
only on the fixed kernel `φ_m`, hence only on `m`; it is not uniform over kernels.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology FourierTransform ContDiff SchwartzMap

namespace ParabolicRectifiability.FourierAffine

open HalfTimeDerivative

variable {m : ℕ}

/-- Direct route to continuity of scalar multiplication; the generic instance search
through the `WithLp` product exceeds the heartbeat budget. -/
theorem continuousSMul_fourierSpace : ContinuousSMul ℝ (FourierSpace m) := by
  have : IsBoundedSMul ℝ (FourierSpace m) := NormedSpace.toIsBoundedSMul
  exact IsBoundedSMul.continuousSMul

attribute [local instance] continuousSMul_fourierSpace

/-- `φ̂`. -/
def bumpHat (m : ℕ) : FourierSpace m → ℂ := 𝓕 (fun z : FourierSpace m => (bump z : ℂ))

/-- `ψ̂_r`. -/
def scaleKernelHat (r : ℝ) : FourierSpace m → ℂ :=
  𝓕 (fun z : FourierSpace m => (scaleKernel r z : ℂ))

/-- `Ψ(ξ,τ) = ξ·∇_ξ φ̂(ξ,τ) + 2τ ∂_τ φ̂(ξ,τ)`, written as `Dφ̂(ζ)(ξ, 2τ)`. -/
def symbolGenerator (ζ : FourierSpace m) : ℂ :=
  fderiv ℝ (bumpHat m) ζ (WithLp.toLp 2 ((WithLp.ofLp ζ).1, 2 * (WithLp.ofLp ζ).2))

/-- The Schwartz test carrying `φ`. -/
def bumpTest (m : ℕ) : 𝓢(FourierSpace m, ℂ) :=
  realCompactTest bump contDiff_bump hasCompactSupport_bump

theorem bumpHat_eq_schwartz : bumpHat m = ⇑(𝓕 (bumpTest m) : 𝓢(FourierSpace m, ℂ)) :=
  (SchwartzMap.fourier_coe (bumpTest m)).symm

theorem contDiff_bumpHat : ContDiff ℝ ∞ (bumpHat m) := by
  rw [bumpHat_eq_schwartz]
  exact (𝓕 (bumpTest m) : 𝓢(FourierSpace m, ℂ)).smooth ⊤

theorem continuous_bumpHat : Continuous (bumpHat m) := contDiff_bumpHat.continuous

theorem bumpHat_zero : bumpHat m 0 = 1 := by
  rw [bumpHat, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_complex_ofReal, integral_bump, Complex.ofReal_one]

theorem inner_dilate (r : ℝ) (w ζ : FourierSpace m) :
    inner ℝ (dilate r w) ζ = inner ℝ w (dilate r ζ) := by
  simp only [WithLp.prod_inner_apply, ofLp_dilate, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, RCLike.inner_apply]
  ring

/-- Parabolic scaling of the Fourier transform of `r^(-k) g(u/r, t/r²)`. -/
theorem fourier_dilate_inv {r : ℝ} (hr : 0 < r) (g : FourierSpace m → ℝ) (ζ : FourierSpace m) :
    𝓕 (fun z : FourierSpace m => (((r ^ (m + 2))⁻¹ * g (dilate r⁻¹ z) : ℝ) : ℂ)) ζ =
      𝓕 (fun z : FourierSpace m => (g z : ℂ)) (dilate r ζ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hz : ∀ z : FourierSpace m, dilate r (dilate r⁻¹ z) = z := fun z => by
    rw [dilate_dilate, mul_inv_cancel₀ hr.ne', dilate_one]
  have hk : (r : ℂ) ^ (m + 2) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
  obtain ⟨G, hG⟩ : ∃ G : FourierSpace m → ℂ, G = fun w =>
      𝐞 (-inner ℝ (dilate r w) ζ) • ((((r ^ (m + 2))⁻¹ * g w : ℝ)) : ℂ) := ⟨_, rfl⟩
  have h1 : (fun z : FourierSpace m => 𝐞 (-inner ℝ z ζ) •
      ((((r ^ (m + 2))⁻¹ * g (dilate r⁻¹ z) : ℝ)) : ℂ)) = fun z => G (dilate r⁻¹ z) := by
    funext z
    rw [hG]
    simp only [hz]
  rw [h1, integral_comp_dilate_inv hr G, ← integral_smul]
  congr 1
  funext w
  rw [hG]
  simp only [inner_dilate, Circle.smul_def, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp

/-- Parabolic scaling of `φ̂_r`. -/
theorem fourier_kernel {r : ℝ} (hr : 0 < r) (ζ : FourierSpace m) :
    𝓕 (fun z : FourierSpace m => (kernel r z : ℂ)) ζ = bumpHat m (dilate r ζ) :=
  fourier_dilate_inv hr bump ζ

/-- `ψ̂_r(ξ,τ) = ψ̂_1(rξ, r²τ)`. -/
theorem scaleKernelHat_dilate {r : ℝ} (hr : 0 < r) (ζ : FourierSpace m) :
    scaleKernelHat r ζ = scaleKernelHat 1 (dilate r ζ) := by
  rw [scaleKernelHat, scaleKernelHat, scaleKernel_one]
  exact fourier_dilate_inv hr scaleKernelOne ζ

theorem scaleKernelHat_zero {r : ℝ} (hr : 0 < r) : scaleKernelHat r (0 : FourierSpace m) = 0 := by
  rw [scaleKernelHat, Real.fourier_eq]
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_complex_ofReal, integral_scaleKernel hr, Complex.ofReal_zero]

theorem continuous_symbolGenerator : Continuous (symbolGenerator (m := m)) := by
  have hA : Continuous fun ζ : FourierSpace m =>
      (WithLp.toLp 2 ((WithLp.ofLp ζ).1, 2 * (WithLp.ofLp ζ).2) : FourierSpace m) := by
    show Continuous fun ζ : FourierSpace m => (fourierCoordinatesHomeomorph m).symm
      (((fourierCoordinatesHomeomorph m) ζ).1, 2 * ((fourierCoordinatesHomeomorph m) ζ).2)
    exact (fourierCoordinatesHomeomorph m).symm.continuous.comp
      ((continuous_fst.comp (fourierCoordinatesHomeomorph m).continuous).prodMk
        (continuous_const.mul (continuous_snd.comp (fourierCoordinatesHomeomorph m).continuous)))
  have hD : Continuous (fderiv ℝ (bumpHat m)) := contDiff_bumpHat.continuous_fderiv (by simp)
  exact hD.clm_apply hA

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_dilate (r : ℝ) (ζ : FourierSpace m) :
    HasDerivAt (fun s => dilate s ζ)
      (WithLp.toLp 2 ((WithLp.ofLp ζ).1, 2 * r * (WithLp.ofLp ζ).2) : FourierSpace m) r := by
  have he : (fun s : ℝ => dilate s ζ) = fun s =>
      s • (WithLp.toLp 2 ((WithLp.ofLp ζ).1, 0) : FourierSpace m) +
        s ^ 2 • (WithLp.toLp 2 (0, (WithLp.ofLp ζ).2) : FourierSpace m) := by
    funext s
    apply WithLp.ofLp_injective
    ext <;> simp
  rw [he]
  have h := ((hasDerivAt_id' r).smul_const (WithLp.toLp 2 ((WithLp.ofLp ζ).1, 0) :
    FourierSpace m)).add
    ((hasDerivAt_pow 2 r).smul_const (WithLp.toLp 2 (0, (WithLp.ofLp ζ).2) : FourierSpace m))
  convert h using 1
  apply WithLp.ofLp_injective
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- `r ∂_r φ̂(rξ, r²τ) = Ψ(rξ, r²τ)`. -/
theorem hasDerivAt_bumpHat_dilate {r : ℝ} (hr : 0 < r) (ζ : FourierSpace m) :
    HasDerivAt (fun s => bumpHat m (dilate s ζ)) (symbolGenerator (dilate r ζ) / r) r := by
  have hf : HasFDerivAt (bumpHat m) (fderiv ℝ (bumpHat m) (dilate r ζ)) (dilate r ζ) :=
    ((contDiff_bumpHat.differentiable (by simp)) (dilate r ζ)).hasFDerivAt
  have h := hf.comp_hasDerivAt r (hasDerivAt_dilate r ζ)
  refine h.congr_deriv ?_
  have hv : (WithLp.toLp 2 ((WithLp.ofLp (dilate r ζ)).1, 2 * (WithLp.ofLp (dilate r ζ)).2) :
      FourierSpace m) = r • WithLp.toLp 2 ((WithLp.ofLp ζ).1, 2 * r * (WithLp.ofLp ζ).2) := by
    apply WithLp.ofLp_injective
    simp only [ofLp_dilate, WithLp.ofLp_smul, Prod.smul_mk, smul_eq_mul]
    congr 1
    ring
  rw [symbolGenerator, hv, map_smul, Complex.real_smul,
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]

/-- `ψ̂_r(ξ,τ) = Ψ(rξ, r²τ)`. -/
theorem scaleKernelHat_eq {r : ℝ} (hr : 0 < r) (ζ : FourierSpace m) :
    scaleKernelHat r ζ = symbolGenerator (dilate r ζ) := by
  have he : Continuous fun z : FourierSpace m => ((𝐞 (-inner ℝ z ζ) : Circle) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_inner.comp
      (continuous_id.prodMk continuous_const)).neg)
  have hd := hasDerivAt_integral_kernel (m := m) hr he (fun z => by simp)
  have heq : (fun s => ∫ z, ((𝐞 (-inner ℝ z ζ) : Circle) : ℂ) * (kernel s z : ℂ)) =ᶠ[𝓝 r]
      fun s => bumpHat m (dilate s ζ) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    rw [← fourier_kernel hs, Real.fourier_eq]
    simp only [Circle.smul_def, smul_eq_mul]
  have h2 := (hasDerivAt_bumpHat_dilate hr ζ).congr_of_eventuallyEq heq
  have hu := hd.unique h2
  have hk : (∫ z, ((𝐞 (-inner ℝ z ζ) : Circle) : ℂ) * (scaleKernel r z : ℂ)) =
      scaleKernelHat r ζ := by
    rw [scaleKernelHat, Real.fourier_eq]
    simp only [Circle.smul_def, smul_eq_mul]
  rw [hk] at hu
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  exact (div_left_inj' hr').mp hu

/-- Decay of `φ̂`: it is at most `1/2` in modulus outside a fixed ball. -/
theorem exists_bumpHat_small (m : ℕ) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ ζ : FourierSpace m, R₀ < ‖ζ‖ → ‖bumpHat m ζ‖ < 1 / 2 := by
  have ht : Tendsto (bumpHat m) (cocompact (FourierSpace m)) (𝓝 0) :=
    tendsto_integral_exp_inner_smul_cocompact (fun z : FourierSpace m => (bump z : ℂ))
  have hev := ht.eventually (ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  rw [Filter.Eventually, mem_cocompact] at hev
  obtain ⟨K, hK, hKs⟩ := hev
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun ζ hζ => ?_⟩
  have hn : ζ ∉ K := fun hk => by
    have := hR hk
    rw [mem_closedBall_zero_iff] at this
    linarith [le_max_left R 0]
  have := hKs hn
  simpa [mem_ball_zero_iff] using this

/-- The real AM–GM step: `a/s ≤ 2R² a²/s³ + s/(8R²)`. -/
theorem div_le_amgm {a s R : ℝ} (hs : 0 < s) (hR : 0 < R) :
    a / s ≤ 2 * R ^ 2 * (a ^ 2 / s ^ 3) + s / (8 * R ^ 2) := by
  have key : 2 * R ^ 2 * (a ^ 2 / s ^ 3) + s / (8 * R ^ 2) - a / s =
      (4 * R ^ 2 * a - s ^ 2) ^ 2 / (8 * R ^ 2 * s ^ 3) := by
    field_simp
    ring
  have hnn : 0 ≤ (4 * R ^ 2 * a - s ^ 2) ^ 2 / (8 * R ^ 2 * s ^ 3) := by positivity
  linarith

/-- The square-function lower bound
`∫_0^∞ |ψ̂_r(ξ,τ)|² dr/r³ ≥ c_m (|ξ|² + |τ|)`, with `c_m > 0` depending only on `m`. -/
theorem exists_symbol_lower_bound (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ζ : FourierSpace m,
      ENNReal.ofReal (c * (‖(WithLp.ofLp ζ).1‖ ^ 2 + |(WithLp.ofLp ζ).2|)) ≤
        ∫⁻ r in Ioi (0 : ℝ), ‖scaleKernelHat r ζ‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹ ^ 3 := by
  obtain ⟨R₀, hR₀, hsmall⟩ := exists_bumpHat_small m
  refine ⟨1 / (16 * (2 * (R₀ + 1)) ^ 2), by positivity, fun ζ => ?_⟩
  set R₁ : ℝ := 2 * (R₀ + 1) with hR₁
  have hR₁pos : 0 < R₁ := by positivity
  set L : ℝ := ‖(WithLp.ofLp ζ).1‖ ^ 2 + |(WithLp.ofLp ζ).2| with hL
  rcases (show 0 ≤ L by positivity).eq_or_lt with hL0 | hLpos
  · rw [← hL0, mul_zero, ENNReal.ofReal_zero]
    exact zero_le
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  set R : ℝ := R₁ / Real.sqrt L with hRdef
  have hRpos : 0 < R := div_pos hR₁pos hsqrt
  have hR2 : R ^ 2 = R₁ ^ 2 / L := by
    rw [hRdef, div_pow, Real.sq_sqrt hLpos.le]
  have hcurve : Continuous fun s : ℝ => dilate s ζ :=
    continuous_dilate₂.comp (continuous_id.prodMk continuous_const)
  -- The far end of the window.
  have hfar : ‖bumpHat m (dilate R ζ)‖ < 1 / 2 := by
    apply hsmall
    have hx : 0 ≤ ‖(WithLp.ofLp ζ).1‖ ^ 2 := sq_nonneg _
    have hy : 0 ≤ |(WithLp.ofLp ζ).2| := abs_nonneg _
    have hR4 : R ^ 4 = (R₁ ^ 2 / L) ^ 2 := by rw [← hR2]; ring
    have hbig : R₀ ^ 2 < ‖(WithLp.ofLp ζ).1‖ ^ 2 * R ^ 2 + (WithLp.ofLp ζ).2 ^ 2 * R ^ 4 := by
      rw [hR4, hR2, ← sq_abs (WithLp.ofLp ζ).2]
      have hA : R₀ ^ 2 < R₁ ^ 2 / 2 := by rw [hR₁]; nlinarith
      have hB : R₀ ^ 2 < R₁ ^ 4 / 4 := by rw [hR₁]; nlinarith [sq_nonneg (R₀ + 1), sq_nonneg R₀]
      rcases le_total (L / 2) (‖(WithLp.ofLp ζ).1‖ ^ 2) with hξ | hτ
      · have h1 : R₁ ^ 2 / 2 ≤ ‖(WithLp.ofLp ζ).1‖ ^ 2 * (R₁ ^ 2 / L) := by
          rw [mul_div_assoc', le_div_iff₀ hLpos]
          nlinarith [sq_nonneg R₁]
        have h2 : 0 ≤ |(WithLp.ofLp ζ).2| ^ 2 * (R₁ ^ 2 / L) ^ 2 := by positivity
        linarith
      · have hτ' : L / 2 ≤ |(WithLp.ofLp ζ).2| := by linarith
        have h1 : R₁ ^ 4 / 4 ≤ |(WithLp.ofLp ζ).2| ^ 2 * (R₁ ^ 2 / L) ^ 2 := by
          have hsq : (L / 2) ^ 2 ≤ |(WithLp.ofLp ζ).2| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hτ' 2
          have he : |(WithLp.ofLp ζ).2| ^ 2 * (R₁ ^ 2 / L) ^ 2 =
              |(WithLp.ofLp ζ).2| ^ 2 * R₁ ^ 4 / L ^ 2 := by
            field_simp
          rw [he, le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (R₁ ^ 2)]
        have h2 : 0 ≤ ‖(WithLp.ofLp ζ).1‖ ^ 2 * (R₁ ^ 2 / L) := by positivity
        linarith
    rw [← norm_sq_dilate] at hbig
    nlinarith [norm_nonneg (dilate R ζ)]
  -- The near end of the window.
  have hg : Continuous fun s : ℝ => bumpHat m (dilate s ζ) := continuous_bumpHat.comp hcurve
  have hg0 : bumpHat m (dilate 0 ζ) = 1 := by
    have : dilate 0 ζ = (0 : FourierSpace m) := by
      apply WithLp.ofLp_injective
      ext <;> simp
    rw [this, bumpHat_zero]
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hg.continuousAt (1 / 4) (by norm_num)
  set ε : ℝ := min (δ / 2) (R / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεR : ε < R := (min_le_right _ _).trans_lt (by linarith)
  have hnear : ‖bumpHat m (dilate ε ζ) - 1‖ < 1 / 4 := by
    rw [← hg0, ← dist_eq_norm]
    apply hδg
    rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]
    exact (min_le_left _ _).trans_lt (by linarith)
  -- Fundamental theorem of calculus on `[ε, R]`.
  have hΨc : Continuous fun s : ℝ => symbolGenerator (dilate s ζ) :=
    continuous_symbolGenerator.comp hcurve
  have hderiv : ∀ s ∈ uIcc ε R, HasDerivAt (fun s => bumpHat m (dilate s ζ))
      (symbolGenerator (dilate s ζ) / s) s := fun s hs => by
    rw [uIcc_of_le hεR.le] at hs
    exact hasDerivAt_bumpHat_dilate (hεpos.trans_le hs.1) ζ
  have hcont : ContinuousOn (fun s : ℝ => symbolGenerator (dilate s ζ) / (s : ℂ)) (uIcc ε R) := by
    refine hΨc.continuousOn.div Complex.continuous_ofReal.continuousOn fun s hs => ?_
    rw [uIcc_of_le hεR.le] at hs
    exact Complex.ofReal_ne_zero.mpr (hεpos.trans_le hs.1).ne'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  -- Lower bound for the change of `φ̂` along the window.
  have hchange : (1 / 4 : ℝ) ≤ ‖bumpHat m (dilate R ζ) - bumpHat m (dilate ε ζ)‖ := by
    have h1 : (1 : ℂ) = (1 - bumpHat m (dilate ε ζ)) +
        (bumpHat m (dilate ε ζ) - bumpHat m (dilate R ζ)) + bumpHat m (dilate R ζ) := by ring
    have h3 : ‖(1 : ℂ)‖ ≤ ‖1 - bumpHat m (dilate ε ζ)‖ +
        ‖bumpHat m (dilate ε ζ) - bumpHat m (dilate R ζ)‖ + ‖bumpHat m (dilate R ζ)‖ := by
      conv_lhs => rw [h1]
      exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    rw [norm_one, norm_sub_rev (1 : ℂ) (bumpHat m (dilate ε ζ)),
      norm_sub_rev (bumpHat m (dilate ε ζ)) (bumpHat m (dilate R ζ))] at h3
    linarith
  have hI : ENNReal.ofReal (1 / 4) ≤
      ∫⁻ s in Ioc ε R, ‖symbolGenerator (dilate s ζ) / (s : ℂ)‖ₑ := by
    calc ENNReal.ofReal (1 / 4)
        ≤ ‖bumpHat m (dilate R ζ) - bumpHat m (dilate ε ζ)‖ₑ := by
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hchange
      _ = ‖∫ s in ε..R, symbolGenerator (dilate s ζ) / (s : ℂ)‖ₑ := by rw [hftc]
      _ ≤ _ := by
          rw [intervalIntegral.integral_of_le hεR.le]
          exact enorm_integral_le_lintegral_enorm _
  -- AM–GM under the integral.
  have hmeasΨ : Measurable fun s : ℝ => ‖symbolGenerator (dilate s ζ)‖ₑ ^ 2 *
      (ENNReal.ofReal s)⁻¹ ^ 3 :=
    (hΨc.measurable.enorm.pow_const 2).mul (ENNReal.measurable_ofReal.inv.pow_const 3)
  have hpoint : ∀ s ∈ Ioc ε R, ‖symbolGenerator (dilate s ζ) / (s : ℂ)‖ₑ ≤
      ENNReal.ofReal (2 * R ^ 2) * (‖symbolGenerator (dilate s ζ)‖ₑ ^ 2 *
        (ENNReal.ofReal s)⁻¹ ^ 3) + ENNReal.ofReal (R / (8 * R ^ 2)) := by
    intro s hs
    have hs0 : 0 < s := hεpos.trans hs.1
    have hnorm : ‖symbolGenerator (dilate s ζ) / (s : ℂ)‖ₑ =
        ENNReal.ofReal (‖symbolGenerator (dilate s ζ)‖ / s) := by
      rw [← ofReal_norm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have hsq : ‖symbolGenerator (dilate s ζ)‖ₑ ^ 2 * (ENNReal.ofReal s)⁻¹ ^ 3 =
        ENNReal.ofReal (‖symbolGenerator (dilate s ζ)‖ ^ 2 / s ^ 3) := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hs0.le,
        ENNReal.inv_pow]
    rw [hnorm, hsq, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 := div_le_amgm (a := ‖symbolGenerator (dilate s ζ)‖) hs0 hRpos
    have h2 : s / (8 * R ^ 2) ≤ R / (8 * R ^ 2) :=
      div_le_div_of_nonneg_right hs.2 (by positivity)
    linarith
  set J := ∫⁻ s in Ioi (0 : ℝ), ‖scaleKernelHat s ζ‖ₑ ^ 2 * (ENNReal.ofReal s)⁻¹ ^ 3 with hJ
  have hupper : ∫⁻ s in Ioc ε R, ‖symbolGenerator (dilate s ζ) / (s : ℂ)‖ₑ ≤
      ENNReal.ofReal (2 * R ^ 2) * J + ENNReal.ofReal (1 / 8) := by
    calc ∫⁻ s in Ioc ε R, ‖symbolGenerator (dilate s ζ) / (s : ℂ)‖ₑ
        ≤ ∫⁻ s in Ioc ε R, (ENNReal.ofReal (2 * R ^ 2) * (‖symbolGenerator (dilate s ζ)‖ₑ ^ 2 *
            (ENNReal.ofReal s)⁻¹ ^ 3) + ENNReal.ofReal (R / (8 * R ^ 2))) :=
          setLIntegral_mono' measurableSet_Ioc hpoint
      _ = ENNReal.ofReal (2 * R ^ 2) * (∫⁻ s in Ioc ε R, ‖symbolGenerator (dilate s ζ)‖ₑ ^ 2 *
            (ENNReal.ofReal s)⁻¹ ^ 3) + ENNReal.ofReal (R / (8 * R ^ 2)) * volume (Ioc ε R) := by
          rw [lintegral_add_left (hmeasΨ.const_mul _), lintegral_const_mul _ hmeasΨ,
            setLIntegral_const]
      _ ≤ _ := by
          gcongr
          · calc ∫⁻ s in Ioc ε R, ‖symbolGenerator (dilate s ζ)‖ₑ ^ 2 * (ENNReal.ofReal s)⁻¹ ^ 3
                = ∫⁻ s in Ioc ε R, ‖scaleKernelHat s ζ‖ₑ ^ 2 * (ENNReal.ofReal s)⁻¹ ^ 3 :=
                  setLIntegral_congr_fun measurableSet_Ioc fun s hs => by
                    rw [scaleKernelHat_eq (hεpos.trans hs.1)]
              _ ≤ J := lintegral_mono_set fun s hs => hεpos.trans hs.1
          · rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
  -- Conclude.
  have h8 : ENNReal.ofReal (1 / 8) ≤ ENNReal.ofReal (2 * R ^ 2) * J := by
    have e : ENNReal.ofReal (1 / 4) = ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    have hfin := hI.trans hupper
    rw [e] at hfin
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hfin
  have hR2pos : 0 < 2 * R ^ 2 := by positivity
  calc ENNReal.ofReal (1 / (16 * R₁ ^ 2) * L)
      = ENNReal.ofReal (1 / (2 * R ^ 2)) * ENNReal.ofReal (1 / 8) := by
        rw [← ENNReal.ofReal_mul (by positivity), hR2]
        congr 1
        field_simp
        ring
    _ ≤ ENNReal.ofReal (1 / (2 * R ^ 2)) * (ENNReal.ofReal (2 * R ^ 2) * J) := by gcongr
    _ = J := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hR2pos.ne',
          ENNReal.ofReal_one, one_mul]

end ParabolicRectifiability.FourierAffine
