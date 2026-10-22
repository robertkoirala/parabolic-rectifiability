import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationConvolution

/-! # Critical Sobolev localization: the near estimate of the high-pass part

The near part of `g` has `L²` norm at most `C B`, and the two multipliers `K̂` and
`|τ|^{1/2} K̂` are bounded; temporal Plancherel then gives `K *_t g₀ ∈ L²(U; H^{1/2}(ℝ))`.
In the form proved here: for an integrable kernel with `√|τ| |K̂(τ)| ≤ C_K` and a real
`w ∈ L²`, the time convolution `N = K *_t w` satisfies
* `∫ |N|² ≤ ‖K‖₁² ∫ |w|²`, and
* `b1loc_timeGagliardo N ≤ (4π² + 4) C_K² ∫ |w|²`,
by the convolution theorem `N̂ = K̂(τ) ŵ` (`b1loc_timeConvolution_fourier`), Plancherel and the
upper temporal bridge `b1loc_timeGagliardo_le_timeFourier`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-- Plancherel for a real `L²` function. -/
theorem b1loc_lintegral_sq_eq_fourier {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    ∫⁻ x, ‖H x‖ₑ ^ 2 =
      ∫⁻ ζ, ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  have hn : ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ =
      ‖realLp hH‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact congrArg _ ((Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).nnnorm_map _)
  calc ∫⁻ x, ‖H x‖ₑ ^ 2 = ∫⁻ x, ‖(realLp hH) x‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [coeFn_realLp hH] with x hx
        rw [hx, FourierAffine.enorm_complex_ofReal]
    _ = ‖realLp hH‖ₑ ^ 2 := by
        rw [FourierAffine.lintegral_enorm_sq_eq (Lp.aestronglyMeasurable _), Lp.enorm_def]
    _ = ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ ^ 2 := by rw [hn]
    _ = _ := by
        rw [Lp.enorm_def, ← FourierAffine.lintegral_enorm_sq_eq (Lp.aestronglyMeasurable _)]

/-- **Near estimate.** For integrable `K` with `√|τ| |K̂(τ)| ≤ C_K` and real `w ∈ L²`, the time
convolution `N = K *_t w` is in `L²` with `∫ |N|² ≤ ‖K‖₁² ∫ |w|²` and
`b1loc_timeGagliardo N ≤ (4π² + 4) C_K² ∫ |w|²`. -/
theorem b1loc_near_estimate {K : ℝ → ℝ} (hK : Integrable K) {CK : ℝ}
    (hCK : ∀ τ : ℝ, Real.sqrt |τ| * ‖𝓕 (fun t : ℝ => (K t : ℂ)) τ‖ ≤ CK)
    {w : FourierSpace m → ℝ} (hw : MemLp w 2 volume) :
    MemLp (fhp_timeConvolution K w) 2 volume ∧
      ∫⁻ x, ‖fhp_timeConvolution K w x‖ₑ ^ 2 ≤
        ENNReal.ofReal ((∫ t, ‖K t‖) ^ 2) * ∫⁻ x, ‖w x‖ₑ ^ 2 ∧
      b1loc_timeGagliardo (fhp_timeConvolution K w) ≤
        ENNReal.ofReal ((4 * Real.pi ^ 2 + 4) * CK ^ 2) * ∫⁻ x, ‖w x‖ₑ ^ 2 := by
  obtain ⟨hN, hF⟩ := b1loc_timeConvolution_fourier hK hw
  have hKb : ∀ τ : ℝ, ‖𝓕 (fun t : ℝ => (K t : ℂ)) τ‖ ≤ ∫ t, ‖K t‖ := by
    intro τ
    have h := Real.norm_fourier_le_integral_norm (fun t : ℝ => (K t : ℂ)) τ
    simpa only [Complex.norm_real] using h
  have hsq : ∫⁻ ζ, ‖(𝓕 (realLp hN) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 =
      ∫⁻ ζ, ‖𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2‖ₑ ^ 2 *
        ‖(𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [hF] with ζ hζ
    rw [hζ, enorm_mul, mul_pow]
  have hwt : ∫⁻ ζ, ENNReal.ofReal |(WithLp.ofLp ζ).2| *
        ‖(𝓕 (realLp hN) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 =
      ∫⁻ ζ, ENNReal.ofReal |(WithLp.ofLp ζ).2| *
        ‖𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2‖ₑ ^ 2 *
          ‖(𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [hF] with ζ hζ
    rw [hζ, enorm_mul, mul_pow, mul_assoc]
  refine ⟨hN, ?_, ?_⟩
  · rw [b1loc_lintegral_sq_eq_fourier hN, hsq, b1loc_lintegral_sq_eq_fourier hw,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ζ => ?_
    gcongr
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hKb _) 2)
  · refine (b1loc_timeGagliardo_le_timeFourier hN).trans ?_
    rw [hwt, b1loc_lintegral_sq_eq_fourier hw, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ζ => ?_
    have hpt : ENNReal.ofReal |(WithLp.ofLp ζ).2| *
        ‖𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2‖ₑ ^ 2 ≤ ENNReal.ofReal (CK ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have h := hCK (WithLp.ofLp ζ).2
      have h0 : 0 ≤ Real.sqrt |(WithLp.ofLp ζ).2| *
          ‖𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2‖ := by positivity
      calc |(WithLp.ofLp ζ).2| * ‖𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2‖ ^ 2
          = (Real.sqrt |(WithLp.ofLp ζ).2| *
              ‖𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2‖) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
        _ ≤ CK ^ 2 := pow_le_pow_left₀ h0 h 2
    calc ENNReal.ofReal (4 * Real.pi ^ 2 + 4) * (ENNReal.ofReal |(WithLp.ofLp ζ).2| *
          ‖𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2‖ₑ ^ 2 *
            ‖(𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2)
        ≤ ENNReal.ofReal (4 * Real.pi ^ 2 + 4) * (ENNReal.ofReal (CK ^ 2) *
            ‖(𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) := by
          gcongr
      _ = ENNReal.ofReal ((4 * Real.pi ^ 2 + 4) * CK ^ 2) *
            ‖(𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end ParabolicRectifiability.Characterization
