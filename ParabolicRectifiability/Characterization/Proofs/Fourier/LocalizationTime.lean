import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationFar

/-! # Critical Sobolev localization: the temporal Gagliardo estimate

The analytic core of `ba1_critical_sobolev_localization_proof`: for the localized function
`H = χ_{x₀} (F ∘ Ψ - F(p₀))` (`b1loc_localized`),

`∫_0^∞ s^{-2} ∫ |H(x + s e_t) - H(x)|² dx ds ≤ C_m (L² + B²)`.

**Proof**, assembled from:
* the decomposition `G - F(p₀) = A + N + V∞` a.e. (`b1loc_decomposition`), multiplied by
  `χ_{x₀}`;
* the splitting rule `b1loc_timeGagliardo_le_add3` (`χ A, χ N ∈ L²`);
* the low-pass estimate `b1loc_lowPass_estimate`: `≤ C L²`;
* the near input `b1loc_near_input`: `≤ C B²`;
* the far input `b1loc_far_input`: `≤ C B²`, from the far estimate `b1loc_far_estimate`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

/-- The temporal Gagliardo estimate of the localized function: there is `C = C_m > 0` such that
for every parabolic `L`-Lipschitz `F` on `Space m` with half-time derivative representative `f`
of real parabolic BMO bound `B`, and every centre `p₀`,
`b1loc_timeGagliardo (b1loc_localized m F p₀) ≤ C (L² + B²)`. Hypotheses: the BMO growth
statement and the two high-pass statements. -/
theorem b1loc_timeGagliardo_localized_le (hBMO : BMOGrowthStatement)
    (hK : HighPassKernelStatement) (hI : HighPassIdentityStatement) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ),
      LipschitzWith L F → HasStandardParabolicBMOBound m f B →
      RepresentsStandardHalfTimeDerivative m F f → ∀ p₀ : Space m,
        b1loc_timeGagliardo (b1loc_localized m F p₀) ≤
          ENNReal.ofReal (C * ((L : ℝ) ^ 2 + B ^ 2)) := by
  obtain ⟨Clow, hClow, hlow⟩ := b1loc_lowPass_estimate m
  obtain ⟨Cnear, hCnear, hnear⟩ := b1loc_near_input hBMO hK m
  obtain ⟨Cfar, hCfar, hfar⟩ := b1loc_far_input hBMO hK m
  refine ⟨3 * (Clow + Cnear + Cfar) + 1, by linarith, fun F f L B hL hB hrep p₀ => ?_⟩
  have hint := (b1loc_highPass_coordinates hI b1loc_cutoff b1loc_cutoff_admissible m F f L B
    hL hB hrep).1
  obtain ⟨hAm, hAg⟩ := hlow F L hL p₀ hint
  obtain ⟨hNm, hNg⟩ := hnear f B hB p₀
  have hVg := hfar f B hB p₀
  have hH : b1loc_localized m F p₀ =ᵐ[volume] fun x =>
      b1loc_cut ((fourierToParabolic m).symm p₀) x * b1loc_lowPass m F p₀ x +
        b1loc_cut ((fourierToParabolic m).symm p₀) x *
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x +
        b1loc_cut ((fourierToParabolic m).symm p₀) x *
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x := by
    filter_upwards [b1loc_decomposition hK hI hL hB hrep p₀] with x hx
    rw [b1loc_localized, hx]
    ring
  have hL0 : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  have hB0 : 0 ≤ B ^ 2 := sq_nonneg _
  calc b1loc_timeGagliardo (b1loc_localized m F p₀)
      ≤ ENNReal.ofReal 3 *
          (b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
              b1loc_lowPass m F p₀ x) +
            b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
              fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_nearPart m f p₀) x) +
            b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
              fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
                (b1loc_farPart m f p₀) x)) :=
        b1loc_timeGagliardo_le_add3 hAm hNm hH
    _ ≤ ENNReal.ofReal 3 * (ENNReal.ofReal (Clow * (L : ℝ) ^ 2) +
          ENNReal.ofReal (Cnear * B ^ 2) + ENNReal.ofReal (Cfar * B ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (3 * (Clow * (L : ℝ) ^ 2 + Cnear * B ^ 2 + Cfar * B ^ 2)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hClow hL0) (mul_nonneg hCnear hB0),
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hClow hL0) (mul_nonneg hCnear hB0))
            (mul_nonneg hCfar hB0),
          ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal ((3 * (Clow + Cnear + Cfar) + 1) * ((L : ℝ) ^ 2 + B ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg hClow hB0, mul_nonneg hCnear hL0, mul_nonneg hCfar hL0]

end ParabolicRectifiability.Characterization
