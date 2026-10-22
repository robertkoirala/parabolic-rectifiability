import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationFarTools

/-! # Critical Sobolev localization: the far part

Part of the proof of `ba1_critical_sobolev_localization_proof`. With
`K = I - η * I` for the fixed cutoff, `w∞ = 1_{Ωᶜ} (g - c)` (`b1loc_farPart`) and
`V∞ = K *_t w∞`, the far estimate is

`LGag(V∞) + ∫_{B(x₀,7)} |V∞|² ≤ C B²`.

**Proof.** For `x ∈ B(x₀,7)` the integrand of `V∞(x)` vanishes for `|r| ≤ 93`
(`Ψ(x - r e_t) ∈ P(p₀,10)`); for `|r| ≥ 93` the tails of `b1loc_kernel_adapter`
(`|K| + |K'| ≤ C_N |t|^{-N}`, `|t| ≥ 1`) and the mean value theorem on `[r, r + s]` give
`|V∞(x)|, s⁻¹ |V∞(x + s e_t) - V∞(x)| ≤ W(x) = D ∫_{|r| ≥ 93} |r|^{-N} |w∞(x - r e_t)| dr`
(after the substitution `r ↦ r + s`, for a.e. `x`), so `LGag(V∞) + ∫_{B(x₀,7)} |V∞|² ≤
2 ∫_{B(x₀,7)} W²`; Cauchy–Schwarz in `r` with the weight `|r|^{-2}`, Tonelli, translation
invariance and clause 3 of `BMOGrowthStatement` on `P(p₀, 10 + |r|) ⊇ Ψ(B(x₀,7) - r e_t)` give
`∫_{B(x₀,7)} W² ≤ C B²` for `N = m + 8` (`b1loc_far_W_L2`).

`b1loc_far_input` turns the far estimate into the cutoff form used by the assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-- **Far estimate.** `LGag(V∞) + ∫_{B(x₀,7)} |V∞|² ≤ C B²`, with `C` depending only on `m` and
the fixed cutoff. -/
theorem b1loc_far_estimate (hBMO : BMOGrowthStatement) (hK : HighPassKernelStatement)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Space m → ℝ) (B : ℝ), HasStandardParabolicBMOBound m f B →
      ∀ p₀ : Space m,
        b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
            (fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)) +
          ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
              (b1loc_farPart m f p₀) x‖ₑ ^ 2 ≤
          ENNReal.ofReal (C * B ^ 2) := by
  obtain ⟨Cb, hCb, hb⟩ := hBMO m
  obtain ⟨D, hD0, hD⟩ := b1loc_kernel_far_bounds hK (m + 8)
  obtain ⟨-, hKint, -⟩ := hK b1loc_cutoff b1loc_cutoff_admissible
  set T := (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)).toReal with hTdef
  have hTe : ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r) = ENNReal.ofReal T :=
    (ENNReal.ofReal_toReal b1loc_lintegral_farA_lt_top.ne).symm
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hK1 : 0 ≤ D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg D) hCb.le) (b1loc_Vm_nonneg m))
      (by positivity)
  refine ⟨2 * (T * (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * T)),
    mul_nonneg (by norm_num) (mul_nonneg hT0 (mul_nonneg hK1 hT0)), fun f B hB p₀ => ?_⟩
  have h3 : ∀ R : ℝ, 10 ≤ R →
      ∫⁻ q in Metric.ball p₀ R, ‖f q - standardBallAverage m f p₀ 10‖ₑ ^ 2
          ∂parabolicVolume m ≤
        ENNReal.ofReal (Cb * B ^ 2 * (1 + Real.log (R / 10)) ^ 2) *
          parabolicVolume m (Metric.ball p₀ R) :=
    fun R hR => (hb f B hB).2.2 p₀ 10 R (by norm_num) hR
  have hKB : 0 ≤ D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2 :=
    mul_nonneg hK1 (sq_nonneg B)
  calc b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
          (fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)) +
        ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
          ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
            (b1loc_farPart m f p₀) x‖ₑ ^ 2
      ≤ 2 * ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
          b1loc_farMajorant D m f p₀ x ^ 2 := b1loc_far_energy_le_W hD hKint.1 hB p₀
    _ ≤ 2 * ((∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
          (ENNReal.ofReal (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2) *
            ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r))) :=
        mul_le_mul_of_nonneg_left (b1loc_far_W_L2 hD0 hCb.le hB p₀ h3) zero_le
    _ = ENNReal.ofReal (2 * (T * (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * T)) * B ^ 2) := by
        rw [hTe, ← ENNReal.ofReal_mul hKB, ← ENNReal.ofReal_mul hT0,
          show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- **Far input.** `b1loc_timeGagliardo (χ_{x₀} V∞) ≤ C B²`. -/
theorem b1loc_far_input (hBMO : BMOGrowthStatement) (hK : HighPassKernelStatement) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Space m → ℝ) (B : ℝ), HasStandardParabolicBMOBound m f B →
      ∀ p₀ : Space m,
        b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
          fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x) ≤
          ENNReal.ofReal (C * B ^ 2) := by
  obtain ⟨C, hC0, hfar⟩ := b1loc_far_estimate hBMO hK m
  obtain ⟨-, hKint, -⟩ := hK b1loc_cutoff b1loc_cutoff_admissible
  refine ⟨6 * C, by linarith, fun f B hB p₀ => ?_⟩
  calc b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
        fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x)
      ≤ ENNReal.ofReal 2 * b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
            (fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)) +
          ENNReal.ofReal 6 * ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
              (b1loc_farPart m f p₀) x‖ₑ ^ 2 :=
        b1loc_timeGagliardo_cut_mul_le _ (b1loc_aestronglyMeasurable_timeConvolution' hKint.1
          (b1loc_aestronglyMeasurable_farPart hB p₀))
    _ ≤ ENNReal.ofReal 6 * (b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
            (fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)) +
          ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
              (b1loc_farPart m f p₀) x‖ₑ ^ 2) := b1loc_two_six_le _ _
    _ ≤ ENNReal.ofReal 6 * ENNReal.ofReal (C * B ^ 2) :=
        mul_le_mul_of_nonneg_left (hfar f B hB p₀) zero_le
    _ = ENNReal.ofReal (6 * C * B ^ 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end ParabolicRectifiability.Characterization
