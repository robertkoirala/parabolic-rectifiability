import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationTime

/-! # Critical Sobolev localization: assembly

This file proves `ba1_critical_sobolev_localization_proof`: the statement
`CriticalSobolevLocalizationStatement`, in its quantitative unit-scale form, follows from
`BMOGrowthStatement`, `HighPassKernelStatement` and `HighPassIdentityStatement`. A parabolic
`L`-Lipschitz function `F` whose half-time derivative has a representative `f` of parabolic BMO
bound `B` is localized near `p₀` to a function `H ∈ L²` that agrees with `F - F(p₀)` on a parabolic
ball and has parabolic Fourier energy at most `C (L² + B²)`.

The witness is `H = χ_{x₀} (F ∘ Ψ - F(p₀))` (`b1loc_localized`), and the energy splits as
`∫ |H|² + ∫ |ξ|² |Ĥ|² + ∫ |τ| |Ĥ|²`:
* `∫ |H|² ≤ 49 V L²` and `∫ |ξ|² |Ĥ|² ≤ 4 m V L²` (`b1loc_lintegral_localized_sq_le`,
  `b1loc_spatial_energy_le`);
* `8 ∫ |τ| |Ĥ|² ≤ b1loc_timeGagliardo H` (`b1loc_timeFourier_le_timeGagliardo`), and
  `b1loc_timeGagliardo H ≤ C₂ (L² + B²)` (`b1loc_timeGagliardo_localized_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-- The parabolic Fourier energy is the sum of its spatial and temporal parts. -/
theorem b1loc_parabolicFourierEnergy_eq {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    parabolicFourierEnergy hH =
      (∫⁻ ζ, ENNReal.ofReal (‖(WithLp.ofLp ζ).1‖ ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) +
        ∫⁻ ζ, ENNReal.ofReal |(WithLp.ofLp ζ).2| *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  unfold parabolicFourierEnergy
  simp_rw [add_mul]
  refine lintegral_add_left ?_ _
  exact (((continuous_fst.comp (WithLp.prod_continuous_ofLp _ _ _)).norm.pow 2).measurable.ennreal_ofReal).mul
    ((Lp.stronglyMeasurable _).measurable.enorm.pow_const 2)

/-- **Critical Sobolev localization**, in implication form over the BMO growth statement and the
two high-pass statements. -/
theorem ba1_critical_sobolev_localization_proof (hBMO : BMOGrowthStatement)
    (hK : HighPassKernelStatement) (hI : HighPassIdentityStatement) :
    CriticalSobolevLocalizationStatement := by
  intro m
  obtain ⟨C₂, hC₂, hT⟩ := b1loc_timeGagliardo_localized_le hBMO hK hI m
  have hV := b1loc_ballVolume_nonneg m
  refine ⟨49 * b1loc_ballVolume m + 4 * m * b1loc_ballVolume m + C₂, by positivity, ?_⟩
  intro F f L B hL hB hrep p₀
  refine ⟨b1loc_localized m F p₀, b1loc_memLp_localized hL p₀,
    fun x hx => b1loc_localized_eq (F := F) p₀ x hx, ?_⟩
  have h0 := b1loc_lintegral_localized_sq_le hL p₀
  have h1 := b1loc_spatial_energy_le hL p₀
  have h2 := (b1loc_timeFourier_le_timeGagliardo (b1loc_memLp_localized hL p₀)).trans
    (hT F f L B hL hB hrep p₀)
  have hTime : ∫⁻ ζ, ENNReal.ofReal |(WithLp.ofLp ζ).2| *
        ‖(𝓕 (realLp (b1loc_memLp_localized hL p₀)) :
          Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 ≤
      ENNReal.ofReal (C₂ * ((L : ℝ) ^ 2 + B ^ 2)) := by
    refine le_trans ?_ h2
    refine le_mul_of_one_le_left (zero_le) ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hLB : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 + B ^ 2 := le_add_of_nonneg_right (sq_nonneg B)
  have hL2 := sq_nonneg (L : ℝ)
  have hB2 := sq_nonneg B
  rw [b1loc_parabolicFourierEnergy_eq]
  calc _ ≤ ENNReal.ofReal (49 * b1loc_ballVolume m * (L : ℝ) ^ 2) +
        (ENNReal.ofReal (4 * m * b1loc_ballVolume m * (L : ℝ) ^ 2) +
          ENNReal.ofReal (C₂ * ((L : ℝ) ^ 2 + B ^ 2))) := add_le_add h0 (add_le_add h1 hTime)
    _ ≤ ENNReal.ofReal (49 * b1loc_ballVolume m * ((L : ℝ) ^ 2 + B ^ 2)) +
        (ENNReal.ofReal (4 * m * b1loc_ballVolume m * ((L : ℝ) ^ 2 + B ^ 2)) +
          ENNReal.ofReal (C₂ * ((L : ℝ) ^ 2 + B ^ 2))) := by
        gcongr
    _ = ENNReal.ofReal ((49 * b1loc_ballVolume m + 4 * m * b1loc_ballVolume m + C₂) *
          ((L : ℝ) ^ 2 + B ^ 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end ParabolicRectifiability.Characterization
