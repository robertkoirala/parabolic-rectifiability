import ParabolicRectifiability.Analysis.HalfTimeDerivative.Basic
import ParabolicRectifiability.Analysis.FractionalKernel.Truncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Spectral approximation of the half-time derivative

These are inverse Fourier transforms of the scalar truncated multipliers.
No physical-space truncated-kernel identity is asserted in this module.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform

namespace ParabolicRectifiability.FractionalKernel

theorem measurable_uncurry_frequencyIntegrand :
    Measurable (fun p : ℝ × ℝ => frequencyIntegrand p.1 p.2) := by
  unfold frequencyIntegrand
  fun_prop

/-- Parameter integration against the fixed annular restriction of ordinary Lebesgue measure. -/
theorem measurable_truncatedMultiplier (j : ℕ) : Measurable (truncatedMultiplier j) := by
  have hi := measurable_uncurry_frequencyIntegrand.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (symmetricAnnulus j))
  exact measurable_const.mul hi.measurable

end ParabolicRectifiability.FractionalKernel

namespace ParabolicRectifiability.HalfTimeDerivative

open FractionalKernel

theorem measurable_truncatedSymbol (m j : ℕ) :
    Measurable (fun z : FourierSpace m => truncatedMultiplier j (timeCoordinate m z)) :=
  (measurable_truncatedMultiplier j).comp (measurable_timeCoordinate m)

theorem norm_truncated_mul_le_symbol_mul {m : ℕ} (j : ℕ) (η : 𝓢(FourierSpace m, ℂ))
    (z : FourierSpace m) :
    ‖(truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z‖ ≤ ‖(symbol z : ℂ) * η z‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (truncatedMultiplier_nonneg _ _),
    abs_of_nonneg (symbol_nonneg z)]
  exact mul_le_mul_of_nonneg_right (truncatedMultiplier_le j _) (norm_nonneg _)

theorem memLp_truncated_mul {m : ℕ} (j : ℕ) (η : 𝓢(FourierSpace m, ℂ)) :
    MemLp (fun z => (truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z)
      2 (volume : Measure (FourierSpace m)) := by
  apply (memLp_symbol_mul η).of_le
  · exact ((Complex.continuous_ofReal.measurable.comp (measurable_truncatedSymbol m j)).mul
      η.continuous.measurable).aestronglyMeasurable
  · exact Eventually.of_forall (norm_truncated_mul_le_symbol_mul j η)

/-- L² frequency class of the scalar truncated multiplier acting on a Schwartz function. -/
def truncatedWeightedLp {m : ℕ} (j : ℕ) (η : 𝓢(FourierSpace m, ℂ)) :
    Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  (memLp_truncated_mul j η).toLp (fun z => (truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z)

theorem coeFn_truncatedWeightedLp {m : ℕ} (j : ℕ) (η : 𝓢(FourierSpace m, ℂ)) :
    truncatedWeightedLp j η =ᵐ[volume]
      (fun z => (truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z) :=
  (memLp_truncated_mul j η).coeFn_toLp

theorem norm_truncatedWeightedLp_le {m : ℕ} (j : ℕ) (η : 𝓢(FourierSpace m, ℂ)) :
    ‖truncatedWeightedLp j η‖ ≤ ‖weightedLp η‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_truncatedWeightedLp j η, coeFn_weightedLp η] with z ht hw
  rw [ht, hw]
  exact norm_truncated_mul_le_symbol_mul j η z

theorem norm_truncatedWeightedLp_le_polynomial {m : ℕ} (j : ℕ) (η : 𝓢(FourierSpace m, ℂ)) :
    ‖truncatedWeightedLp j η‖ ≤ ‖(polynomialMul m η).toLp 2 volume‖ :=
  (norm_truncatedWeightedLp_le j η).trans (norm_weightedLp_le η)

@[simp] theorem truncatedWeightedLp_zero {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    truncatedWeightedLp 0 η = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_truncatedWeightedLp 0 η, Lp.coeFn_zero (ℂ) 2
    (volume : Measure (FourierSpace m))] with z hz hzero
  simp only [hz, hzero, truncatedMultiplier_zero_index, Complex.ofReal_zero, zero_mul, Pi.zero_apply]

/-- Sharp pointwise L² error majorant, using `0 ≤ M_j ≤ a`. -/
theorem norm_truncated_error_le {m : ℕ} (j : ℕ) (η : 𝓢(FourierSpace m, ℂ)) (z : FourierSpace m) :
    ‖(truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z - (symbol z : ℂ) * η z‖ ≤
      ‖(symbol z : ℂ) * η z‖ := by
  have hle : truncatedMultiplier j (timeCoordinate m z) ≤ symbol z := truncatedMultiplier_le j _
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hle),
    abs_of_nonneg (symbol_nonneg z)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith [truncatedMultiplier_nonneg j (timeCoordinate m z)]

/-- The squared error tends to zero in integral by dominated convergence, not merely pointwise. -/
theorem tendsto_integral_sq_truncated_error {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    Tendsto (fun j => ∫ z : FourierSpace m,
      ‖(truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z - (symbol z : ℂ) * η z‖ ^ 2)
      atTop (𝓝 0) := by
  let F : ℕ → FourierSpace m → ℝ := fun j z =>
    ‖(truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z - (symbol z : ℂ) * η z‖ ^ 2
  have hmeas : ∀ j, AEStronglyMeasurable (F j) volume := by
    intro j
    exact ((memLp_truncated_mul j η).aestronglyMeasurable.sub
      (memLp_symbol_mul η).aestronglyMeasurable).norm.pow 2
  have hint : Integrable (fun z => ‖(symbol z : ℂ) * η z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (memLp_symbol_mul η).aestronglyMeasurable).mp
      (memLp_symbol_mul η)
  have hbound : ∀ j, ∀ᵐ z ∂volume, ‖F j z‖ ≤ ‖(symbol z : ℂ) * η z‖ ^ 2 := by
    intro j
    apply Eventually.of_forall
    intro z
    dsimp [F]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncated_error_le j η z) 2
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun j => F j z) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro z
    have hz := ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_truncatedMultiplier (timeCoordinate m z))).mul_const (η z)
    have hh := ((hz.sub_const ((symbol z : ℂ) * η z)).norm).pow 2
    simpa [F, symbol] using hh
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (f := fun _ : FourierSpace m => (0 : ℝ))
    (fun z => ‖(symbol z : ℂ) * η z‖ ^ 2) hmeas hint hbound hlim

private theorem norm_toLp_two {m : ℕ} {f : FourierSpace m → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ = (∫ z, ‖f z‖ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp) hf]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity)]
  norm_num

theorem tendsto_truncatedWeightedLp {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    Tendsto (fun j => truncatedWeightedLp j η) atTop (𝓝 (weightedLp η)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht := (tendsto_integral_sq_truncated_error η).rpow_const_nhds_zero
    (by norm_num : (0 : ℝ) < 1 / 2)
  have heq (j : ℕ) : ‖truncatedWeightedLp j η - weightedLp η‖ =
      (∫ z : FourierSpace m, ‖(truncatedMultiplier j (timeCoordinate m z) : ℂ) * η z -
        (symbol z : ℂ) * η z‖ ^ 2) ^ (1 / 2 : ℝ) := by
    exact norm_toLp_two ((memLp_truncated_mul j η).sub (memLp_symbol_mul η))
  simp_rw [heq]
  simpa using ht

/-- Spectral approximant only; its identification with a physical truncated integral is proved
separately. -/
def spectralApproximation {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm (truncatedWeightedLp j (𝓕 ψ))

theorem fourier_spectralApproximation {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    𝓕 (spectralApproximation j ψ) = truncatedWeightedLp j (𝓕 ψ) :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).apply_symm_apply _

@[simp] theorem spectralApproximation_zero {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    spectralApproximation 0 ψ = 0 := by simp [spectralApproximation]

theorem tendsto_spectralApproximation {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    Tendsto (fun j => spectralApproximation j ψ) atTop (𝓝 (halfTimeDeriv m ψ)) :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.continuous.tendsto _ |>.comp
    (tendsto_truncatedWeightedLp (𝓕 ψ))

end ParabolicRectifiability.HalfTimeDerivative
