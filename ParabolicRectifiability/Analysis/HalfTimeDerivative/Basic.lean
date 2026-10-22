import ParabolicRectifiability.Analysis.Coordinates
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Half-time derivative on Schwartz tests

The square-root time symbol is only used as a measurable L² weight. Continuity
on Schwartz space follows by domination by the smooth polynomial `1 + τ²`.
All measures are the canonical Euclidean volume on `FourierSpace`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform

namespace ParabolicRectifiability.HalfTimeDerivative

/-- The real continuous linear time coordinate of the canonical Euclidean product. -/
def timeCoordinate (m : ℕ) : FourierSpace m →L[ℝ] ℝ :=
  WithLp.sndL 2 ℝ (Spatial m) ℝ

@[simp] theorem timeCoordinate_apply {m : ℕ} (z : FourierSpace m) :
    timeCoordinate m z = (WithLp.ofLp z).2 := rfl

@[simp] theorem timeCoordinate_toLp {m : ℕ} (u : Spatial m) (t : ℝ) :
    timeCoordinate m (WithLp.toLp 2 (u, t)) = t := rfl

theorem continuous_timeCoordinate (m : ℕ) : Continuous (timeCoordinate m) :=
  (timeCoordinate m).continuous

theorem measurable_timeCoordinate (m : ℕ) : Measurable (timeCoordinate m) :=
  (continuous_timeCoordinate m).measurable

/-- Unit vector in the time direction, including when the spatial rank is zero. -/
def timeVector (m : ℕ) : FourierSpace m := WithLp.toLp 2 (0, 1)

@[simp] theorem timeCoordinate_timeVector (m : ℕ) : timeCoordinate m (timeVector m) = 1 := rfl

theorem inner_timeVector {m : ℕ} (z : FourierSpace m) :
    inner ℝ z (timeVector m) = timeCoordinate m z := by
  simp [timeVector, WithLp.prod_inner_apply]

theorem timeCoordinate_sub_timeVector {m : ℕ} (z : FourierSpace m) (h : ℝ) :
    timeCoordinate m (z - h • timeVector m) = timeCoordinate m z - h := by
  rw [map_sub, map_smul, timeCoordinate_timeVector, smul_eq_mul, mul_one]

theorem coordinates_sub_timeVector {m : ℕ} (z : FourierSpace m) (h : ℝ) :
    WithLp.ofLp (z - h • timeVector m) =
      ((WithLp.ofLp z).1, (WithLp.ofLp z).2 - h) := by
  change ((WithLp.ofLp z).1 - h • (0 : Spatial m), (WithLp.ofLp z).2 - h • (1 : ℝ)) = _
  simp

/-- The nonsmooth, nonnegative half-time frequency symbol. -/
def symbol {m : ℕ} (z : FourierSpace m) : ℝ := |timeCoordinate m z| ^ (1 / 2 : ℝ)

theorem symbol_nonneg {m : ℕ} (z : FourierSpace m) : 0 ≤ symbol z :=
  Real.rpow_nonneg (abs_nonneg _) _

theorem continuous_symbol (m : ℕ) : Continuous (symbol (m := m)) :=
  (continuous_timeCoordinate m).abs.rpow_const (fun _ => Or.inr (by norm_num))

theorem measurable_symbol (m : ℕ) : Measurable (symbol (m := m)) :=
  (continuous_symbol m).measurable

@[simp] theorem symbol_neg {m : ℕ} (z : FourierSpace m) : symbol (-z) = symbol z := by
  simp only [symbol, map_neg, abs_neg]

theorem symbol_eq_zero_of_timeCoordinate_eq_zero {m : ℕ} {z : FourierSpace m}
    (hz : timeCoordinate m z = 0) : symbol z = 0 := by
  simp [symbol, hz]

/-- Smooth polynomial majorant; this, rather than `symbol`, multiplies Schwartz maps. -/
def polynomialWeight {m : ℕ} (z : FourierSpace m) : ℝ := 1 + (timeCoordinate m z) ^ 2

theorem polynomialWeight_nonneg {m : ℕ} (z : FourierSpace m) : 0 ≤ polynomialWeight z := by
  unfold polynomialWeight; positivity

theorem symbol_le_polynomialWeight {m : ℕ} (z : FourierSpace m) :
    symbol z ≤ polynomialWeight z := by
  by_cases hz : |timeCoordinate m z| ≤ 1
  · have hs := Real.rpow_le_rpow (abs_nonneg (timeCoordinate m z)) hz
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simp only [Real.one_rpow] at hs
    exact hs.trans (by unfold polynomialWeight; nlinarith [sq_nonneg (timeCoordinate m z)])
  · have hs := Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hz))
      (by norm_num : (1 / 2 : ℝ) ≤ 2)
    rw [Real.rpow_two, sq_abs] at hs
    exact hs.trans (by unfold polynomialWeight; linarith)

theorem polynomialWeight_hasTemperateGrowth (m : ℕ) :
    (polynomialWeight (m := m)).HasTemperateGrowth := by
  unfold polynomialWeight
  have ht := (timeCoordinate m).hasTemperateGrowth
  fun_prop

theorem complex_polynomialWeight_hasTemperateGrowth (m : ℕ) :
    (fun z : FourierSpace m => (polynomialWeight z : ℂ)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp (polynomialWeight_hasTemperateGrowth m)

/-- Continuous complex-linear multiplication by the proved smooth polynomial. -/
def polynomialMul (m : ℕ) : 𝓢(FourierSpace m, ℂ) →L[ℂ] 𝓢(FourierSpace m, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z : FourierSpace m => (polynomialWeight z : ℂ))

@[simp] theorem polynomialMul_apply {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) (z : FourierSpace m) :
    polynomialMul m η z = (polynomialWeight z : ℂ) * η z :=
  SchwartzMap.smulLeftCLM_apply_apply (complex_polynomialWeight_hasTemperateGrowth m) η z

theorem norm_symbol_mul_le_polynomialMul {m : ℕ} (η : 𝓢(FourierSpace m, ℂ))
    (z : FourierSpace m) : ‖(symbol z : ℂ) * η z‖ ≤ ‖polynomialMul m η z‖ := by
  rw [polynomialMul_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (symbol_nonneg z),
    abs_of_nonneg (polynomialWeight_nonneg z)]
  exact mul_le_mul_of_nonneg_right (symbol_le_polynomialWeight z) (norm_nonneg _)

theorem memLp_symbol_mul {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    MemLp (fun z => (symbol z : ℂ) * η z) 2 (volume : Measure (FourierSpace m)) := by
  apply ((polynomialMul m η).memLp 2 (volume : Measure (FourierSpace m))).of_le
  · exact ((Complex.continuous_ofReal.comp (continuous_symbol m)).mul η.continuous).aestronglyMeasurable
  · exact Eventually.of_forall (norm_symbol_mul_le_polynomialMul η)

/-- Frequency-side L² class, constructed using actual membership of the weighted function. -/
def weightedLp {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) : Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  (memLp_symbol_mul η).toLp (fun z => (symbol z : ℂ) * η z)

theorem coeFn_weightedLp {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    weightedLp η =ᵐ[volume] (fun z => (symbol z : ℂ) * η z) :=
  (memLp_symbol_mul η).coeFn_toLp

theorem norm_weightedLp_le {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    ‖weightedLp η‖ ≤ ‖(polynomialMul m η).toLp 2 volume‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coeFn_weightedLp η, (polynomialMul m η).coeFn_toLp 2 volume] with z hz hp
  rw [hz, hp]
  exact norm_symbol_mul_le_polynomialMul η z

def weightedLinearMap (m : ℕ) :
    𝓢(FourierSpace m, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (FourierSpace m)) where
  toFun := weightedLp
  map_add' η ξ := by
    apply Lp.ext
    filter_upwards [coeFn_weightedLp (η + ξ), coeFn_weightedLp η, coeFn_weightedLp ξ,
      Lp.coeFn_add (weightedLp η) (weightedLp ξ)] with z ha hb hc hd
    simp only [ha, hd, Pi.add_apply, hb, hc, add_apply, mul_add]
  map_smul' c η := by
    apply Lp.ext
    filter_upwards [coeFn_weightedLp (c • η), coeFn_weightedLp η,
      Lp.coeFn_smul c (weightedLp η)] with z ha hb hc
    simp only [ha, hc, Pi.smul_apply, hb, smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- The continuous complex-linear frequency weighting on the actual Schwartz topology. -/
def weightedLpCLM (m : ℕ) :
    𝓢(FourierSpace m, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (FourierSpace m)) where
  toLinearMap := weightedLinearMap m
  cont := by
    apply continuous_of_continuousAt_zero (weightedLinearMap m)
    change Tendsto (weightedLinearMap m) (𝓝 0) (𝓝 (weightedLinearMap m 0))
    rw [map_zero]
    apply squeeze_zero_norm (fun η => norm_weightedLp_le η)
    have hc := ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (FourierSpace m))).comp
      (polynomialMul m)).continuous.norm.continuousAt (x := (0 : 𝓢(FourierSpace m, ℂ)))
    have ht := hc.tendsto
    simp only [map_zero, norm_zero] at ht
    simpa only [ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply] using ht

@[simp] theorem weightedLpCLM_apply {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    weightedLpCLM m η = weightedLp η := rfl

/-- Half-time derivative on complex Schwartz tests, valued in L², using the inverse L² Fourier map. -/
def halfTimeDeriv (m : ℕ) :
    𝓢(FourierSpace m, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    weightedLpCLM m ∘L FourierTransform.fourierCLM ℂ 𝓢(FourierSpace m, ℂ)

theorem halfTimeDeriv_apply {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    halfTimeDeriv m ψ = (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm (weightedLp (𝓕 ψ)) := rfl

theorem fourier_halfTimeDeriv {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    𝓕 (halfTimeDeriv m ψ) = weightedLp (𝓕 ψ) :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).apply_symm_apply _

theorem coeFn_fourier_halfTimeDeriv {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    (𝓕 (halfTimeDeriv m ψ) : Lp ℂ 2 (volume : Measure (FourierSpace m))) =ᵐ[volume]
      (fun z => (symbol z : ℂ) * (𝓕 ψ) z) := by
  rw [fourier_halfTimeDeriv]
  exact coeFn_weightedLp _

theorem norm_halfTimeDeriv {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖halfTimeDeriv m ψ‖ = ‖weightedLp (𝓕 ψ)‖ :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.norm_map _

theorem norm_halfTimeDeriv_le {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖halfTimeDeriv m ψ‖ ≤ ‖(polynomialMul m (𝓕 ψ)).toLp 2 volume‖ := by
  rw [norm_halfTimeDeriv]
  exact norm_weightedLp_le _

/-- The Schwartz Fourier transform in the definition uses exactly the L² Fourier convention. -/
theorem toLp_fourier_compatibility {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ) (ψ.toLp 2 volume) =
      (𝓕 ψ).toLp 2 volume := SchwartzMap.toLp_fourier_eq ψ

end ParabolicRectifiability.HalfTimeDerivative
