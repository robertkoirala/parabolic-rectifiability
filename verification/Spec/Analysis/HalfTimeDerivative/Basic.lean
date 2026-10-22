import Mathlib.Analysis.Fourier.LpSpace
import Spec.Analysis.Coordinates
import Spec.Basic
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Analysis.HalfTimeDerivative.Basic` used by the headline statements. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
namespace ParabolicRectifiability.HalfTimeDerivative
/-- The real continuous linear time coordinate of the canonical Euclidean product. -/
def timeCoordinate (m : ℕ) : FourierSpace m →L[ℝ] ℝ :=
  WithLp.sndL 2 ℝ (Spatial m) ℝ

/-- The nonsmooth, nonnegative half-time frequency symbol. -/
def symbol {m : ℕ} (z : FourierSpace m) : ℝ := |timeCoordinate m z| ^ (1 / 2 : ℝ)

/-- Smooth polynomial majorant; this, rather than `symbol`, multiplies Schwartz maps. -/
def polynomialWeight {m : ℕ} (z : FourierSpace m) : ℝ := 1 + (timeCoordinate m z) ^ 2

/-- Continuous complex-linear multiplication by the proved smooth polynomial. -/
def polynomialMul (m : ℕ) : 𝓢(FourierSpace m, ℂ) →L[ℂ] 𝓢(FourierSpace m, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z : FourierSpace m => (polynomialWeight z : ℂ))

theorem memLp_symbol_mul {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    MemLp (fun z => (symbol z : ℂ) * η z) 2 (volume : Measure (FourierSpace m)) := by
  sorry

/-- Frequency-side L² class, constructed using actual membership of the weighted function. -/
def weightedLp {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) : Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  (memLp_symbol_mul η).toLp (fun z => (symbol z : ℂ) * η z)

theorem coeFn_weightedLp {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    weightedLp η =ᵐ[volume] (fun z => (symbol z : ℂ) * η z) := by
  sorry

theorem norm_weightedLp_le {m : ℕ} (η : 𝓢(FourierSpace m, ℂ)) :
    ‖weightedLp η‖ ≤ ‖(polynomialMul m η).toLp 2 volume‖ := by
  sorry

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

/-- Half-time derivative on complex Schwartz tests, valued in L², using the inverse L² Fourier map. -/
def halfTimeDeriv (m : ℕ) :
    𝓢(FourierSpace m, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    weightedLpCLM m ∘L FourierTransform.fourierCLM ℂ 𝓢(FourierSpace m, ℂ)

end ParabolicRectifiability.HalfTimeDerivative
