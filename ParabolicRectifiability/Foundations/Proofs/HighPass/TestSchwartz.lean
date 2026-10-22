import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.HighPassMultipliers

/-! # The high-pass test is Schwartz and has finite weighted norm

Proof of `fhpbc_b2_testSchwartz`, in implication form over the three statements the type itself
contains: `FhpbcKernelFactsStatement`, `FhpbcTimeConvolutionStatement` and
`FhpbcSchwartzNormFiniteStatement`.

Route (Fourier). For an admissible cutoff `η` the complete multiplier
`M̃(ξ,τ) = (1 - η̂(τ)) |τ|^{-1/2}` has temperate growth
(`fhpbb2s_hasTemperateGrowth_highPassMultiplier`), so
`Θ = 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ M̃ (𝓕 φ_ℂ))` is a Schwartz function with `𝓕 Θ = M̃ φ̂`.
The kernel facts give `K̂(τ) = M̃(τ)` for `τ ≠ 0`, and at `τ = 0` both vanish (`K̂(0) = ∫ K = 0`
and `η̂(0) = 1`). The time-convolution statement gives `𝓕 (K *_t φ) = K̂(τ) φ̂`, continuity and
integrability of `K *_t φ`, so Fourier inversion (`Continuous.fourierInv_fourier_eq`) identifies
`K *_t φ` with `Θ` at **every** point. Finally `Θ = ofReal ∘ (K *_t φ)` has the same weighted norm
as `K *_t φ` (the time derivatives have equal norms), which is finite by `FhpbcSchwartzNormFiniteStatement`.

Helpers carry the prefix `fhpbb2s_`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Proof-only shortcut, as in the construction of `testKernel`: the default
instance search for `ContinuousSMul ℝ (FourierSpace m)` exceeds the heartbeat budget. -/
local instance fhpbb2s_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-! ## Schwartz-side constructions -/

/-- The complete high-pass multiplier `M̃(ξ,τ) = (1 - η̂(τ)) |τ|^{-1/2}` on `FourierSpace m`, with
`η̂ = 𝓕 (fun t => (η t : ℂ))` (Mathlib's phase) and `τ = (WithLp.ofLp ζ).2`. -/
def fhpbb2s_multiplier (η : 𝓢(ℝ, ℝ)) (m : ℕ) (ζ : FourierSpace m) : ℂ :=
  (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) (WithLp.ofLp ζ).2) *
    ((|(WithLp.ofLp ζ).2| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- For an admissible cutoff the complete multiplier has temperate growth. -/
theorem fhpbb2s_multiplier_hasTemperateGrowth {η : 𝓢(ℝ, ℝ)} (hη : fhp_IsFrequencyCutoff η)
    (m : ℕ) : (fhpbb2s_multiplier η m).HasTemperateGrowth :=
  fhpbb2s_hasTemperateGrowth_highPassMultiplier hη.2.1 hη.2.2.1 hη.2.2.2 m

/-- The complexification of a real compact smooth function as a Schwartz map. -/
def fhpbb2s_complexTest {m : ℕ} {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) : 𝓢(FourierSpace m, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (φ x : ℂ))
    (hφc.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hφ)

theorem fhpbb2s_coe_complexTest {m : ℕ} {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (fhpbb2s_complexTest hφ hφc : FourierSpace m → ℂ) = fun x => (φ x : ℂ) :=
  rfl

/-- The candidate Schwartz realization `Θ = 𝓕⁻ (M̃ · 𝓕 φS)`. -/
def fhpbb2s_highPassTest (η : 𝓢(ℝ, ℝ)) {m : ℕ} (φS : 𝓢(FourierSpace m, ℂ)) :
    𝓢(FourierSpace m, ℂ) :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (fhpbb2s_multiplier η m) (𝓕 φS))

/-- `𝓕 Θ = M̃ · 𝓕 φS` pointwise (Schwartz Fourier inversion and the temperate multiplier). -/
theorem fhpbb2s_fourier_highPassTest_apply {η : 𝓢(ℝ, ℝ)} {m : ℕ}
    (hM : (fhpbb2s_multiplier η m).HasTemperateGrowth) (φS : 𝓢(FourierSpace m, ℂ))
    (ζ : FourierSpace m) :
    𝓕 (fhpbb2s_highPassTest η φS : FourierSpace m → ℂ) ζ =
      fhpbb2s_multiplier η m ζ * 𝓕 (φS : FourierSpace m → ℂ) ζ := by
  have h : (𝓕 (fhpbb2s_highPassTest η φS)) ζ = fhpbb2s_multiplier η m ζ * (𝓕 φS) ζ := by
    rw [fhpbb2s_highPassTest, FourierTransform.fourier_fourierInv_eq,
      SchwartzMap.smulLeftCLM_apply_apply hM, smul_eq_mul]
  exact h

/-! ## Fourier inversion and the kernel transform at every frequency -/

/-- Fourier inversion against a Schwartz function: a continuous integrable `f` with the same
Fourier transform as a Schwartz `Θ` equals `Θ` everywhere. -/
theorem fhpbb2s_coe_eq_of_fourier_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (Θ : 𝓢(V, ℂ)) {f : V → ℂ} (hfc : Continuous f) (hfi : Integrable f)
    (hF : 𝓕 f = 𝓕 (Θ : V → ℂ)) : (Θ : V → ℂ) = f := by
  have hΘF : Integrable (𝓕 (Θ : V → ℂ)) := (𝓕 Θ).integrable
  have hFi : Integrable (𝓕 f) := by rw [hF]; exact hΘF
  rw [← hfc.fourierInv_fourier_eq hfi hFi, hF]
  exact (Θ.continuous.fourierInv_fourier_eq Θ.integrable hΘF).symm

/-- The kernel facts give `K̂(τ) = (1 - η̂(τ)) |τ|^{-1/2}` for **every** `τ`: for `τ ≠ 0` this is
the transform clause, and at `τ = 0` both sides vanish (`K̂(0) = ∫ K = 0`, `η̂(0) = 1`). -/
theorem fhpbb2s_fourier_highPassKernel_eq (hK : FhpbcKernelFactsStatement) {η : 𝓢(ℝ, ℝ)}
    (hη : fhp_IsFrequencyCutoff η) (τ : ℝ) :
    𝓕 (fun t : ℝ => (fhp_highPassKernel η t : ℂ)) τ =
      (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  obtain ⟨-, -, hmean, -, -, -, hfour⟩ := hK η hη
  rcases eq_or_ne τ 0 with rfl | hτ
  · have h0 : 𝓕 (fun t : ℝ => (fhp_highPassKernel η t : ℂ)) 0 =
        ∫ t : ℝ, (fhp_highPassKernel η t : ℂ) := by
      rw [Real.fourier_real_eq]
      simp
    rw [h0, integral_complex_ofReal, hmean, fhpbb2s_one_sub_apply_zero hη.2.2.2, zero_mul,
      Complex.ofReal_zero]
  · exact hfour τ hτ

/-! ## The pointwise Schwartz realization -/

/-- **Pointwise realization.** For an admissible cutoff and a real compact smooth `φ`, the
Schwartz function `Θ = 𝓕⁻ (M̃ · 𝓕 φ_ℂ)` equals `K *_t φ` at every point. -/
theorem fhpbb2s_highPassTest_eq (hK : FhpbcKernelFactsStatement)
    (hC : FhpbcTimeConvolutionStatement) {η : 𝓢(ℝ, ℝ)} (hη : fhp_IsFrequencyCutoff η) {m : ℕ}
    {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (x : FourierSpace m) :
    fhpbb2s_highPassTest η (fhpbb2s_complexTest hφ hφc) x =
      (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ) := by
  obtain ⟨-, hKint, -, -, -, -, -⟩ := hK η hη
  obtain ⟨hψs, -, hψi, -, hψF⟩ := hC (fhp_highPassKernel η) hKint m φ hφ hφc
  have hM := fhpbb2s_multiplier_hasTemperateGrowth hη m
  have hcont : Continuous
      (fun x : FourierSpace m => (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) :=
    Complex.continuous_ofReal.comp hψs.continuous
  have hint : Integrable
      (fun x : FourierSpace m => (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) :=
    hψi.ofReal
  have hF : 𝓕 (fun x : FourierSpace m => (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) =
      𝓕 (fhpbb2s_highPassTest η (fhpbb2s_complexTest hφ hφc) : FourierSpace m → ℂ) := by
    funext ζ
    rw [fhpbb2s_fourier_highPassTest_apply hM, hψF ζ, fhpbb2s_fourier_highPassKernel_eq hK hη,
      fhpbb2s_coe_complexTest, fhpbb2s_multiplier]
  exact congrFun (fhpbb2s_coe_eq_of_fourier_eq _ hcont hint hF) x

/-! ## The weighted norm -/

/-- The weighted norm `N` does not see the complexification of a differentiable real function. -/
theorem fhpbb2s_weightedTestNorm_ofReal {m : ℕ} {ψ : FourierSpace m → ℝ}
    (hψ : Differentiable ℝ ψ) :
    fhp_weightedTestNorm (fun x => (ψ x : ℂ)) = fhp_weightedTestNorm ψ := by
  have h1 : ∀ x, ‖((ψ x : ℝ) : ℂ)‖ₑ = ‖ψ x‖ₑ := fun x =>
    enorm_eq_iff_norm_eq.2 (Complex.norm_real (ψ x))
  have h2 : ∀ x, ‖fderiv ℝ (fun y => (ψ y : ℂ)) x (timeVector m)‖ₑ =
      ‖fderiv ℝ ψ x (timeVector m)‖ₑ := by
    intro x
    have hfun : (fun y => (ψ y : ℂ)) = Complex.ofRealCLM ∘ ψ := by
      funext y
      simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    have hd : fderiv ℝ (fun y => (ψ y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ ψ x) := by
      rw [hfun]
      exact (Complex.ofRealCLM.hasFDerivAt.comp x (hψ x).hasFDerivAt).fderiv
    rw [hd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    exact enorm_eq_iff_norm_eq.2 (Complex.norm_real _)
  simp only [fhp_weightedTestNorm, h1, h2]

/-! ## The statement -/

/-- **The high-pass test is Schwartz** (`fhpbc_b2_testSchwartz`): for an admissible cutoff and real
compact smooth `φ`, there is `Θ : 𝓢(FourierSpace m, ℂ)` with `Θ x = (K *_t φ)(x)` for every `x`,
and `N(K *_t φ) < ∞`; implication form over `FhpbcKernelFactsStatement`,
`FhpbcTimeConvolutionStatement` and `FhpbcSchwartzNormFiniteStatement`. -/
theorem fhpbc_b2_testSchwartz_proof : FhpbcKernelFactsStatement →
    FhpbcTimeConvolutionStatement →
    FhpbcSchwartzNormFiniteStatement →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      ∀ (m : ℕ) (φ : FourierSpace m → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∃ Θ : 𝓢(FourierSpace m, ℂ),
          ∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) ∧
        fhp_weightedTestNorm (fhp_timeConvolution (fhp_highPassKernel η) φ) < ⊤ := by
  intro hK hC hN η hη m φ hφ hφc
  have hΘ := fhpbb2s_highPassTest_eq hK hC hη hφ hφc
  refine ⟨⟨_, hΘ⟩, ?_⟩
  obtain ⟨-, hKint, -, -, -, -, -⟩ := hK η hη
  obtain ⟨hψs, -, -, -, -⟩ := hC (fhp_highPassKernel η) hKint m φ hφ hφc
  have hcoe : (fhpbb2s_highPassTest η (fhpbb2s_complexTest hφ hφc) : FourierSpace m → ℂ) =
      fun x => (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ) := funext hΘ
  rw [← fhpbb2s_weightedTestNorm_ofReal (hψs.differentiable (by simp)), ← hcoe]
  exact hN m _

end ParabolicRectifiability.Foundations
