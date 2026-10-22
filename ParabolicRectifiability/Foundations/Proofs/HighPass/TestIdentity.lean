import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.HighPassMultipliers
import ParabolicRectifiability.Foundations.Proofs.HighPass.TestSchwartz

/-! # `|D_t|^{1/2} (K *_t φ) = φ - η *_t φ` almost everywhere

Proof of `fhpbc_b2_testIdentity`, in implication form over the two statements the type itself
contains: `FhpbcKernelFactsStatement` and `FhpbcTimeConvolutionStatement`.

Route. Let `Θ` be **any** complex Schwartz function with `Θ x = (K *_t φ)(x)` for every `x`, where
`K = I - η * I` is the high-pass kernel of an admissible cutoff `η`.

1. `𝓕 (halfTimeDeriv m Θ) = |τ|^{1/2} 𝓕 Θ` (the definition, `fourier_halfTimeDeriv`).
2. `𝓕 Θ = K̂(τ) φ̂` (`FhpbcTimeConvolutionStatement` with `k = K`) and `K̂(τ) = (1 - η̂(τ)) |τ|^{-1/2}` for `τ ≠ 0` (kernel
   facts), so `|τ|^{1/2} 𝓕 Θ = Q φ̂` with `Q(ξ,τ) = 1 - η̂(τ)`, **at every frequency**: at `τ = 0`
   the symbol `|τ|^{1/2}` vanishes and so does `Q`, because `η̂ = 1` near `0`
   (`fhpbb2s_one_sub_apply_zero`). No value of `K̂(0)` is used.
3. `Q` has temperate growth (`fhpbb2s_hasTemperateGrowth_lowPassComplement`), so
   `Φ = 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ Q (𝓕 φ_ℂ))` is a Schwartz function with `𝓕 Φ = Q φ̂`.
4. `Φ = φ - η *_t φ` at every point: `FhpbcTimeConvolutionStatement` with `k = η` gives continuity, integrability and
   `𝓕 (η *_t φ) = η̂(τ) φ̂`, so both sides have the transform `(1 - η̂(τ)) φ̂`, and Fourier inversion
   against a Schwartz function (`fhpbb2s_coe_eq_of_fourier_eq`)
   identifies them.
5. `halfTimeDeriv m Θ = Φ.toLp 2` in `L²` by injectivity of `Lp.fourierTransformₗᵢ`
   (`SchwartzMap.toLp_fourier_eq`), and `SchwartzMap.coeFn_toLp` turns this into the a.e.
   identity.

Helpers carry the prefix `fhpbb2i_`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-! ## Linearity of the Fourier integral on integrable functions -/

/-- The Fourier transform of a difference of integrable functions is the difference of the
transforms. -/
theorem fhpbb2i_fourier_sub {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {f g : V → ℂ}
    (hf : Integrable f) (hg : Integrable g) (w : V) :
    𝓕 (fun x => f x - g x) w = 𝓕 f w - 𝓕 g w := by
  simp only [Real.fourier_eq, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff w).2 hf)
    ((Real.fourierIntegral_convergent_iff w).2 hg)

/-! ## The low-pass complement and the Schwartz candidate -/

/-- The low-pass complement `Q(ξ,τ) = 1 - η̂(τ)` on `FourierSpace m`, with
`η̂ = 𝓕 (fun t => (η t : ℂ))` (Mathlib's phase) and `τ = (WithLp.ofLp ζ).2`. -/
def fhpbb2i_lowPassComplement (η : 𝓢(ℝ, ℝ)) (m : ℕ) (ζ : FourierSpace m) : ℂ :=
  1 - 𝓕 (fun t : ℝ => (η t : ℂ)) (WithLp.ofLp ζ).2

/-- For an admissible cutoff, `Q` has temperate growth (the lemma
`fhpbb2s_hasTemperateGrowth_lowPassComplement` with `F := η̂`). -/
theorem fhpbb2i_lowPassComplement_hasTemperateGrowth {η : 𝓢(ℝ, ℝ)}
    (hη : fhp_IsFrequencyCutoff η) (m : ℕ) :
    (fhpbb2i_lowPassComplement η m).HasTemperateGrowth :=
  fhpbb2s_hasTemperateGrowth_lowPassComplement hη.2.1 hη.2.2.1 m

/-- The Schwartz candidate `Φ = 𝓕⁻ (Q · 𝓕 φS)` for the high-frequency part `φ - η *_t φ`. -/
def fhpbb2i_highFrequencyPart (η : 𝓢(ℝ, ℝ)) {m : ℕ} (φS : 𝓢(FourierSpace m, ℂ)) :
    𝓢(FourierSpace m, ℂ) :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (fhpbb2i_lowPassComplement η m) (𝓕 φS))

/-- `𝓕 Φ = Q · 𝓕 φS` as Schwartz maps (Schwartz Fourier inversion). -/
theorem fhpbb2i_fourier_highFrequencyPart {η : 𝓢(ℝ, ℝ)} {m : ℕ} (φS : 𝓢(FourierSpace m, ℂ)) :
    𝓕 (fhpbb2i_highFrequencyPart η φS) =
      SchwartzMap.smulLeftCLM ℂ (fhpbb2i_lowPassComplement η m) (𝓕 φS) := by
  rw [fhpbb2i_highFrequencyPart, FourierTransform.fourier_fourierInv_eq]

/-- `𝓕 Φ = Q · 𝓕 φS` pointwise. -/
theorem fhpbb2i_fourier_highFrequencyPart_apply {η : 𝓢(ℝ, ℝ)} {m : ℕ}
    (hQ : (fhpbb2i_lowPassComplement η m).HasTemperateGrowth) (φS : 𝓢(FourierSpace m, ℂ))
    (ζ : FourierSpace m) :
    𝓕 (fhpbb2i_highFrequencyPart η φS : FourierSpace m → ℂ) ζ =
      fhpbb2i_lowPassComplement η m ζ * 𝓕 (φS : FourierSpace m → ℂ) ζ := by
  have h : (𝓕 (fhpbb2i_highFrequencyPart η φS)) ζ =
      fhpbb2i_lowPassComplement η m ζ * (𝓕 φS) ζ := by
    rw [fhpbb2i_fourier_highFrequencyPart, SchwartzMap.smulLeftCLM_apply_apply hQ, smul_eq_mul]
  exact h

/-! ## The physical form of the candidate -/

/-- **`Φ = φ - η *_t φ` at every point.** `FhpbcTimeConvolutionStatement` with `k = η` gives continuity, integrability and
`𝓕 (η *_t φ) = η̂(τ) φ̂`; both sides have the transform `(1 - η̂(τ)) φ̂`, and Fourier inversion
identifies them. -/
theorem fhpbb2i_highFrequencyPart_eq (hC : FhpbcTimeConvolutionStatement) {η : 𝓢(ℝ, ℝ)}
    (hη : fhp_IsFrequencyCutoff η) {m : ℕ} {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : FourierSpace m) :
    fhpbb2i_highFrequencyPart η (fhpbb2s_complexTest hφ hφc) x =
      ((φ x - fhp_timeConvolution η φ x : ℝ) : ℂ) := by
  obtain ⟨hηφs, -, hηφi, -, hηφF⟩ := hC η η.integrable m φ hφ hφc
  have hQ := fhpbb2i_lowPassComplement_hasTemperateGrowth hη m
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hφi' : Integrable (fun x : FourierSpace m => (φ x : ℂ)) := hφi.ofReal
  have hηφi' : Integrable (fun x : FourierSpace m => (fhp_timeConvolution η φ x : ℂ)) :=
    hηφi.ofReal
  have hcont : Continuous
      (fun x : FourierSpace m => ((φ x - fhp_timeConvolution η φ x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφ.continuous.sub hηφs.continuous)
  have hint : Integrable
      (fun x : FourierSpace m => ((φ x - fhp_timeConvolution η φ x : ℝ) : ℂ)) :=
    (hφi.sub hηφi).ofReal
  have hF : 𝓕 (fun x : FourierSpace m => ((φ x - fhp_timeConvolution η φ x : ℝ) : ℂ)) =
      𝓕 (fhpbb2i_highFrequencyPart η (fhpbb2s_complexTest hφ hφc) : FourierSpace m → ℂ) := by
    funext ζ
    rw [fhpbb2i_fourier_highFrequencyPart_apply hQ, fhpbb2s_coe_complexTest]
    simp only [Complex.ofReal_sub]
    rw [fhpbb2i_fourier_sub hφi' hηφi' ζ, hηφF ζ, fhpbb2i_lowPassComplement]
    ring
  exact congrFun (fhpbb2s_coe_eq_of_fourier_eq _ hcont hint hF) x

/-! ## The frequency-side identity, at every frequency -/

/-- **`|τ|^{1/2} 𝓕 Θ = Q φ̂` at every frequency** (also at `τ = 0`). For `τ ≠ 0` this is
`|τ|^{1/2} K̂(τ) = 1 - η̂(τ)`; at `τ = 0` the symbol vanishes and so does `Q`. -/
theorem fhpbb2i_symbol_mul_fourier (hK : FhpbcKernelFactsStatement)
    (hC : FhpbcTimeConvolutionStatement) {η : 𝓢(ℝ, ℝ)} (hη : fhp_IsFrequencyCutoff η) {m : ℕ}
    {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (Θ : 𝓢(FourierSpace m, ℂ))
    (hΘ : ∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ))
    (ζ : FourierSpace m) :
    (symbol ζ : ℂ) * 𝓕 (Θ : FourierSpace m → ℂ) ζ =
      fhpbb2i_lowPassComplement η m ζ * 𝓕 (fun x => (φ x : ℂ)) ζ := by
  obtain ⟨-, hKint, -, -, -, -, hfour⟩ := hK η hη
  obtain ⟨-, -, -, -, hψF⟩ := hC (fhp_highPassKernel η) hKint m φ hφ hφc
  have hcoe : (Θ : FourierSpace m → ℂ) =
      fun x => (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ) := funext hΘ
  rw [hcoe, hψF ζ, fhpbb2i_lowPassComplement]
  rcases eq_or_ne (WithLp.ofLp ζ).2 0 with hτ | hτ
  · have hs : symbol ζ = 0 :=
      symbol_eq_zero_of_timeCoordinate_eq_zero (by rw [timeCoordinate_apply]; exact hτ)
    rw [hs, hτ, fhpbb2s_one_sub_apply_zero hη.2.2.2]
    simp
  · rw [hfour _ hτ]
    have hpos : 0 < |(WithLp.ofLp ζ).2| := abs_pos.2 hτ
    have h1 : symbol ζ * |(WithLp.ofLp ζ).2| ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [symbol, timeCoordinate_apply, ← Real.rpow_add hpos]
      norm_num
    calc (symbol ζ : ℂ) * ((1 - 𝓕 (fun t : ℝ => (η t : ℂ)) (WithLp.ofLp ζ).2) *
            ((|(WithLp.ofLp ζ).2| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * 𝓕 (fun x => (φ x : ℂ)) ζ)
        = ((symbol ζ * |(WithLp.ofLp ζ).2| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((1 - 𝓕 (fun t : ℝ => (η t : ℂ)) (WithLp.ofLp ζ).2) *
              𝓕 (fun x => (φ x : ℂ)) ζ) := by
          rw [Complex.ofReal_mul]; ring
      _ = (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) (WithLp.ofLp ζ).2) * 𝓕 (fun x => (φ x : ℂ)) ζ := by
          rw [h1, Complex.ofReal_one, one_mul]

/-- The frequency-side `L²` class of `halfTimeDeriv m Θ` is that of the Schwartz map `Q · 𝓕 φS`. -/
theorem fhpbb2i_weightedLp_eq (hK : FhpbcKernelFactsStatement)
    (hC : FhpbcTimeConvolutionStatement) {η : 𝓢(ℝ, ℝ)} (hη : fhp_IsFrequencyCutoff η) {m : ℕ}
    {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (Θ : 𝓢(FourierSpace m, ℂ))
    (hΘ : ∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) :
    weightedLp (𝓕 Θ) =
      (SchwartzMap.smulLeftCLM ℂ (fhpbb2i_lowPassComplement η m)
        (𝓕 (fhpbb2s_complexTest hφ hφc))).toLp 2 := by
  have hQ := fhpbb2i_lowPassComplement_hasTemperateGrowth hη m
  apply Lp.ext
  filter_upwards [coeFn_weightedLp (𝓕 Θ),
    SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM ℂ (fhpbb2i_lowPassComplement η m)
      (𝓕 (fhpbb2s_complexTest hφ hφc))) 2] with z h1 h2
  rw [h1, h2, SchwartzMap.smulLeftCLM_apply_apply hQ, smul_eq_mul]
  exact fhpbb2i_symbol_mul_fourier hK hC hη hφ hφc Θ hΘ z

/-- **`halfTimeDeriv m Θ = Φ` in `L²`**, by injectivity of the `L²` Fourier transform. -/
theorem fhpbb2i_halfTimeDeriv_eq (hK : FhpbcKernelFactsStatement)
    (hC : FhpbcTimeConvolutionStatement) {η : 𝓢(ℝ, ℝ)} (hη : fhp_IsFrequencyCutoff η) {m : ℕ}
    {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (Θ : 𝓢(FourierSpace m, ℂ))
    (hΘ : ∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) :
    halfTimeDeriv m Θ = (fhpbb2i_highFrequencyPart η (fhpbb2s_complexTest hφ hφc)).toLp 2 := by
  apply (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).injective
  change 𝓕 (halfTimeDeriv m Θ) =
    𝓕 ((fhpbb2i_highFrequencyPart η (fhpbb2s_complexTest hφ hφc)).toLp 2)
  rw [fourier_halfTimeDeriv, SchwartzMap.toLp_fourier_eq, fhpbb2i_fourier_highFrequencyPart]
  exact fhpbb2i_weightedLp_eq hK hC hη hφ hφc Θ hΘ

/-! ## The statement -/

/-- **The half-derivative identity** (`fhpbc_b2_testIdentity`): for an admissible cutoff, a real
compact smooth `φ` and **any** Schwartz `Θ` with `Θ x = (K *_t φ)(x)` for every `x`,
`|D_t|^{1/2} Θ = φ - η *_t φ` almost everywhere; implication form over
`FhpbcKernelFactsStatement` and `FhpbcTimeConvolutionStatement`. -/
theorem fhpbc_b2_testIdentity_proof : FhpbcKernelFactsStatement →
    FhpbcTimeConvolutionStatement →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      ∀ (m : ℕ) (φ : FourierSpace m → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∀ Θ : 𝓢(FourierSpace m, ℂ),
          (∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) →
          (halfTimeDeriv m Θ : FourierSpace m → ℂ) =ᵐ[volume]
            fun x => ((φ x - fhp_timeConvolution η φ x : ℝ) : ℂ) := by
  intro hK hC η hη m φ hφ hφc Θ hΘ
  rw [fhpbb2i_halfTimeDeriv_eq hK hC hη hφ hφc Θ hΘ]
  filter_upwards [SchwartzMap.coeFn_toLp
    (fhpbb2i_highFrequencyPart η (fhpbb2s_complexTest hφ hφc)) 2] with x hx
  rw [hx]
  exact fhpbb2i_highFrequencyPart_eq hC hη hφ hφc x

end ParabolicRectifiability.Foundations
