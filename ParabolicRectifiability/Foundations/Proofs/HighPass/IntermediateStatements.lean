import ParabolicRectifiability.Foundations.Statements.HighPass
import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel

/-! # High-pass chain: named intermediate statements

Definitions and proposition statements only. Consumers take the intermediate statements they
need as hypotheses with exactly these types (implication form). The public statements are
`HighPassWeightedPairingStatement`, `HighPassKernelStatement`, `HighPassBMOLogStatement` and
`HighPassIdentityStatement`.

Structure of the proof:
* (b1) `HighPassWeightedPairingStatement` ⇐ `FhpbcBracketL1Statement` (the quantitative `L¹(dt)`
  bracket bound, proved once) ⇐ the a.e. fibre transfer `fhpa_ae_fibre_halfTimeDeriv` and the
  split at the spatial base point `0` into a difference term
  (`FhpbcOneDimUnweightedStatement`) and a mean term
  (`FhpbcOneDimWeightedStatement`, `FhpbcMarginalStatement`); `FhpbcSchwartzNormFiniteStatement`
  gives integrability.
* (b2) `HighPassKernelStatement` = `FhpbcKernelFactsStatement` (its first seven clauses) and
  `FhpbcKernelTestStatement` (its test clause). The kernel facts come from
  `FhpbcKernelBasicStatement`, `FhpbcInverseHalfAsymptoticStatement` (tails, physical route),
  `FhpbcKernelTailsStatement` and `FhpbcInverseHalfFourierStatement` (the normalized transform of
  `|t|^{-1/2}`); the test clause from
  `FhpbcTimeConvolutionStatement`.
* (c1) `HighPassBMOLogStatement` = `FhpbcBMOLogGrowthStatement` and the absolute local
  convolution bounds.
* (c2) `HighPassIdentityStatement` ⇐ `FhpbcLowPassStatement`, `FhpbcHighPassPairingStatement`,
  `FhpbcSchwartzExtensionStatement` (⇐ `FhpbcCorrectedTestStatement`) and
  `FhpbcBracketOfAeEqStatement`, assembled by uniqueness of `L¹_loc` distributions.

Conventions are those of the public statements: ordinary coordinates
`FourierSpace m`, a point `x = (u,t)` with time `(WithLp.ofLp x).2`, the time shift
`x - s • timeVector m = (u, t - s)`, Mathlib's Fourier phase `e^{-2πi⟨x,ζ⟩}`, Bochner integrals
(value `0` when not integrable) with every needed integrability stated.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-! ## One-dimensional kernel operator -/

/-- The one-dimensional half-time kernel operator
`D f(t) = κ ∫ |h|^{-3/2} (f(t) - f(t-h)) dh`, with the normalization
`κ = FractionalKernel.kappa` of the base `testKernel`. For a Schwartz test `ψ` on `ℝ^m × ℝ`,
`testKernel ψ (u,t) = fhpbc_halfDeriv1D (fun s => ψ (u,s)) t` (unfold `testKernel`,
`testKernelIntegrand` and use `timeShift_toLp`). A Bochner integral: `0` at a time where the
`h`-integrand is not integrable. -/
def fhpbc_halfDeriv1D (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (FractionalKernel.kappa : ℂ) * ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))

/-! ## (b1): the weighted pairing -/

/-- **Unweighted one-dimensional estimate**:
`‖D f‖₁ ≤ C (‖f‖₁ + ‖f'‖₁)` for every `C¹` function, with a universal constant. Both sides are
extended integrals, so nothing is assumed about integrability. -/
def FhpbcOneDimUnweightedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 1 f →
    ∫⁻ t, ‖fhpbc_halfDeriv1D f t‖ₑ ≤ ENNReal.ofReal C * ∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ)

/-- **Weighted one-dimensional estimate for mean-zero functions**:
`∫ (1 + √|t|) |D f(t)| dt ≤ C ∫ (1 + |s|) (|f(s)| + |f'(s)|) ds` for every integrable `C¹`
function with `∫ f = 0`, with a universal constant. -/
def FhpbcOneDimWeightedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 1 f → Integrable f → ∫ t, f t = 0 →
    ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) * ‖fhpbc_halfDeriv1D f t‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ t, ENNReal.ofReal (1 + |t|) * (‖f t‖ₑ + ‖deriv f t‖ₑ)

/-- **Schwartz tests have finite weighted norm**: `N(θ) < ∞` for every
complex Schwartz test on `ℝ^m × ℝ`. -/
def FhpbcSchwartzNormFiniteStatement : Prop :=
  ∀ (m : ℕ) (θ : 𝓢(FourierSpace m, ℂ)), fhp_weightedTestNorm (⇑θ) < ⊤

/-- **The spatial marginal of a test** (the weighted estimate is applied to
`f(t) = ∫ θ(u,t) du` in the mean term). For a Schwartz test `θ` supported spatially in a
compact `A`, the marginal `F(s) = ∫ θ(u,s) du` is `C¹`, integrable with `∫ F = ∫ θ`, has
`∫ (1 + |s|) (|F| + |F'|) ≤ N(θ)`, and the spatial integral of the pointwise test kernel is the
one-dimensional operator of the marginal: `∫ testKernel θ (u,t) du = D F(t)` for every `t`
(Fubini in `(u,h)`). -/
def FhpbcMarginalStatement : Prop :=
  ∀ (m : ℕ) (A : Set (Spatial m)), IsCompact A →
    ∀ θ : 𝓢(FourierSpace m, ℂ), fhp_IsSpatiallySupportedIn (⇑θ) A →
      ContDiff ℝ 1 (fun s : ℝ => ∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))) ∧
      Integrable (fun s : ℝ => ∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))) ∧
      ∫ s : ℝ, (∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))) = ∫ x, θ x ∧
      ∫⁻ s : ℝ, ENNReal.ofReal (1 + |s|) *
          (‖∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))‖ₑ +
            ‖deriv (fun s' : ℝ => ∫ u : Spatial m, θ (WithLp.toLp 2 (u, s'))) s‖ₑ) ≤
        fhp_weightedTestNorm (⇑θ) ∧
      ∀ t : ℝ, ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t)) =
        fhpbc_halfDeriv1D (fun s : ℝ => ∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))) t

/-- **The quantitative ordered-bracket estimate**
`∫ |B_{G,θ}(t)| dt ≤ C_{A,G} N(θ)` together with a.e. inner integrability.
For parabolic Lipschitz `G` and compact `A` there is `C = C_{A,G}` such that for every Schwartz
test `θ` supported spatially in `A` with `∫ θ = 0`: the spatial integrand is integrable for a.e.
time, the bracket is in `L¹(dt)`, and `∫ |bracket| ≤ C N(θ)`. Absolute integrability on the
product is **not** claimed (it fails: `G = √|t|`, `θ = a(u) b(t)`). The public (b1)
follows (window limit and `|∫ ·| ≤ ∫ |·|`); so does `HalfTimeBracketIntegrableStatement`. -/
def FhpbcBracketL1Statement : Prop :=
  ∀ (m : ℕ) (G : FourierSpace m → ℝ),
    (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
    ∀ A : Set (Spatial m), IsCompact A →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ : 𝓢(FourierSpace m, ℂ), fhp_IsSpatiallySupportedIn (⇑θ) A → ∫ x, θ x = 0 →
          (∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G θ t)) ∧
          Integrable (halfTimeSpatialBracket G θ) ∧
          ∫⁻ t, ‖halfTimeSpatialBracket G θ t‖ₑ ≤
            ENNReal.ofReal C * fhp_weightedTestNorm (⇑θ)

/-! ## (b2): the high-pass kernel -/

/-- **Basic kernel facts**: for an admissible cutoff, `K = I - η * I` is
even, smooth away from `0`, satisfies the near-zero bound `|K(t)| ≤ C (1 + |t|^{-1/2})` for
`|t| ≤ 1`, and away from `0` its derivatives are those of `I` minus `η^{(j)} * I` (derivatives
moved to `η`). -/
def FhpbcKernelBasicStatement : Prop :=
  ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
    (∀ t : ℝ, fhp_highPassKernel η (-t) = fhp_highPassKernel η t) ∧
    ContDiffOn ℝ ∞ (fhp_highPassKernel η) {0}ᶜ ∧
    (∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      |fhp_highPassKernel η t| ≤ C * (1 + |t| ^ (-(1 / 2 : ℝ)))) ∧
    ∀ (j : ℕ) (t : ℝ), t ≠ 0 →
      iteratedDeriv j (fhp_highPassKernel η) t =
        iteratedDeriv j fhp_inverseHalfKernel t -
          ∫ s : ℝ, iteratedDeriv j (⇑η) s * fhp_inverseHalfKernel (t - s)

/-- **Asymptotic expansion of `ρ * I`** (a physical-space route to the rapid tails:
Taylor-expand only on `|s| ≤ |t|/2`). For a real
Schwartz `ρ` and every `N`, for `|t| ≥ 1`,
`∫ ρ(s) I(t-s) ds = Σ_{k<N} ((-1)^k / k!) (∫ s^k ρ(s) ds) I^{(k)}(t) + O(|t|^{-N})`. -/
def FhpbcInverseHalfAsymptoticStatement : Prop :=
  ∀ (ρ : 𝓢(ℝ, ℝ)) (N : ℕ), ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
    |(∫ s : ℝ, ρ s * fhp_inverseHalfKernel (t - s)) -
        ∑ k ∈ Finset.range N,
          ((-1 : ℝ) ^ k / (k.factorial : ℝ) * ∫ s : ℝ, s ^ k * ρ s) *
            iteratedDeriv k fhp_inverseHalfKernel t| ≤
      C * |t| ^ (-(N : ℝ))

/-- **Rapid tails of the kernel in choice (b)**: exactly the tail clause of
`HighPassKernelStatement`. -/
def FhpbcKernelTailsStatement : Prop :=
  ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
    ∀ j N : ℕ, ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      |iteratedDeriv j (fhp_highPassKernel η) t| ≤ C * |t| ^ (-(N : ℝ))

/-- **The normalized Fourier transform of `I(t) = |t|^{-1/2}`**, in the weak form against Schwartz tests and with Mathlib's phase:
`∫ |t|^{-1/2} ψ̂(t) dt = ∫ |τ|^{-1/2} ψ(τ) dτ`, i.e. `Î = |τ|^{-1/2}` with constant one. -/
def FhpbcInverseHalfFourierStatement : Prop :=
  ∀ ψ : 𝓢(ℝ, ℂ),
    ∫ t : ℝ, (fhp_inverseHalfKernel t : ℂ) * 𝓕 (fun x : ℝ => ψ x) t =
      ∫ τ : ℝ, ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ

/-- **The kernel facts of (b2)**: the first seven clauses of
`HighPassKernelStatement` (evenness, `L¹`, mean zero, smoothness off `0`, near-zero bound,
rapid tails, Fourier transform). Consumed by (c1), the test clause of (b2) and (c2). -/
def FhpbcKernelFactsStatement : Prop :=
  ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
    (∀ t : ℝ, fhp_highPassKernel η (-t) = fhp_highPassKernel η t) ∧
    Integrable (fhp_highPassKernel η) ∧
    ∫ t, fhp_highPassKernel η t = 0 ∧
    ContDiffOn ℝ ∞ (fhp_highPassKernel η) {0}ᶜ ∧
    (∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      |fhp_highPassKernel η t| ≤ C * (1 + |t| ^ (-(1 / 2 : ℝ)))) ∧
    (∀ j N : ℕ, ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      |iteratedDeriv j (fhp_highPassKernel η) t| ≤ C * |t| ^ (-(N : ℝ))) ∧
    (∀ τ : ℝ, τ ≠ 0 →
      𝓕 (fun t : ℝ => (fhp_highPassKernel η t : ℂ)) τ =
        (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))

/-- **Time convolution of a compact smooth function with an `L¹` kernel**:
for integrable `k` and real compact smooth `φ` on `ℝ^m × ℝ`, `k *_t φ` is smooth, supported
spatially in a compact set, integrable with `∫ k *_t φ = (∫ k)(∫ φ)`, and its Fourier transform
is `k̂(τ) φ̂(ξ,τ)`. -/
def FhpbcTimeConvolutionStatement : Prop :=
  ∀ k : ℝ → ℝ, Integrable k →
    ∀ (m : ℕ) (φ : FourierSpace m → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ContDiff ℝ ∞ (fhp_timeConvolution k φ) ∧
      (∃ A : Set (Spatial m), IsCompact A ∧
        fhp_IsSpatiallySupportedIn (fhp_timeConvolution k φ) A) ∧
      Integrable (fhp_timeConvolution k φ) ∧
      ∫ x, fhp_timeConvolution k φ x = (∫ s, k s) * ∫ x, φ x ∧
      ∀ ζ : FourierSpace m,
        𝓕 (fun x : FourierSpace m => (fhp_timeConvolution k φ x : ℂ)) ζ =
          𝓕 (fun s : ℝ => (k s : ℂ)) (WithLp.ofLp ζ).2 *
            𝓕 (fun x : FourierSpace m => (φ x : ℂ)) ζ

/-- **The test clause of (b2)**: the last clause of
`HighPassKernelStatement`. -/
def FhpbcKernelTestStatement : Prop :=
  ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
    ∀ (m : ℕ) (φ : FourierSpace m → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ContDiff ℝ ∞ (fhp_timeConvolution (fhp_highPassKernel η) φ) ∧
      (∃ A : Set (Spatial m), IsCompact A ∧
        fhp_IsSpatiallySupportedIn (fhp_timeConvolution (fhp_highPassKernel η) φ) A) ∧
      Integrable (fhp_timeConvolution (fhp_highPassKernel η) φ) ∧
      ∫ x, fhp_timeConvolution (fhp_highPassKernel η) φ x = 0 ∧
      fhp_weightedTestNorm (fhp_timeConvolution (fhp_highPassKernel η) φ) < ⊤ ∧
      ∃ Θ : 𝓢(FourierSpace m, ℂ),
        (∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) ∧
        (halfTimeDeriv m Θ : FourierSpace m → ℂ) =ᵐ[volume]
          fun x => ((φ x - fhp_timeConvolution η φ x : ℝ) : ℂ)

/-! ## (c1): BMO tails -/

/-- **BMO growth on translated fixed cylinders**: the first clause
of `HighPassBMOLogStatement`. -/
def FhpbcBMOLogGrowthStatement : Prop :=
  ∀ (m : ℕ) (g : FourierSpace m → ℝ),
    (∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) →
    ∀ A : Set (Spatial m), Bornology.IsBounded A → MeasurableSet A → ∀ a b : ℝ,
      ∃ C : ℝ, ∀ j : ℤ,
        ∫⁻ x in fhp_cylinder A (Set.Icc (a + j) (b + j)), ‖g x‖ₑ ≤
          ENNReal.ofReal (C * (1 + Real.log (2 + |(j : ℝ)|)))

/-! ## (c2): the high-pass identity -/

/-- **The low-pass side**: for parabolic Lipschitz `G` and an even
Schwartz `η`, the low-pass integral `η *_t G` converges absolutely at every point and is
continuous; for every real compact smooth `φ`, `G (η *_t φ)` is integrable and the even kernel
moves to `G`: `∫ G (η *_t φ) = ∫ (η *_t G) φ` (absolute Fubini). -/
def FhpbcLowPassStatement : Prop :=
  ∀ (m : ℕ) (G : FourierSpace m → ℝ),
    (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
    ∀ η : 𝓢(ℝ, ℝ), (∀ t : ℝ, η (-t) = η t) →
      (∀ x : FourierSpace m, Integrable (fun s : ℝ => η s * G (x - s • timeVector m))) ∧
      Continuous (fhp_timeConvolution η G) ∧
      ∀ φ : FourierSpace m → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        Integrable (fun x => G x * fhp_timeConvolution η φ x) ∧
        ∫ x, G x * fhp_timeConvolution η φ x = ∫ x, fhp_timeConvolution η G x * φ x

/-- **The high-pass side** (with (c1)): for `g` of finite parabolic BMO
seminorm, an admissible cutoff and a real compact smooth `φ`, `g (K *_t φ)` is integrable and
the even kernel moves to `g`: `∫ g (K *_t φ) = ∫ (K *_t g) φ` (absolute Fubini from the local
bound of (c1)). -/
def FhpbcHighPassPairingStatement : Prop :=
  ∀ (m : ℕ) (g : FourierSpace m → ℝ),
    (∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      ∀ φ : FourierSpace m → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        Integrable (fun x => g x * fhp_timeConvolution (fhp_highPassKernel η) φ x) ∧
        ∫ x, g x * fhp_timeConvolution (fhp_highPassKernel η) φ x =
          ∫ x, fhp_timeConvolution (fhp_highPassKernel η) g x * φ x

/-- **Corrected compact tests**: a real test `θ` with a
Schwartz complexification `Θ`, supported spatially in a compact `A`, with `∫ θ = 0`, is the limit
of real compact smooth mean-zero tests `θ_n`, all supported spatially in one compact `A' ⊇ A`,
with `N(θ_n - θ) → 0`, pointwise convergence, and domination `|θ_n| ≤ |θ| + D |ρ|` by a fixed
compact smooth `ρ`. (Intended construction: `θ_n = χ_n θ - a_n ρ`, `χ_n(t) = χ(t/n)`,
`a_n = ∫ χ_n θ`, `∫ ρ = 1`.) -/
def FhpbcCorrectedTestStatement : Prop :=
  ∀ (m : ℕ) (θ : FourierSpace m → ℝ) (Θ : 𝓢(FourierSpace m, ℂ)), (∀ x, Θ x = (θ x : ℂ)) →
    ∀ A : Set (Spatial m), IsCompact A → fhp_IsSpatiallySupportedIn θ A → ∫ x, θ x = 0 →
      ∃ (A' : Set (Spatial m)) (ρ : FourierSpace m → ℝ) (D : ℝ)
        (θs : ℕ → FourierSpace m → ℝ),
        IsCompact A' ∧ fhp_IsSpatiallySupportedIn θ A' ∧
        ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
        (∀ n, ContDiff ℝ ∞ (θs n) ∧ HasCompactSupport (θs n) ∧ ∫ x, θs n x = 0 ∧
          fhp_IsSpatiallySupportedIn (θs n) A') ∧
        (∀ n x, |θs n x| ≤ |θ x| + D * |ρ x|) ∧
        (∀ x, Tendsto (fun n => θs n x) atTop (𝓝 (θ x))) ∧
        Tendsto (fun n => fhp_weightedTestNorm (fun x => θs n x - θ x)) atTop (𝓝 0)

/-- **The representation extends to spatially compact Schwartz tests**: if
`g` represents the homogeneous half derivative of the parabolic Lipschitz `G` and has finite
parabolic BMO seminorm, then for every real test `θ` with a Schwartz complexification `Θ`,
supported spatially in a compact set, with `∫ θ = 0`, `g θ` is integrable and
`T_G(Θ) = ∫ bracket = ∫ g θ`. -/
def FhpbcSchwartzExtensionStatement : Prop :=
  ∀ (m : ℕ) (G g : FourierSpace m → ℝ),
    (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
    (∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) →
    RepresentsHomogeneousHalfTimeDerivative G g →
    ∀ (θ : FourierSpace m → ℝ) (Θ : 𝓢(FourierSpace m, ℂ)), (∀ x, Θ x = (θ x : ℂ)) →
      ∀ A : Set (Spatial m), IsCompact A → fhp_IsSpatiallySupportedIn θ A → ∫ x, θ x = 0 →
        Integrable (fun x => g x * θ x) ∧
        ∫ t, halfTimeSpatialBracket G Θ t = ((∫ x, g x * θ x : ℝ) : ℂ)

/-- **The bracket of a test whose half derivative is a real function**: if
`|D_t|^{1/2} Θ = ψ` almost everywhere and `G ψ` is integrable, then the full bracket integral is
`∫ G ψ` (fibrewise a.e. transfer as in `fhpa_ae_fibre_halfTimeDeriv`, then Fubini). No Lipschitz hypothesis is needed. -/
def FhpbcBracketOfAeEqStatement : Prop :=
  ∀ (m : ℕ) (G : FourierSpace m → ℝ) (Θ : 𝓢(FourierSpace m, ℂ)) (ψ : FourierSpace m → ℝ),
    (halfTimeDeriv m Θ : FourierSpace m → ℂ) =ᵐ[volume] (fun x => (ψ x : ℂ)) →
    Integrable (fun x => G x * ψ x) →
    ∫ t, halfTimeSpatialBracket G Θ t = ((∫ x, G x * ψ x : ℝ) : ℂ)

end ParabolicRectifiability.Foundations
