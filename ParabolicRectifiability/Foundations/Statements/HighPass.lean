import ParabolicRectifiability.Foundations.HalfTimeDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Statements of the high-pass chain

Definitions and exact proposition statements only.

* (b1) the weighted pairing estimate: `HighPassWeightedPairingStatement`;
* (b2) the high-pass kernel: `HighPassKernelStatement`;
* (c1) logarithmic growth of BMO functions: `HighPassBMOLogStatement`;
* (c2) the high-pass identity: `HighPassIdentityStatement`.

Scope: these declarations state the Schwartz-test, frequency-cutoff choice-(b)
specialization. The full smooth finite-`N` test-space extension and cutoff choice (a) are not
claimed here. The bracket integrability of the homogeneous half-time derivative is a separate
statement, `HalfTimeBracketIntegrableStatement`; nothing here depends on it.

Conventions.
* Everything is scalar and lives on the ordinary coordinates `FourierSpace m = ℝ^m × ℝ` of the
  half-time derivative. A point is `x = (u,t)`; time is `(WithLp.ofLp x).2`, and the
  time direction is `timeVector m`, so `x - s • timeVector m = (u, t - s)`
  (`HalfTimeDerivative.coordinates_sub_timeVector`). Fourier analysis never uses snowflaked time.
* The two parabolic hypotheses are read through `fourierToParabolic m`: `G` is parabolic
  Lipschitz when `G ∘ (fourierToParabolic m).symm` is Lipschitz on `Space m` (the convention of
  `HalfTimeBracketIntegrableStatement`), and `g` has
  finite parabolic BMO seminorm when `g ∘ (fourierToParabolic m).symm` satisfies the base
  predicate `HasStandardParabolicBMOBound`.
* The pairing and the half derivative are the base `halfTimeSpatialIntegrand`,
  `halfTimeSpatialBracket`, `halfTimeWindowPairing` and `halfTimeDeriv` (Mathlib's phase
  `e^{-2πi(u·ξ+tτ)}`, symbol exactly `|τ|^{1/2}`). They are defined on Schwartz
  tests, so the tests of (b1) are Schwartz tests; in choice (b) the high-pass tests `K *_t φ`
  are Schwartz, and (b2) says so.
* Only cutoff choice (b) is used (the frequency cutoff `fhp_IsFrequencyCutoff`).
  (b2), (c1) and (c2) quantify over all admissible cutoffs, and their
  constants may depend on the cutoff; (b1) involves no cutoff. A consumer fixes one admissible
  cutoff once; kernel constants may then depend on that fixed choice.
* Convolutions are `(k * f)(t) = ∫ k(s) f(t - s) ds`. Integrals are Bochner integrals (value `0`
  when not integrable). Where a conclusion uses a convolution value or a total integral whose
  convergence is not immediate from the stated data, the statement also asserts the
  integrability (the convolutions with `G` and `g`, the total integral of `K *_t φ`); the
  convolutions `K *_t φ` and `η *_t φ` with compact smooth `φ` converge since `K, η ∈ L¹`.
* An admissible cutoff exists; the hypotheses of (c2) are satisfiable; (b1) implies
  `HalfTimeBracketIntegrableStatement`. The statements are in ordinary Fourier coordinates; an
  application on `Space m` must retain both convolution-convergence clauses and transport the
  a.e. statement to `parabolicVolume`, for the given representative.

Vector forms reduce componentwise. For a general regular vertical function
(`IsGeneralRegularVerticalFunction W G ε`, with representative `g`), apply the statements to
`normalFourierComponent W G i` and `normalFourierComponent W g i`: the representation clause is
the `i`-th component of `RepresentsGeneralHalfTimeDerivative`; the Lipschitz clause follows from
`subspaceParabolic_fourierToParabolic` (the coordinates are a parabolic isometry) and the
`1`-Lipschitz normal coordinate; the scalar BMO clause follows from the vector
`HasParabolicBMOBound` through the measure-preserving isometry `subspaceParabolicIsometry` and
`|g_i - (g_P)_i| ≤ |g - g_P|`. For a vertical reference (`HasCoordinateHalfTimeBMOBound`), each
coordinate `F^α : Space m → ℝ` with representative `f` gives `G = F^α ∘ fourierToParabolic m`
and `g = f ∘ fourierToParabolic m`; `RepresentsStandardHalfTimeDerivative m F^α f` is then the
representation clause verbatim. Thus the hypotheses of (c2) apply verbatim to a coordinate of a
vertical reference; its conclusions hold on `FourierSpace m` and transfer to `Space m`, a.e. for
`parabolicVolume m`, through the measure-preserving `fourierToParabolic m` and
`Ψ(Ψ⁻¹p - s e_t) = point p.1 (p.2.val - s)`, keeping both convergence clauses.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-! ## Definitions -/

/-- Time convolution in ordinary coordinates:
`(k *_t F)(u,t) = ∫_ℝ k(s) F(u, t - s) ds` (a Bochner integral, `0` when not integrable).
The spatial variable is a parameter; `x - s • timeVector m = (u, t - s)`. -/
def fhp_timeConvolution (k : ℝ → ℝ) (F : FourierSpace m → ℝ) (x : FourierSpace m) : ℝ :=
  ∫ s : ℝ, k s * F (x - s • timeVector m)

/-- The kernel `I(t) = |t|^{-1/2}` of the inverse half derivative, as a real
power; Mathlib's convention gives the value `0` at `t = 0`, a null set. -/
def fhp_inverseHalfKernel (t : ℝ) : ℝ :=
  |t| ^ (-(1 / 2 : ℝ))

/-- The high-pass kernel `K = I - η * I`, with `(η * I)(t) = ∫ η(s) I(t - s) ds`. -/
def fhp_highPassKernel (η : ℝ → ℝ) (t : ℝ) : ℝ :=
  fhp_inverseHalfKernel t - ∫ s : ℝ, η s * fhp_inverseHalfKernel (t - s)

/-- Cutoff choice (b): a real even
Schwartz function `η` whose Fourier transform `η̂(τ) = ∫ e^{-2πitτ} η(t) dt` (Mathlib's phase) is
smooth, compactly supported, and equal to one on a neighbourhood of zero. Realness is the type;
`η̂` is then real and even, and `∫ η = η̂(0) = 1`. Nonnegativity is not required. -/
def fhp_IsFrequencyCutoff (η : 𝓢(ℝ, ℝ)) : Prop :=
  (∀ t : ℝ, η (-t) = η t) ∧
    ContDiff ℝ ∞ (𝓕 (fun t : ℝ => (η t : ℂ))) ∧
    HasCompactSupport (𝓕 (fun t : ℝ => (η t : ℂ))) ∧
    ∀ᶠ τ in 𝓝 (0 : ℝ), 𝓕 (fun t : ℝ => (η t : ℂ)) τ = 1

/-- `θ` is supported spatially in `A`: it vanishes at every `(u,t)` with `u ∉ A`. -/
def fhp_IsSpatiallySupportedIn {E : Type*} [Zero E] (θ : FourierSpace m → E)
    (A : Set (Spatial m)) : Prop :=
  ∀ x : FourierSpace m, (WithLp.ofLp x).1 ∉ A → θ x = 0

/-- The weighted norm of the weighted pairing estimate,
`N(θ) = ∫ (1 + |t|) (|θ| + |∂_t θ|) du dt`, as an extended lower integral over all of
`ℝ^m × ℝ`. For `θ` supported spatially in `A` (then so is `∂_t θ`) this is the integral over
`A × ℝ`. The time derivative is `∂_t θ(x) = Dθ(x)(e_t)`. -/
def fhp_weightedTestNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : FourierSpace m → E) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
    (‖θ x‖ₑ + ‖fderiv ℝ θ x (timeVector m)‖ₑ)

/-- The space-time cylinder `A × J = {(u,t) : u ∈ A, t ∈ J}` in ordinary coordinates. -/
def fhp_cylinder (A : Set (Spatial m)) (J : Set ℝ) : Set (FourierSpace m) :=
  {x | (WithLp.ofLp x).1 ∈ A ∧ (WithLp.ofLp x).2 ∈ J}

/-! ## Statements -/

/-- **(b1) The weighted pairing estimate.**

For a parabolic Lipschitz `G` on `ℝ^m × ℝ` and a compact `A ⊂ ℝ^m` there is a constant
`C = C_{A,G}` such that for every Schwartz test `θ` supported spatially in `A` with total integral
zero (so `N(θ) < ∞`):
* the ordered bracket construction is integrable: for a.e. `t` the spatial integrand
  `u ↦ G(u,t) (|D_t|^{1/2}θ)(u,t)` is integrable, and the bracket
  `t ↦ ∫ G(u,t) (|D_t|^{1/2}θ)(u,t) du` is in `L¹(dt)`;
* the window pairing converges to the bracket integral, so `T_G(θ) = ∫ bracket` extends the
  compact-test pairing of `RepresentsHomogeneousHalfTimeDerivative`;
* `|T_G(θ)| ≤ C N(θ)`.

Continuity in `N` follows by linearity, since the difference of two admissible tests is again
admissible. The tests are Schwartz because the base half derivative is defined on Schwartz
tests; this class contains the compact tests and the high-pass tests `K *_t φ` of (b2), which
are the only tests the proof of (c2) uses. The test is complex-valued; real tests
enter as their complexification. -/
def HighPassWeightedPairingStatement : Prop :=
  ∀ (m : ℕ) (G : FourierSpace m → ℝ),
    (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
    ∀ A : Set (Spatial m), IsCompact A →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ : 𝓢(FourierSpace m, ℂ), fhp_IsSpatiallySupportedIn (⇑θ) A → ∫ x, θ x = 0 →
          (∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G θ t)) ∧
          Integrable (halfTimeSpatialBracket G θ) ∧
          Tendsto (halfTimeWindowPairing G θ) atTop
            (𝓝 (∫ t, halfTimeSpatialBracket G θ t)) ∧
          ‖∫ t, halfTimeSpatialBracket G θ t‖ₑ ≤
            ENNReal.ofReal C * fhp_weightedTestNorm (⇑θ)

/-- **(b2) The high-pass kernel**, cutoff choice (b).

For every admissible frequency cutoff `η`, the kernel `K = I - η * I` satisfies:
* `K` is real (by type) and even;
* `K ∈ L¹(ℝ)` and `∫ K = 0`;
* `K` is smooth away from `0` (so its derivatives below are genuine);
* near zero, `|K(t)| ≤ C (1 + |t|^{-1/2})` for `|t| ≤ 1`;
* rapid tails (choice (b)): for all `j, N`, `|K^{(j)}(t)| ≤ C_{j,N} |t|^{-N}` for
  `|t| ≥ 1`;
* `K̂(τ) = (1 - η̂(τ)) |τ|^{-1/2}` for `τ ≠ 0`; the value `K̂(0) = ∫ K = 0` is the
  continuous extension;
* for every real compact smooth `φ` on `ℝ^m × ℝ`, `θ = K *_t φ` is smooth, supported spatially in
  a compact set, integrable with total integral zero, has `N(θ) < ∞`, has a Schwartz
  complexification `Θ` (`Θ x = θ x` for every `x`), and `|D_t|^{1/2} Θ = (1 - η *_t) φ` almost
  everywhere.

Schwartz membership is a representation strengthening needed to apply the base `halfTimeDeriv`;
it holds in choice (b) because `θ̂ = (1 - η̂(τ)) |τ|^{-1/2} φ̂` with a smooth multiplier of
temperate growth vanishing near `τ = 0`. -/
def HighPassKernelStatement : Prop :=
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
        (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ∧
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

/-- **(c1) Logarithmic growth of BMO functions**, cutoff choice (b).

Let `g` have finite parabolic BMO seminorm on `ℝ^m × ℝ` (read through `fourierToParabolic m`).
* For every bounded Borel `A ⊂ ℝ^m` and every bounded interval `J ⊂ [a,b]` there is
  `C = C_{A,J,g}` with `∫_{A × (J + j)} |g| ≤ C (1 + log (2 + |j|))` for all `j ∈ ℤ`. It is
  stated for `J = [a,b]`, which implies it for every subinterval.
* Consequently, for every admissible cutoff `η` and `K = I - η * I`, the convolution `K *_t g`
  is a well-defined element of `L¹_loc`: the absolute convolution integral is locally
  integrable (`∫_S ∫ |K(s)| |g(u,t-s)| ds dx < ∞` for compact `S`), the convolution integral
  converges absolutely at almost every point, and `K *_t g` is locally integrable.
* Adding a constant to `g` does not change `K *_t g` (almost everywhere). -/
def HighPassBMOLogStatement : Prop :=
  ∀ (m : ℕ) (g : FourierSpace m → ℝ),
    (∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) →
    (∀ A : Set (Spatial m), Bornology.IsBounded A → MeasurableSet A → ∀ a b : ℝ,
      ∃ C : ℝ, ∀ j : ℤ,
        ∫⁻ x in fhp_cylinder A (Set.Icc (a + j) (b + j)), ‖g x‖ₑ ≤
          ENNReal.ofReal (C * (1 + Real.log (2 + |(j : ℝ)|)))) ∧
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      (∀ S : Set (FourierSpace m), IsCompact S →
        ∫⁻ x in S, ∫⁻ s : ℝ, ‖fhp_highPassKernel η s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤) ∧
      (∀ᵐ x ∂(volume : Measure (FourierSpace m)),
        Integrable (fun s : ℝ => fhp_highPassKernel η s * g (x - s • timeVector m))) ∧
      LocallyIntegrable (fhp_timeConvolution (fhp_highPassKernel η) g) ∧
      ∀ c : ℝ, fhp_timeConvolution (fhp_highPassKernel η) (fun x => g x + c) =ᵐ[volume]
        fhp_timeConvolution (fhp_highPassKernel η) g

/-- **(c2) The high-pass identity**, cutoff choice (b).

Let `G` be general regular on `ℝ^m × ℝ` (parabolic Lipschitz, with some representative of finite
parabolic BMO seminorm) and let `g` be such a representative of its homogeneous half-time
derivative. Then, for every admissible cutoff `η` and `K = I - η * I`,
`(1 - η *_t) G = K *_t g` as locally integrable functions, i.e. almost everywhere, where the
low-pass integral `η *_t G` converges absolutely at every point and the high-pass integral
`K *_t g` at almost every point. Every `m`, including `m = 0`, is covered. There is no compact
support or `L²` hypothesis on `G` or `g`. Local integrability of `K *_t g` is (c1); it also follows
from this identity, since the left side is continuous. The identity is equivalent to the
decomposition `G = η *_t G + K *_t g`. -/
def HighPassIdentityStatement : Prop :=
  ∀ (m : ℕ) (G g : FourierSpace m → ℝ),
    (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
    (∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) →
    RepresentsHomogeneousHalfTimeDerivative G g →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      (∀ x : FourierSpace m, Integrable (fun s : ℝ => η s * G (x - s • timeVector m))) ∧
      (∀ᵐ x ∂(volume : Measure (FourierSpace m)),
        Integrable (fun s : ℝ => fhp_highPassKernel η s * g (x - s • timeVector m))) ∧
      (fun x => G x - fhp_timeConvolution η G x) =ᵐ[volume]
        fhp_timeConvolution (fhp_highPassKernel η) g

end ParabolicRectifiability.Foundations
