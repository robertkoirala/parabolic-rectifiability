import ParabolicRectifiability.Examples.Statements.Lacunary
import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel

/-! # The exponent witness below `p = 2`: intermediate statements

Definitions and `Prop`-valued intermediate statements for the proof of
`ExponentWitnessBelowStatement`: for the amplitudes `a_j = exponentAmplitude c₀ j`
(with `a_j² = c₀² / ((j+1) log²(j+2))`), the lacunary graph has a regular normal function
(parabolic Lipschitz with a BMO half time derivative), `a ∈ ℓ²`, `a ∉ ℓ^p` for `p < 2`, and the
`T_p`-energy diverges at every interior point. Each statement is proved by a theorem of the
corresponding name (e.g. `e2_sup_modulus`), and the theorem `e2_exponent_witness_below_of`
assembles them.

Lean indices are the mathematical indices minus one (see the "Indexing" note of the lacunary construction
`lacunaryFunction`).
Notation: `f = lacunaryFunction ε a N`, `F = lacunaryGraphMap ε a N`,
`ν_J = lacunarySource ε a N J`, `κ = (2π)^{-1/2} ε`,
`S_m(t) = κ Σ_{j<m} a_j cos(N_j t)` (`e2_halfDerivPartialSum`), `‖a‖₂² = Σ' a_j²`,
`sup a = ⨆ j, a j`.

The statement has five conjuncts (the third and fourth share the data `h, L, B`). The
intermediate statements are grouped as follows:
* amplitudes: `E2ExponentSquareSummableStatement` (`a ∈ ℓ²`), `E2ExponentNotSummableStatement`
  (`a ∉ ℓ^p`, `p < 2`);
* divergence: `E2BelowDivergenceStatement` (`T^R_{p,ν_J}(F(t)) = ∞` from the lower energy
  bound `LacunaryLowerEnergyStatement`);
* parabolic Lipschitz bound: `E2SupModulusStatement`, `E2ZeroBaseLipschitzStatement`;
* the periodic half derivative `h`: `E2PeriodicLimitStatement` (existence of the periodic `L²`
  limit), `E2PeriodicLocalStatement` (periodic-to-local transfer);
* BMO: `E2CosProductMeanStatement`, `E2HighFrequencyL2Statement`,
  `E2LowFrequencyOscillationStatement`, `E2HighFrequencyLimitStatement`,
  `E2BelowIntervalBMOStatement`, `E2ZeroBaseBMOStatement`;
* representation: `E2CosineKernelPairingStatement`, `E2SeriesPairingStatement`,
  `E2ZeroDimRepresentationStatement`, `E2ZeroBaseRepresentationStatement`.
The general regularity predicate (fourth conjunct) follows from `L + B ≤ 16 ε (sup a + ‖a‖₂)`.

The universal constant of the statement is `C = 16`: the Lipschitz bound gives
`L ≤ 16 ε sup a` (the argument gives `16/3`), the BMO bound gives `B ≤ 16 ε ‖a‖₂` (the argument
gives `(2√5 + 2) ε ‖a‖₂ < 6.5 ε ‖a‖₂`; a bound keeping the factor `(2π)^{-1/2}` does not follow
from `E2HighFrequencyLimitStatement`, which already replaces `κ²` by `ε²`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

/-! ## Definitions -/

/-- The partial sums `S_m(t) = (2π)^{-1/2} ε Σ_{j<m} a_j cos(N_j t)` of the periodic half
derivative, written exactly as in the convergence clause of `ExponentWitnessBelowStatement`.
Reducible, so that clause is this one up to unfolding. -/
abbrev e2_halfDerivPartialSum (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (m : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ε * ∑ j ∈ Finset.range m, a j * Real.cos (N j * t)

/-- `h` is a measurable, `2π`-periodic periodic-`L²` limit of the partial sums `S_m`: the
periodicity and convergence clauses of `ExponentWitnessBelowStatement`, plus
measurability. Reducible, so its projections are exactly those clauses. -/
abbrev E2IsPeriodicHalfDerivative (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (h : ℝ → ℝ) : Prop :=
  Measurable h ∧ Function.Periodic h (2 * Real.pi) ∧
    Tendsto (fun m : ℕ => ∫⁻ t in Ioc 0 (2 * Real.pi),
        ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N m t) ^ 2)) atTop (𝓝 0)

/-- Real mean oscillation at most `C` on every open interval: `h` is locally integrable and, for
every centre `τ` and half-length `ρ > 0`, with `I = (τ-ρ, τ+ρ)` and `h_I` its average,
`∫_I |h - h_I| ≤ C |I|` (global BMO on all intervals). -/
def E2IntervalBMOBound (h : ℝ → ℝ) (C : ℝ) : Prop :=
  LocallyIntegrable h volume ∧ ∀ τ ρ : ℝ, 0 < ρ →
    ∫ s in Ioo (τ - ρ) (τ + ρ), |h s - (2 * ρ)⁻¹ * (∫ u in Ioo (τ - ρ) (τ + ρ), h u)| ≤
      C * (2 * ρ)

/-! ## Amplitudes -/

/-- **`a ∈ ℓ²`.** For every `c₀`, `Σ_j c₀²/((j+1) log²(j+2))` converges: the first clause of
`ExponentWitnessBelowStatement` (`Σ j^{-1} log(j+1)^{-2}` converges). -/
def E2ExponentSquareSummableStatement : Prop :=
  ∀ c₀ : ℝ, Summable (fun j => exponentAmplitude c₀ j ^ 2)

/-- **`a ∉ ℓ^p` for `p < 2`.** The second clause of `ExponentWitnessBelowStatement` (any
positive power of `j` eventually dominates a logarithm). -/
def E2ExponentNotSummableStatement : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∀ p : ℝ, 0 < p → p < 2 →
    ¬ Summable (fun j => exponentAmplitude c₀ j ^ p)

/-! ## Divergence -/

/-- **`T_p` divergence.** Under the standing hypotheses, if `Σ_j a_j^p = ∞` then
`T^R_{p,ν_J}(F(t)) = ∞` for every `R > 0` and every interior parameter `-1 < t < 1`. -/
def E2BelowDivergenceStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ p : ℝ, 0 < p → ¬ Summable (fun j => a j ^ p) →
    ∀ R : ℝ, 0 < R → ∀ t ∈ Ioo (-1 : ℝ) 1,
      energyT (lacunarySource ε a N lacunaryInterval) 2 .mixed p R
        (lacunaryGraphMap ε a N t) = ⊤

/-! ## Parabolic Lipschitz bound -/

/-- **Half-Hölder modulus with the supremum amplitude.** For `ε ≥ 0` and lacunary data,
`|f(t) - f(s)| ≤ 16 ε (sup a) √|t-s|` (the lacunary modulus estimate with `a_j ≤ sup a`; the
argument gives the constant `16/3`). -/
def E2SupModulusStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 ≤ ε → IsLacunaryData a N →
    ∀ t s : ℝ, |lacunaryFunction ε a N t - lacunaryFunction ε a N s| ≤
      16 * ε * (⨆ j, a j) * Real.sqrt |t - s|

/-- **Zero-base Lipschitz adapter.** A real function of time with
`|g(t) - g(s)| ≤ C √|t-s|` lifts to a parabolic Lipschitz normal-valued function on the zero
vertical base `{0} × ℝ`, with a constant `L ≤ C` (the normal target is `ℝ` over the zero
spatial base). -/
def E2ZeroBaseLipschitzStatement : Prop :=
  ∀ (g : ℝ → ℝ) (C : ℝ), (∀ t s : ℝ, |g t - g s| ≤ C * Real.sqrt |t - s|) →
    ∃ L : ℝ≥0, LipschitzWith L (zeroBaseLift g) ∧ (L : ℝ) ≤ C

/-! ## The periodic half derivative -/

/-- **Existence of the periodic `L²` limit.** For lacunary data with
`Σ a_j² < ∞` there is a measurable `2π`-periodic `h` with `∫_{(0,2π]} |h - S_m|² → 0`
(orthogonality of distinct integer frequencies gives convergence in periodic `L²`). -/
def E2PeriodicLimitStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), IsLacunaryData a N → Summable (fun j => a j ^ 2) →
    ∃ h : ℝ → ℝ, E2IsPeriodicHalfDerivative ε a N h

/-- **Periodic-to-local transfer.** If `h` is a measurable `2π`-periodic
periodic-`L²` limit of the `S_m`, then `h` is locally integrable, square integrable on every
bounded interval `(α, β]`, and `∫_{(α,β]} |h - S_m|² → 0` (periodic `L²` convergence implies
convergence on every bounded interval, including intervals longer than a period: cover by
finitely many periods). No hypothesis on `a`, `N` or `ε`. -/
def E2PeriodicLocalStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ) (h : ℝ → ℝ), E2IsPeriodicHalfDerivative ε a N h →
    LocallyIntegrable h volume ∧ ∀ α β : ℝ,
      ∫⁻ t in Ioc α β, ENNReal.ofReal (h t ^ 2) < ⊤ ∧
      Tendsto (fun m : ℕ => ∫⁻ t in Ioc α β,
          ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N m t) ^ 2)) atTop (𝓝 0)

/-! ## BMO -/

/-- **Cosine product means.** For `0 ≤ μ`, `0 < ν`, `16 μ ≤ ν` and every
interval, `|∫_α^{α+ℓ} cos(μt) cos(νt) dt| ≤ 3/ν` (using `ν - μ ≥ 15ν/16`). -/
def E2CosProductMeanStatement : Prop :=
  ∀ μ ν : ℝ, 0 ≤ μ → 0 < ν → 16 * μ ≤ ν → ∀ α ℓ : ℝ,
    |∫ t in α..α + ℓ, Real.cos (μ * t) * Real.cos (ν * t)| ≤ 3 / ν

/-- **High-frequency `L²` bound, finite sums.** For positive frequencies with
`16 N_j ≤ N_{j+1}`, an interval of length `ℓ > 0`, and `K` with `ℓ N_K ≥ 1`: every finite
high-frequency sum satisfies `∫_α^{α+ℓ} |Σ_{K≤j<M} c_j cos(N_j t)|² ≤ 5 ℓ Σ_{K≤j<M} c_j²`.
A pure trigonometric fact; `c` is arbitrary. -/
def E2HighFrequencyL2Statement : Prop :=
  ∀ (c : ℕ → ℝ) (N : ℕ → ℕ), (∀ j, 0 < N j) → (∀ j, 16 * N j ≤ N (j + 1)) →
    ∀ α ℓ : ℝ, 0 < ℓ → ∀ K : ℕ, 1 ≤ ℓ * N K → ∀ M : ℕ,
      ∫ t in α..α + ℓ, (∑ j ∈ Finset.Ico K M, c j * Real.cos (N j * t)) ^ 2 ≤
        5 * ℓ * ∑ j ∈ Finset.Ico K M, c j ^ 2

/-- **Low-frequency oscillation.** For positive frequencies with
`16 N_j ≤ N_{j+1}`, `ℓ > 0` and `K` with `N_j ℓ ≤ 1` for all `j < K`: the low-frequency sum
oscillates by at most `2 (Σ_{j<K} c_j²)^{1/2}` over parameter gaps `|t - s| ≤ ℓ`. -/
def E2LowFrequencyOscillationStatement : Prop :=
  ∀ (c : ℕ → ℝ) (N : ℕ → ℕ), (∀ j, 0 < N j) → (∀ j, 16 * N j ≤ N (j + 1)) →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ K : ℕ, (∀ j < K, (N j : ℝ) * ℓ ≤ 1) → ∀ t s : ℝ, |t - s| ≤ ℓ →
      |∑ j ∈ Finset.range K, c j * Real.cos (N j * t) -
          ∑ j ∈ Finset.range K, c j * Real.cos (N j * s)| ≤
        2 * Real.sqrt (∑ j ∈ Finset.range K, c j ^ 2)

/-- **High-frequency bound for the limit.** For lacunary data with
`Σ a_j² < ∞`, a periodic half derivative `h`, an interval `(α, α+ℓ]` with `ℓ > 0` and `K` with
`ℓ N_K ≥ 1`: `∫_{(α,α+ℓ]} |h - S_K|² ≤ 5 ℓ ε² Σ' a_j²` (pass to the limit in the finite-sum
bound; the coefficients `c_j = κ a_j` satisfy `κ² ≤ ε²`). -/
def E2HighFrequencyLimitStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), IsLacunaryData a N → Summable (fun j => a j ^ 2) →
    ∀ h : ℝ → ℝ, E2IsPeriodicHalfDerivative ε a N h →
    ∀ α ℓ : ℝ, 0 < ℓ → ∀ K : ℕ, 1 ≤ ℓ * N K →
      ∫⁻ t in Ioc α (α + ℓ), ENNReal.ofReal ((h t - e2_halfDerivPartialSum ε a N K t) ^ 2) ≤
        ENNReal.ofReal (5 * ℓ * (ε ^ 2 * ∑' j, a j ^ 2))

/-- **Interval BMO of the periodic half derivative.** For `ε > 0`, lacunary data
with `Σ a_j² < ∞` and a periodic half derivative `h`: `h` has mean oscillation at most
`16 ε ‖a‖₂` on every open interval (the argument through the mean-oscillation adapter gives
`(2√5 + 2) ε ‖a‖₂`, and the midpoint argument `2(2 + √5) ε ‖a‖₂`; both are `< 16 ε ‖a‖₂`). -/
def E2BelowIntervalBMOStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → IsLacunaryData a N →
    Summable (fun j => a j ^ 2) → ∀ h : ℝ → ℝ, E2IsPeriodicHalfDerivative ε a N h →
      E2IntervalBMOBound h (16 * ε * Real.sqrt (∑' j, a j ^ 2))

/-- **Zero-base BMO adapter.** A real interval BMO bound `C` lifts to the vector
parabolic BMO bound of `zeroBaseLift h` on the zero vertical base, with some `B ≤ C` (for `m = 0`
the parabolic balls are exactly ordinary time intervals): the ball `P((0,τ), r)` is the
time interval `(τ - r², τ + r²)`. -/
def E2ZeroBaseBMOStatement : Prop :=
  ∀ (h : ℝ → ℝ) (C : ℝ), E2IntervalBMOBound h C →
    ∃ B : ℝ≥0, HasParabolicBMOBound zeroDirection (zeroBaseLift h) (B : ℝ) ∧ (B : ℝ) ≤ C

/-! ## Representation -/

/-- **Cosine pairing with the test kernel.** In the zero-dimensional spatial case
`m = 0`, for every real compact smooth test `φ` and every frequency `ω` (Lean name `freq`; `ω` is a
token under `open scoped ContDiff`), the pointwise half derivative `testKernel` of `φ` satisfies
`∫ cos(ω t) (|D_t|^{1/2} φ)(t) dt = (|ω|/(2π))^{1/2} ∫ cos(ω t) φ(t) dt` (the
difference-kernel form; Fourier convention `e^{-2πitτ}`, symbol `|τ|^{1/2}`). -/
def E2CosineKernelPairingStatement : Prop :=
  ∀ (φ : FourierSpace 0 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (freq : ℝ),
    ∫ x, (Real.cos (freq * timeCoordinate 0 x) : ℂ) * testKernel (realCompactTest φ hφ hc) x =
      (Real.sqrt (|freq| / (2 * Real.pi)) : ℂ) *
        ∫ x, (Real.cos (freq * timeCoordinate 0 x) : ℂ) * (φ x : ℂ)

/-- **Series pairing identity.** Under the standing hypotheses, for a periodic
half derivative `h` and every real compact smooth test `φ` on `FourierSpace 0`:
`∫ f(t) (|D_t|^{1/2} φ)(t) dt = ∫ h(t) φ(t) dt` (uniform convergence of `f` on the left,
`D φ ∈ L¹`; periodic `L²` convergence on the compact support of `φ` on the right). -/
def E2SeriesPairingStatement : Prop :=
  ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ h : ℝ → ℝ, E2IsPeriodicHalfDerivative ε a N h →
    ∀ (φ : FourierSpace 0 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ∫ x, (lacunaryFunction ε a N (timeCoordinate 0 x) : ℂ) *
          testKernel (realCompactTest φ hφ hc) x =
        ∫ x, (h (timeCoordinate 0 x) : ℂ) * (φ x : ℂ)

/-- **Zero-dimensional representation from the pairing identity.** If `F` has a
half-Hölder modulus `|F(t) - F(s)| ≤ C √|t-s|`, `g` is locally integrable and
`∫ F (|D_t|^{1/2} φ) = ∫ g φ` for every real compact smooth test, then `g ∘ time` represents the
homogeneous half-time derivative of `F ∘ time` on `FourierSpace 0` in the exact base sense
(spatial rank zero). For the total-integral-zero tests in the target,
`HalfTimeBracketIntegrableStatement` supplies globally integrable brackets; at spatial rank zero
this gives scalar-product integrability, so the symmetric time truncations converge to the
bracket integral, which is the left side of the hypothesis. Unrestricted absolute integrability
is false: for `F = √|t|` and a test with positive integral, `F · Dφ ~ -c/|t|`; the hypothesis is
used only at mean-zero tests. -/
def E2ZeroDimRepresentationStatement : Prop :=
  ∀ (F g : ℝ → ℝ) (C : ℝ), (∀ t s : ℝ, |F t - F s| ≤ C * Real.sqrt |t - s|) →
    LocallyIntegrable g volume →
    (∀ (φ : FourierSpace 0 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ∫ x, (F (timeCoordinate 0 x) : ℂ) * testKernel (realCompactTest φ hφ hc) x =
        ∫ x, (g (timeCoordinate 0 x) : ℂ) * (φ x : ℂ)) →
    RepresentsHomogeneousHalfTimeDerivative (fun x : FourierSpace 0 => F (timeCoordinate 0 x))
      (fun x => g (timeCoordinate 0 x))

/-- **Zero-base representation adapter.** The scalar representation on
`FourierSpace 0` gives the vector representation of `zeroBaseLift g` for `zeroBaseLift F` on the zero
vertical base, whose ordinary coordinates are `FourierSpace (finrank ⊥)` with `finrank ⊥ = 0` and
whose normal coordinates are fixed scalar multiples of the coordinate of `ℝ¹`. -/
def E2ZeroBaseRepresentationStatement : Prop :=
  ∀ F g : ℝ → ℝ,
    RepresentsHomogeneousHalfTimeDerivative (fun x : FourierSpace 0 => F (timeCoordinate 0 x))
      (fun x => g (timeCoordinate 0 x)) →
    RepresentsGeneralHalfTimeDerivative zeroDirection (zeroBaseLift F) (zeroBaseLift g)

end ParabolicRectifiability.Examples
