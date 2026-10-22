import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterStatements
import ParabolicRectifiability.Characterization.Proofs.GraphSource.RelativeDifferentiation
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SmallDensity
import ParabolicRectifiability.Foundations.Density

/-! # Component estimates for the density bounds on graph images

The declarations expose the component estimates used for the density bounds of
`graph_density_bounds`, each with its original hypotheses and one mathematical responsibility.
They delegate to the corresponding proof theorems from `Characterization/Proofs/`.

The density argument is per carrier: on each closed ADR reference carrier `(Γ, σ)` the **full**
source decomposes as `μ = f σ + τ`, `τ ⊥ σ` (Mathlib's Lebesgue decomposition,
`f = μ.rnDeriv σ`), relative differentiation of the full `μ` against `σ` gives
`μ(P(z,r))/σ(P(z,r)) → f(z)`, and ADR turns this into `c f(z)/2 ≤ μ(P(z,r))/r^k ≤ 2 C f(z)` for
small `r`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- Relative differentiation (`RelativeDifferentiationStatement`).

Relative differentiation of a locally Radon ambient `μ` against an ADR
reference `σ`, with open balls, including the singular part and the mass off the carrier.

Proof route. Weak maximal inequality
`σ{z ∈ Γ : sup_{r<r₀} ρ(P(z,r))/σ(P(z,r)) > a} ≤ C_ADR ρ(X)/a` for finite `ρ`, by fivefold
selection of witnessing balls and `σ(5P) ≤ C_ADR σ(P)` on the carrier. Absolutely continuous
part `ρ = h σ`, `h ∈ L¹(σ)`: approximate `h` by restrictions of continuous compactly supported
ambient functions (`RadonApproximationStatement`, with `Y = Γ` or `Y = X` and the Borel
restriction clause), whose averages converge everywhere on `Γ`; the maximal inequality
controls the error. Singular part `τ ⊥ σ`: inner regularity gives compact `F` inside a
`σ`-null carrier of `τ` with `τ(X \ F)` small; off `F` small balls miss `F`. Locally finite `μ`:
keep the global ADR reference `σ` fixed and localize only `μ`. Apply the
finite-source argument to `μ_N = μ⌊P̄(0,N)`; on smaller interiors, sufficiently small testing
balls agree with those of `μ`, and `dμ_N/dσ = 1_{P̄(0,N)} dμ/dσ` almost everywhere. Exhaust
the ambient space. Mathlib alternative for the AC part: the Vitali family of `σ` restricted to
the doubling metric space `Γ` (`VitaliFamily.ae_tendsto_rnDeriv`); it needs a bridge from the
relative balls `Γ ∩ P(z,r)` back to the ambient open-ball numerator `μ(P(z,r))`.

The proof uses Mathlib's `VitaliFamily.ae_tendsto_rnDeriv` with the global `σ`, plus a
closed-to-open-ball limit step. -/
theorem b2_relative_differentiation : RelativeDifferentiationStatement := by
  exact ParabolicRectifiability.Characterization.b2_relative_differentiation_proof

/-- The Radon–Nikodym density is positive and finite on the carrier: if `μ⌊Γ = fσ` and the
off-carrier measure is singular, then `0 < f(z) < ∞` at `μ`-typical points of `Γ`.

Precisely, if `μ⌊Γ ≪ σ` for an ADR carrier `(Γ, σ)` and a locally Radon `μ`, then at
`μ`-almost every point of `Γ`, `0 < (dμ/dσ)(z) < ∞`.

Proof route. `σ` and `μ` are sigma-finite (finite on compacts in the sigma-compact `X`), so
`μ = μ.singularPart σ + σ.withDensity (μ.rnDeriv σ)`. Since `σ(Γᶜ) = 0` and `μ⌊Γ ≪ σ`, the
restriction of the singular part to `Γ` is both `≪ σ` and `⊥ σ`, hence zero; so
`μ⌊Γ = (f σ)⌊Γ`. Then `μ(Γ ∩ {f = 0}) = ∫_{Γ ∩ {f = 0}} f dσ = 0`, and `{f = ∞}` is `σ`-null
(`Measure.rnDeriv_lt_top`), hence `μ⌊Γ`-null.
-/
theorem b2_rnDeriv_pos_on_carrier :
    ∀ n : ℕ, 1 ≤ n → ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
      IsADRCarrier k c C Γ σ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      μ.restrict Γ ≪ σ →
        ∀ᵐ z ∂μ, z ∈ Γ → 0 < μ.rnDeriv σ z ∧ μ.rnDeriv σ z < ⊤ := by
  exact ParabolicRectifiability.Characterization.b2_rnDeriv_pos_on_carrier_proof

/-- ADR turns a positive finite ratio limit into density bounds: ADR gives positive lower and
finite upper density, including the effect of off-carrier mass.

At a carrier point `z` of an ADR carrier `(Γ, σ)`, if
`μ(P(z,r))/σ(P(z,r)) → f` as `r ↓ 0` with `0 < f < ∞`, then `Θ_*^k(μ,z) > 0` and
`Θ^{k,*}(μ,z) < ∞`.

Proof route. For small `r > 0` the ratio lies in `(f/2, 2f)`, and
`c r^k ≤ σ(P(z,r)) ≤ C r^k`, so `c f/2 ≤ μ(P(z,r))/r^k ≤ 2 C f`; take `liminf`/`limsup` along
`𝓝[>] 0` (`densityRatio`, `lowerDensity`, `upperDensity`, all in `ℝ≥0∞`).
-/
theorem b2_density_of_ratio :
    ∀ n : ℕ, 1 ≤ n → ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
      IsADRCarrier k c C Γ σ → ∀ (μ : Measure (Space n)) (z : Space n), z ∈ Γ →
      ∀ f : ℝ≥0∞,
        Tendsto (fun r : ℝ => μ (Metric.ball z r) / σ (Metric.ball z r)) (𝓝[>] (0 : ℝ))
          (𝓝 f) →
        0 < f → f < ⊤ → 0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤ := by
  exact ParabolicRectifiability.Characterization.b2_density_of_ratio_proof

end ParabolicRectifiability.Characterization
