import ParabolicRectifiability.QuantitativeCharacterization.References
import ParabolicRectifiability.Foundations.ADR
import ParabolicRectifiability.Foundations.Graphs

/-! # Named statements for the reference adapters and the ADR comparisons

Proposition definitions only. They state the graph-to-reference adapters (vertical and
horizontal graphs are carried by typed references) and the ADR facts that square finiteness
and density bounds of graph sources need.

Conventions. `P(z,r)` is `Metric.ball z r`; `H_P^k` is `hausdorffP n k`, applied to
arbitrary sets (outer measure); real constants are compared through `ENNReal.ofReal`;
`r ↓ 0` is the filter `𝓝[>] 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- **Half-time derivative of an affine-plus-combination function** (analytic core of the
vertical adapter): spatial affine functions independent of time have zero derivative.

On the ordinary coordinates `ℝ^m × ℝ`, if each `G_i` (`i < d`) has its homogeneous
half-time derivative represented by `g_i` (`RepresentsHomogeneousHalfTimeDerivative`, with its
ordered-integrability clauses), then for every real `c`, every continuous linear
`ℓ : ℝ^m → ℝ` and all real coefficients `M_i`, the function
`(u,t) ↦ c + ℓ(u) + Σ_i M_i G_i(u,t)` has its derivative represented by `Σ_i M_i g_i`.

The time-independent affine part `c + ℓ(u)` is represented by `0`. For a compact smooth test
`φ`, the pointwise kernel `testKernel` of `|D_t|^{1/2} φ` vanishes off the spatial projection
of `supp φ`, is integrable, and has total integral zero; the `L²` representative
`halfTimeDeriv` has these properties only almost everywhere. No total-integral-zero condition is needed for this part. -/
def HalfTimeAffineCombinationStatement : Prop :=
  ∀ (m d : ℕ) (G g : Fin d → FourierSpace m → ℝ),
    (∀ i, RepresentsHomogeneousHalfTimeDerivative (G i) (g i)) →
    ∀ (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) (M : Fin d → ℝ),
      RepresentsHomogeneousHalfTimeDerivative
        (fun x => c + ℓ (WithLp.ofLp x).1 + ∑ i, M i * G i x)
        (fun x => ∑ i, M i * g i x)

/-- **Vertical adapter.**

For `k < n + 2`, every full general regular vertical graph `Γ` of norm at most `ε` is the
carrier of a vertical `(1 + ε)`-reference: in orthonormal coordinates `e` of `W`,
`Φ(u,t) = (a + e(u) + G(e(u),t), t)` is time preserving and `(1 + ε)`-bi-Lipschitz, every
ambient coordinate of its spatial part has a half-time derivative representative with real
parabolic BMO seminorm at most `ε`, and `Φ(ℝ^{k-2} × ℝ) = Γ`.

The reference measure `Φ_#(du dt)` is not compared with `H_P^k` here: that comparison is
`ADRHausdorffComparisonStatement` applied to the ADR carrier given by the reference
estimates. The guard `k < n + 2` is that of `VerticalReference`; at `k = n + 2` the ambient
reference is used instead. -/
def VerticalGraphReferenceStatement : Prop :=
  ∀ (n k : ℕ), k < n + 2 → ∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε),
    ∃ V : VerticalReference n k (1 + ε), V.carrier = G.image

/-- **Horizontal adapter.**

For `1 ≤ k` and every real `ε` there is `L ≥ 1`, chosen uniformly over graphs for fixed
`n, k, ε` (the type is `∀ n k, … ∀ ε, ∃ L`, so `L = L(n, k, ε)`), such that every
horizontal subset graph of slope at most `ε` with **nonempty compact** domain lies in the
carrier `Γ = supp σ` of a horizontal `L`-reference (the Whitney plateau completion of a
bi-Lipschitz extension of its spatial chart, with the graph's time function as trace).

On the original graph the reference measure and `H_P^k` have the same null sets; this
follows from `ADRHausdorffComparisonStatement` on the whole closed carrier, which contains
the graph.

Uniformity: a proof may use `L = 1 + √n|ε|`, which is additionally uniform
in `k`; the type does not advertise that independence. -/
def HorizontalGraphReferenceStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → ∀ ε : ℝ, ∃ L : ℝ, 1 ≤ L ∧
    ∀ G : HorizontalGraph n k ε, G.domain.Nonempty → IsCompact G.domain →
      ∃ H : HorizontalReference n k L, G.image ⊆ H.carrier

/-- **`IsADR` gives the closed ADR carrier of the source-transfer appendix.**

A measure that is globally `A`-ADR in dimension `k > 0` on its support, with nonempty
support, satisfies the reference hypotheses `IsADRCarrier k A⁻¹ A (supp σ) σ`: the support
is closed and nonempty, `σ` is finite on compacts (upper ADR around a nearby support point)
and inner regular (a locally finite Borel measure on the proper Polish space `X`), and the
two-sided ADR bounds hold with `c = A⁻¹`, `C = A`. -/
def ADRCarrierOfADRStatement : Prop :=
  ∀ (n k : ℕ) (A : ℝ) (σ : Measure (Space n)), 0 < k → 0 < A → σ.support.Nonempty →
    IsADR A k σ → IsADRCarrier k A⁻¹ A σ.support σ

/-- **ADR comparison**: an ADR reference measure is comparable to
`H_P^k` on its carrier.

The constants depend only on `(k, c, C)` (for instance `a = 2^k C`, `b = 10^k / c`) and are
chosen before the ambient dimension, the carrier and the measure. Both inequalities hold for
**every** set `S` (outer measures): `σ(S) ≤ a H_P^k(S ∩ Γ)` and `H_P^k(S ∩ Γ) ≤ b σ(S)`. In
particular `σ` and `H_P^k⌊Γ` have the same null sets. -/
def ADRHausdorffComparisonStatement : Prop :=
  ∀ (k : ℕ) (c C : ℝ), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ n : ℕ, 1 ≤ n → ∀ (Γ : Set (Space n)) (σ : Measure (Space n)),
      IsADRCarrier k c C Γ σ → ∀ S : Set (Space n),
        σ S ≤ ENNReal.ofReal a * hausdorffP n k (S ∩ Γ) ∧
          hausdorffP n k (S ∩ Γ) ≤ ENNReal.ofReal b * σ S

/-- **Relative differentiation**: relative differentiation with an ADR denominator.

Under the reference hypotheses `IsADRCarrier k c C Γ σ`, for every locally Radon ambient `μ`,
with Lebesgue decomposition `μ = f σ + τ`, `f = dμ/dσ` (`Measure.rnDeriv`), `τ ⊥ σ`,
the ratio `μ(P(z,r)) / σ(P(z,r))` of open balls tends to `f(z)` as `r ↓ 0` for
`σ`-almost every `z`. The source is the full ambient `μ`, including its singular part and
its mass off `Γ`. -/
def RelativeDifferentiationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ᵐ z ∂σ, Tendsto (fun r : ℝ => μ (Metric.ball z r) / σ (Metric.ball z r))
        (𝓝[>] (0 : ℝ)) (𝓝 (μ.rnDeriv σ z))

end ParabolicRectifiability.Characterization
