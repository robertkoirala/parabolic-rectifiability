import ParabolicRectifiability.IntegralCanonical.Defs

/-! # Statements: exact integral tests and the integral characterization

The `Prop`-valued statements `IntegralEquivalencesStatement` and `IntegralCriterionStatement`.
Their proofs are `integral_equivalences` and `integral_criterion`.

Conventions. The standing assumptions `1 ≤ n`, `1 ≤ k ≤ n + 2` are hypotheses. "Locally
Radon" is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`. The family is the
mixed family or an available fixed family, encoded as `Nonempty (Models n k T)` (automatic
for `T = .mixed` in this range). "`μ`-almost everywhere" is `∀ᵐ z ∂μ`. The scale
endpoint is written `R`. The index `j : Fin 5` of `IntegralTest` is test `(j+1)`, so
`j ≠ 2` selects the tests (1), (2), (4), (5).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- **Exact integral tests** for square finiteness.

Setting: `n ≥ 1`, `1 ≤ k ≤ n+2`, `μ` locally Radon, `T` the mixed family or an available
fixed family; `S = S^1_{μ,T}` and `T_ρ = S^ρ_{μ,T}` for `0 < ρ ≤ 1`.
* (i) For every bounded Borel `A`, both `lim_{ρ↓0} ∫_A min{1,T_ρ} dμ` and
  `lim_{L→∞} L^{-1} ∫_A min{S,L} dμ` equal `μ(A ∩ {S = ∞})`.
* (ii) `S < ∞` `μ`-a.e. is equivalent to each test (1)–(5), tested on all bounded
  cylinders.
* (iii) In (1), (2), (4), (5), testing only `P(0,j)`, `j ≥ 1`, is sufficient:
  the reduced test implies `S < ∞` `μ`-a.e. (The converse is part of (ii), since each
  `P(0,j)` is a bounded cylinder.) -/
def IntegralEquivalencesStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
    (∀ A : Set (Space n), MeasurableSet A → Bornology.IsBounded A →
      Tendsto (fun ρ : ℝ => ∫⁻ z in A, min 1 (squareEnergy μ k T ρ z) ∂μ) (𝓝[>] 0)
          (𝓝 (μ (A ∩ {z | squareEnergy μ k T 1 z = ⊤}))) ∧
        Tendsto (fun L : ℝ =>
            (ENNReal.ofReal L)⁻¹ *
              ∫⁻ z in A, min (squareEnergy μ k T 1 z) (ENNReal.ofReal L) ∂μ)
          atTop (𝓝 (μ (A ∩ {z | squareEnergy μ k T 1 z = ⊤})))) ∧
    (∀ j : Fin 5,
      (∀ᵐ z ∂μ, squareEnergy μ k T 1 z < ⊤) ↔ IntegralTest j μ k T 1 (boundedCylinders n)) ∧
    (∀ j : Fin 5, j ≠ 2 →
      IntegralTest j μ k T 1 (originCylinders n) → ∀ᵐ z ∂μ, squareEnergy μ k T 1 z < ⊤)

/-- **Integral criterion.** Integral enhancement of the characterization: all fifteen
combinations.

Setting: `n ≥ 1`, `1 ≤ k ≤ n+2` (the ambient case `k = n+2` included), `μ`
locally Radon, and the mixed family `A_k` (`T = .mixed`) or an available fixed family with
its own graph class. For every structural condition `i ∈ {(a),(b),(c)}` and
every test `j ∈ {(1),…,(5)}`:
* for every positive finite endpoint `R` (`R = 1` is the basic case), `μ` is regularly
  `k`-rectifiable of type `T` (in the exact sense of Foundations'
  `IsRegularlyRectifiableMeasure`) iff the
  structural condition holds and test `j` holds with `S = S^R_{μ,T}` on all bounded
  cylinders;
* equivalently, iff the structural condition holds and test `j` holds at every positive
  finite endpoint;
* in (1), (2), (4), (5), testing only `P(0,j)`, `j ≥ 1`, suffices;
* every such pair of conditions implies the density improvement
  `0 < Θ_* ≤ Θ^* < ∞` `μ`-a.e. and graph covers of the measure at every positive tolerance,
  with the graph class of `T`. -/
def IntegralCriterionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ (i : Fin 3) (j : Fin 5),
    (∀ R : ℝ, 0 < R →
      (IsRegularlyRectifiableMeasure T k μ ↔
        StructuralCondition i k μ ∧ IntegralTest j μ k T R (boundedCylinders n))) ∧
    (IsRegularlyRectifiableMeasure T k μ ↔
      StructuralCondition i k μ ∧
        ∀ R : ℝ, 0 < R → IntegralTest j μ k T R (boundedCylinders n)) ∧
    (∀ R : ℝ, 0 < R → j ≠ 2 →
      StructuralCondition i k μ → IntegralTest j μ k T R (originCylinders n) →
        IsRegularlyRectifiableMeasure T k μ) ∧
    (∀ R : ℝ, 0 < R →
      StructuralCondition i k μ → IntegralTest j μ k T R (boundedCylinders n) →
        (∀ᵐ z ∂μ, 0 < lowerDensity μ k z ∧ lowerDensity μ k z ≤ upperDensity μ k z ∧
          upperDensity μ k z < ⊤) ∧
        ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover T k μ ε)

end ParabolicRectifiability.IntegralCanonical
