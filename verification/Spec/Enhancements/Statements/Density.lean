import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Enhancements.Decomposition
import Spec.Foundations.Density
import Spec.Foundations.GraphDomainCover
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Foundations.SupportBounds
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.ModelDistance
import Spec.Geometry.SubspaceCoordinates
import Spec.Measure.Beta
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Space
import Spec.Specifications.Rectifiability

/-! Specification: the definitions of `ParabolicRectifiability.Enhancements.Statements.Density` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Enhancements
open ParabolicRectifiability.Foundations
/-- **All three density conclusions.**

For each `n ≥ 1` there is `C > 0` (depending only on `n` and the fixed Hausdorff
normalization, so chosen before `k`, `μ`, `A` and `a`) such that, for `1 ≤ k ≤ n+2`,
locally Radon `μ`, `U = P(0,1)` and `𝓔 = ∫_U S²_{μ,A_k} dμ < ∞`:

1. if `0 ≤ A` and `Θ_*^k(μ,·) ≤ A` `μ`-a.e. on `U`, then
   `μ(U) ≤ C (A + √𝓔)`;
2. if `0 < a` and `Θ^{k,*}(μ,·) ≥ a` `μ`-a.e. on `U`, then
   `F = U ∩ {Θ^{k,*} ≥ a}` is Borel, a full `μ⌊U` carrier, regularly rectifiable as a set,
   and `H_P^k(F) ≤ C (1 + √𝓔 / a)`;
   if instead `Θ^{k,*}(μ,·) ≥ a` at every point of `supp μ ∩ U`, then
   `supp μ ∩ U` is regularly rectifiable as a set and `H_P^k(supp μ ∩ U) ≤ C (1 + √𝓔/a)`;
3. if both density assumptions hold, then `μ⌊U ≪ H_P^k`, `μ⌊U` is
   regularly rectifiable as a measure with measure covers at every positive tolerance,
   and both bounds hold. -/
def DensityThreePartsStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    unitSquareEnergy μ k .mixed < ⊤ →
      (∀ A : ℝ, 0 ≤ A →
        (∀ᵐ z ∂μ, z ∈ Metric.ball (point 0 0) 1 → lowerDensity μ k z ≤ ENNReal.ofReal A) →
        μ (Metric.ball (point 0 0) 1) ≤
          ENNReal.ofReal (C * (A + Real.sqrt (unitSquareEnergy μ k .mixed).toReal))) ∧
      (∀ a : ℝ, 0 < a →
        (∀ᵐ z ∂μ, z ∈ Metric.ball (point 0 0) 1 → ENNReal.ofReal a ≤ upperDensity μ k z) →
        MeasurableSet (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a) ∧
        μ.restrict (Metric.ball (point 0 0) 1)
            (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a)ᶜ = 0 ∧
        IsRegularlyRectifiableSet .mixed k
          (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a) ∧
        hausdorffP n k (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a) ≤
          ENNReal.ofReal (C * (1 + Real.sqrt (unitSquareEnergy μ k .mixed).toReal / a))) ∧
      (∀ a : ℝ, 0 < a →
        (∀ z ∈ μ.support ∩ Metric.ball (point 0 0) 1, ENNReal.ofReal a ≤ upperDensity μ k z) →
        IsRegularlyRectifiableSet .mixed k (μ.support ∩ Metric.ball (point 0 0) 1) ∧
        hausdorffP n k (μ.support ∩ Metric.ball (point 0 0) 1) ≤
          ENNReal.ofReal (C * (1 + Real.sqrt (unitSquareEnergy μ k .mixed).toReal / a))) ∧
      (∀ A a : ℝ, 0 ≤ A → 0 < a →
        (∀ᵐ z ∂μ, z ∈ Metric.ball (point 0 0) 1 → lowerDensity μ k z ≤ ENNReal.ofReal A) →
        (∀ᵐ z ∂μ, z ∈ Metric.ball (point 0 0) 1 → ENNReal.ofReal a ≤ upperDensity μ k z) →
        μ.restrict (Metric.ball (point 0 0) 1) ≪ hausdorffP n k ∧
        IsRegularlyRectifiableMeasure .mixed k (μ.restrict (Metric.ball (point 0 0) 1)) ∧
        (∀ ε : ℝ, 0 < ε →
          HasTypedMeasureCover .mixed k (μ.restrict (Metric.ball (point 0 0) 1)) ε) ∧
        μ (Metric.ball (point 0 0) 1) ≤
          ENNReal.ofReal (C * (A + Real.sqrt (unitSquareEnergy μ k .mixed).toReal)) ∧
        hausdorffP n k (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a) ≤
          ENNReal.ofReal (C * (1 + Real.sqrt (unitSquareEnergy μ k .mixed).toReal / a)))

/-- **Rectifiable Reifenberg density bounds.**

For each `n ≥ 1` there is `C > 0` such that, for `1 ≤ k ≤ n+2`, locally Radon `μ`,
`U = P(0,1)` and real `M, Γ ≥ 0` with `μ(U ∩ {S²_{μ,A_k} > M}) ≤ Γ` (no integrated
energy assumption):

* if `0 ≤ A` and `Θ_*^k(μ,·) ≤ A` `μ`-a.e. on `U`, then
  `μ(U) ≤ C (A + M) + Γ`;
* for every `a > 0`, with no density hypothesis, the level set
  `F = U ∩ {Θ^{k,*} ≥ a}` is Borel and `H_P^k(F) ≤ C + (C / a)(C M + Γ)`;
* if `Θ^{k,*}(μ,·) ≥ a` `μ`-a.e. on `U`, then `F` is a full `μ⌊U`
  carrier;
* if `Θ^{k,*}(μ,·) ≥ a` at every point of `supp μ ∩ U`, then
  `H_P^k(supp μ ∩ U) ≤ C + (C / a)(C M + Γ)`.

No rectifiability is asserted. -/
def DensityRectifiableReifenbergStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
      μ (exceptionalSet μ k M) ≤ ENNReal.ofReal Γ →
      (∀ A : ℝ, 0 ≤ A →
        (∀ᵐ z ∂μ, z ∈ Metric.ball (point 0 0) 1 → lowerDensity μ k z ≤ ENNReal.ofReal A) →
        μ (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C * (A + M) + Γ)) ∧
      (∀ a : ℝ, 0 < a →
        MeasurableSet (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a) ∧
        hausdorffP n k (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a) ≤
          ENNReal.ofReal (C + C / a * (C * M + Γ))) ∧
      (∀ a : ℝ, 0 < a →
        (∀ᵐ z ∂μ, z ∈ Metric.ball (point 0 0) 1 → ENNReal.ofReal a ≤ upperDensity μ k z) →
        μ.restrict (Metric.ball (point 0 0) 1)
            (upperDensityLevelSet μ k (Metric.ball (point 0 0) 1) a)ᶜ = 0) ∧
      (∀ a : ℝ, 0 < a →
        (∀ z ∈ μ.support ∩ Metric.ball (point 0 0) 1, ENNReal.ofReal a ≤ upperDensity μ k z) →
        hausdorffP n k (μ.support ∩ Metric.ball (point 0 0) 1) ≤
          ENNReal.ofReal (C + C / a * (C * M + Γ)))

/-- **All local scales and their exact normalization.**

For each `n ≥ 1` there is `C > 0` such that, for `1 ≤ k ≤ n+2`, locally Radon `μ`,
`q ∈ X`, `R > 0`, and with `F_{q,R} = P(q,R) ∩ {Θ^{k,*} ≥ a}`:

* if `𝓔_{q,R} = ∫_{P(q,R)} S^{2R}_{μ,A_k} dμ < ∞`:
  - for `0 ≤ A` with `Θ_*^k ≤ A` `μ`-a.e. on `P(q,R)`:
    `μ(P(q,R)) ≤ C (A R^k + R^{k/2} √𝓔_{q,R})`;
  - for `0 < a` with `Θ^{k,*} ≥ a` `μ`-a.e. on `P(q,R)`: `F_{q,R}` is a
    full `μ⌊P(q,R)` carrier, regularly rectifiable as a set, and
    `H_P^k(F_{q,R}) ≤ C (R^k + a⁻¹ R^{k/2} √𝓔_{q,R})`;
  - for `0 < a` with `Θ^{k,*} ≥ a` at every point of
    `supp μ ∩ P(q,R)`: that support portion is regularly rectifiable as a set and has the
    same Hausdorff bound;
  - under both density assumptions: `μ⌊P(q,R) ≪ H_P^k`, and `μ⌊P(q,R)` is
    regularly rectifiable as a measure with measure covers at every positive tolerance;
* under only the weak threshold `μ(P(q,R) ∩ {S^{2R}_{μ,A_k} > M}) ≤ Γ`
  with real `M, Γ ≥ 0` (no integrated energy assumption):
  - for `0 ≤ A` with `Θ_*^k ≤ A` `μ`-a.e. on `P(q,R)`: `μ(P(q,R)) ≤ C (A + M) R^k + Γ`;
  - for every `a > 0`: `H_P^k(F_{q,R}) ≤ C R^k + (C / a)(C M R^k + Γ)`, with no density
    hypothesis, as in `DensityRectifiableReifenbergStatement`. -/
def DensityScalingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ (q : Space n) (R : ℝ), 0 < R →
      (localSquareEnergy μ k .mixed q R < ⊤ →
        (∀ A : ℝ, 0 ≤ A →
          (∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) →
          μ (Metric.ball q R) ≤ ENNReal.ofReal (C * (A * R ^ k +
            R ^ ((k : ℝ) / 2) * Real.sqrt (localSquareEnergy μ k .mixed q R).toReal))) ∧
        (∀ a : ℝ, 0 < a →
          (∀ᵐ z ∂μ, z ∈ Metric.ball q R → ENNReal.ofReal a ≤ upperDensity μ k z) →
          μ.restrict (Metric.ball q R) (upperDensityLevelSet μ k (Metric.ball q R) a)ᶜ = 0 ∧
          IsRegularlyRectifiableSet .mixed k (upperDensityLevelSet μ k (Metric.ball q R) a) ∧
          hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
            ENNReal.ofReal (C * (R ^ k + a⁻¹ * R ^ ((k : ℝ) / 2) *
              Real.sqrt (localSquareEnergy μ k .mixed q R).toReal))) ∧
        (∀ a : ℝ, 0 < a →
          (∀ z ∈ μ.support ∩ Metric.ball q R, ENNReal.ofReal a ≤ upperDensity μ k z) →
          IsRegularlyRectifiableSet .mixed k (μ.support ∩ Metric.ball q R) ∧
          hausdorffP n k (μ.support ∩ Metric.ball q R) ≤
            ENNReal.ofReal (C * (R ^ k + a⁻¹ * R ^ ((k : ℝ) / 2) *
              Real.sqrt (localSquareEnergy μ k .mixed q R).toReal))) ∧
        (∀ A a : ℝ, 0 ≤ A → 0 < a →
          (∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) →
          (∀ᵐ z ∂μ, z ∈ Metric.ball q R → ENNReal.ofReal a ≤ upperDensity μ k z) →
          μ.restrict (Metric.ball q R) ≪ hausdorffP n k ∧
          IsRegularlyRectifiableMeasure .mixed k (μ.restrict (Metric.ball q R)) ∧
          ∀ ε : ℝ, 0 < ε →
            HasTypedMeasureCover .mixed k (μ.restrict (Metric.ball q R)) ε)) ∧
      (∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (Metric.ball q R ∩
          {z | ENNReal.ofReal M < squareEnergy μ k .mixed (2 * R) z}) ≤ ENNReal.ofReal Γ →
        (∀ A : ℝ, 0 ≤ A →
          (∀ᵐ z ∂μ, z ∈ Metric.ball q R → lowerDensity μ k z ≤ ENNReal.ofReal A) →
          μ (Metric.ball q R) ≤ ENNReal.ofReal (C * (A + M) * R ^ k + Γ)) ∧
        (∀ a : ℝ, 0 < a →
          hausdorffP n k (upperDensityLevelSet μ k (Metric.ball q R) a) ≤
            ENNReal.ofReal (C * R ^ k + C / a * (C * M * R ^ k + Γ))))

end ParabolicRectifiability.Enhancements
