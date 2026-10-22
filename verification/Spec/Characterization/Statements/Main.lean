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
import Spec.Foundations.Carriers
import Spec.Foundations.Density
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
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

/-! Specification: the definitions of `ParabolicRectifiability.Characterization.Statements.Main` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Characterization
open ParabolicRectifiability.Foundations
/-- **Qualitative characterization.**

For `n ≥ 1`, `1 ≤ k ≤ n + 2`, an available family `T` (mixed, or an available fixed
family) and a locally Radon `μ`, the four conditions
1. `μ ≪ H_P^k` and `μ` is carried by countably many graphs of finite norm of the permitted
   types: `IsRegularlyRectifiableMeasure T k μ`;
2. for one positive finite endpoint `R`, at `μ`-a.e. point, `S^R_{μ,T} < ∞`,
   `Θ^{k,*} > 0` and `Θ_*^k < ∞`;
3. for one positive finite `R`, at `μ`-a.e. point, `S^R_{μ,T} < ∞` and
   `0 < Θ^{k,*} < ∞`;
4. `μ ≪ H_P^k`, `μ` has a Borel sigma-finite `H_P^k` carrier, and `S^R_{μ,T} < ∞`
   `μ`-a.e. for one positive finite `R`

are equivalent. The encoding is organized around (1): each of (2), (3), (4) is equivalent to (1), once with
"one" endpoint (`∃ R > 0`) and once with "every" endpoint (`∀ R > 0`), so "one" may be
replaced by "every". Every condition implies (through its equivalence with (1))
`0 < Θ_*^k ≤ Θ^{k,*} < ∞` `μ`-a.e. and, for every prescribed `ε > 0`, a cover of the
measure by permitted graphs of slope or regular norm at most `ε`:
`HasTypedMeasureCover T k μ ε`. The last conjunct states that at `k = n + 2` the square
function is identically zero, for every available family and every endpoint. -/
def QualitativeCharacterizationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    -- (1) ⟺ (2), with one endpoint and with every endpoint
    (IsRegularlyRectifiableMeasure T k μ ↔
      ∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂μ,
        squareEnergy μ k T R z < ⊤ ∧ 0 < upperDensity μ k z ∧ lowerDensity μ k z < ⊤) ∧
    (IsRegularlyRectifiableMeasure T k μ ↔
      ∀ R : ℝ, 0 < R → ∀ᵐ z ∂μ,
        squareEnergy μ k T R z < ⊤ ∧ 0 < upperDensity μ k z ∧ lowerDensity μ k z < ⊤) ∧
    -- (1) ⟺ (3), with one endpoint and with every endpoint
    (IsRegularlyRectifiableMeasure T k μ ↔
      ∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂μ,
        squareEnergy μ k T R z < ⊤ ∧ 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤) ∧
    (IsRegularlyRectifiableMeasure T k μ ↔
      ∀ R : ℝ, 0 < R → ∀ᵐ z ∂μ,
        squareEnergy μ k T R z < ⊤ ∧ 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤) ∧
    -- (1) ⟺ (4), with one endpoint and with every endpoint
    (IsRegularlyRectifiableMeasure T k μ ↔
      μ ≪ hausdorffP n k ∧ HasBorelSigmaFiniteHausdorffCarrier k μ ∧
        ∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) ∧
    (IsRegularlyRectifiableMeasure T k μ ↔
      μ ≪ hausdorffP n k ∧ HasBorelSigmaFiniteHausdorffCarrier k μ ∧
        ∀ R : ℝ, 0 < R → ∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) ∧
    -- consequences of the (equivalent) conditions
    (IsRegularlyRectifiableMeasure T k μ →
      (∀ᵐ z ∂μ, 0 < lowerDensity μ k z ∧ lowerDensity μ k z ≤ upperDensity μ k z ∧
        upperDensity μ k z < ⊤) ∧
      ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover T k μ ε) ∧
    -- at the ambient endpoint the square function is identically zero
    (k = n + 2 → ∀ (R : ℝ) (z : Space n), squareEnergy μ k T R z = 0)

end ParabolicRectifiability.Characterization
