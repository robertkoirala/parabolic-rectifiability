import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Foundations.Carriers

/-! # Statement: the qualitative characterization

`QualitativeCharacterizationStatement` states the qualitative characterization of regularly
rectifiable measures in the parabolic space by square energies together with density or
carrier conditions. It is proved as `qualitative_characterization`.

Conventions.
* "Locally Radon" is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`.
* The family is a parameter `T : FamilyKind` with availability `Nonempty (Models n k T)`.
  `T = .mixed` is the main statement (the family `𝒜_k`); `T = .horizontal` and
  `T = .vertical` are the available fixed-family variants, with only that family and its
  corresponding graph class. In condition (1) the graph class is the typed one,
  `IsRegularlyRectifiableMeasure T k μ`; unavailable types contribute no graph.
* The square endpoint, often written `T` in the literature, is written `R`, since `T` names
  the family. `S^R_{μ,T}(z)` is `squareEnergy μ k T R z`; `Θ_*^k`, `Θ^{k,*}` are
  `lowerDensity`, `upperDensity`; `H_P^k` is `hausdorffP n k`; "μ-almost every" is
  `∀ᵐ z ∂μ`.
* The ambient endpoint `k = n + 2` is included.
-/

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
