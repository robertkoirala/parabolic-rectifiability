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

/-! Specification: the definitions of `ParabolicRectifiability.Characterization.Statements.Branches` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Characterization
open ParabolicRectifiability.Foundations
/-- **Finite-Hausdorff criterion.**

First clause: for `n ≥ 1`, `1 ≤ k ≤ n + 2`, an available family `T`, and a Borel `E` with
`H_P^k(E) < ∞`, put `η = H_P^k⌊E`. If `S^R_{η,T} < ∞` at `η`-a.e. point for some
`0 < R < ∞`, then for every `ε > 0` the set `E` is covered modulo `H_P^k` by countably many
permitted graphs of slope or regular norm at most `ε`, i.e. `IsRegularlyRectifiableSet T k E`.
The energy uses the source `η` itself. A fixed family gives only that type, because the
typed cover of a fixed `T` contains graphs of that type only.

Second clause: at `k = n + 2` every set is contained in the ambient zero-norm
vertical graph, independently of energy: there is one full general regular vertical graph of
norm at most `0` whose image contains every subset of `X`. -/
def FiniteHausdorffCriterionStatement : Prop :=
  (∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ T : FamilyKind, Nonempty (Models n k T) →
    ∀ E : Set (Space n), MeasurableSet E → hausdorffP n k E < ⊤ →
      (∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂(hausdorffP n k).restrict E,
        squareEnergy ((hausdorffP n k).restrict E) k T R z < ⊤) →
      IsRegularlyRectifiableSet T k E) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∃ G : GeneralRegularVerticalGraph n (n + 2) 0, ∀ E : Set (Space n), E ⊆ G.image)

/-- **Intrinsic sufficiency.**

For `n ≥ 1`, `1 ≤ k ≤ n + 2`, an available family `T` and a locally Radon `μ` with
`μ ≪ H_P^k` and a Borel sigma-finite `H_P^k` carrier: if `S^R_{μ,T} < ∞` `μ`-a.e. for one
`0 < R < ∞`, then for every `ε > 0` the measure is carried by countably many permitted graphs
of slope or regular norm at most `ε` (`HasTypedMeasureCover T k μ ε`). The energy uses the
original `μ`. -/
def IntrinsicSufficiencyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    μ ≪ hausdorffP n k → HasBorelSigmaFiniteHausdorffCarrier k μ →
    (∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂μ, squareEnergy μ k T R z < ⊤) →
    ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover T k μ ε

/-- **Graph-source finiteness.**

For `n ≥ 1` and `1 ≤ k ≤ n + 2`: for every individual horizontal subset graph of finite
slope (arbitrary domain) and every individual full general regular vertical graph of finite
norm, every locally Radon ambient `μ` and every `0 < R < ∞`,
`H_P^k({z ∈ Γ_T : S^R_{μ,T}(z) = ∞}) = 0`, where the energy family is the graph's own type.
The Hausdorff measure is the outer measure, so a non-Borel horizontal domain is allowed.
No smallness of the graph, absolute continuity, support condition or finite total mass is
assumed.

"Of available type" needs no separate hypothesis: a horizontal graph has a spatial direction
of rank `k`, which forces `k ≤ n`, and a vertical graph forces `2 ≤ k ≤ n + 2`. -/
def GraphSourceStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    (∀ (ε : ℝ) (G : HorizontalGraph n k ε) (μ : Measure (Space n)),
      IsFiniteMeasureOnCompacts μ → μ.InnerRegular → ∀ R : ℝ, 0 < R →
        hausdorffP n k (G.image ∩ {z | squareEnergy μ k .horizontal R z = ⊤}) = 0) ∧
    (∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε) (μ : Measure (Space n)),
      IsFiniteMeasureOnCompacts μ → μ.InnerRegular → ∀ R : ℝ, 0 < R →
        hausdorffP n k (G.image ∩ {z | squareEnergy μ k .vertical R z = ⊤}) = 0)

/-- **Necessity.**

For `n ≥ 1`, `1 ≤ k ≤ n + 2`, an available family `T` and a locally Radon `μ` that is
regularly `k`-rectifiable in the finite-norm definition with graphs of type `T`: `μ` has a
Borel sigma-finite `H_P^k` carrier and, for `μ`-a.e. `z`, `0 < Θ_*^k ≤ Θ^{k,*} < ∞` and
`S^R_{μ,𝒜_k}(z) < ∞` for every `0 < R < ∞`. When the cover has one available type
(`T = .horizontal` or `.vertical`), the corresponding assertion with the fixed-family energy
`S^R_{μ,T}` holds as well. A cover of one type is also a mixed cover, so the
mixed energy is finite in that case too; for `T = .mixed` the two energy clauses coincide.
The universal quantifier over the endpoint sits inside the almost-everywhere clause.

The locally Radon hypotheses (`IsFiniteMeasureOnCompacts μ`, `μ.InnerRegular`) are
necessary: without local finiteness the statement is false. For a nondegenerate horizontal
segment `L`, `μ = ∞ · H_P^1⌊L` is absolutely continuous and carried by one horizontal graph,
but its densities are infinite `μ`-almost everywhere. -/
def NecessityStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    IsRegularlyRectifiableMeasure T k μ →
      HasBorelSigmaFiniteHausdorffCarrier k μ ∧
      ∀ᵐ z ∂μ, (0 < lowerDensity μ k z ∧ lowerDensity μ k z ≤ upperDensity μ k z ∧
          upperDensity μ k z < ⊤) ∧
        ∀ R : ℝ, 0 < R → squareEnergy μ k .mixed R z < ⊤ ∧ squareEnergy μ k T R z < ⊤

/-- **Typed refinement, set version.**

For `n ≥ 1`, `1 ≤ k ≤ n + 2` and a Borel `E` with `η = H_P^k⌊E` finite (`H_P^k(E) < ∞`) and
`S^1_{η,𝒜_k} < ∞` `η`-a.e., there are Borel sets `E_H, E_V ⊆ E`, disjoint and chosen once
(before every tolerance), such that `H_P^k(E \ (E_H ∪ E_V)) = 0`; for each available type
`T`, `S^1_{η,T} < ∞` at `η`-a.e. point of `E_T`; for every `ε > 0` the same `E_T` has a
type-`T` graph cover modulo `H_P^k` at bound `ε`; and an unavailable type has empty
assigned set. No closure or canonical uniqueness is claimed. -/
def TypedRefinementSetStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ E : Set (Space n), MeasurableSet E → hausdorffP n k E < ⊤ →
    (∀ᵐ z ∂(hausdorffP n k).restrict E,
      squareEnergy ((hausdorffP n k).restrict E) k .mixed 1 z < ⊤) →
    ∃ EH EV : Set (Space n), MeasurableSet EH ∧ MeasurableSet EV ∧ Disjoint EH EV ∧
      EH ⊆ E ∧ EV ⊆ E ∧ hausdorffP n k (E \ (EH ∪ EV)) = 0 ∧
      (Nonempty (Models n k .horizontal) →
        ∀ᵐ z ∂(hausdorffP n k).restrict E, z ∈ EH →
          squareEnergy ((hausdorffP n k).restrict E) k .horizontal 1 z < ⊤) ∧
      (Nonempty (Models n k .vertical) →
        ∀ᵐ z ∂(hausdorffP n k).restrict E, z ∈ EV →
          squareEnergy ((hausdorffP n k).restrict E) k .vertical 1 z < ⊤) ∧
      (∀ ε : ℝ, 0 < ε →
        HasTypedGraphCover .horizontal k EH ε ∧ HasTypedGraphCover .vertical k EV ε) ∧
      (¬ Nonempty (Models n k .horizontal) → EH = ∅) ∧
      (¬ Nonempty (Models n k .vertical) → EV = ∅)

/-- **Typed refinement, measure version.**

For `n ≥ 1`, `1 ≤ k ≤ n + 2` and a locally Radon, regularly rectifiable `μ` (finite-norm
mixed definition), there are disjoint Borel source pieces `E_H, E_V`, chosen once, with
`μ`-null remainder `μ(X \ (E_H ∪ E_V)) = 0`; for each available type `T`,
`S^1_{μ,T} < ∞` at `μ`-a.e. point of `E_T`, with the whole original `μ` as source; for every
`ε > 0` the restriction `μ⌊E_T` is carried by type-`T` graphs of slope or regular norm at
most `ε` ("type-preserving arbitrarily small covers modulo `μ`",
`HasTypedMeasureCover T k (μ.restrict E_T) ε`); and an unavailable type has empty piece.

The locally Radon hypotheses (`IsFiniteMeasureOnCompacts μ`, `μ.InnerRegular`) are
necessary: without local finiteness the statement is false. For `n = 2`, `k = 1`, infinity
times the `H_P^1` restriction to two noncollinear horizontal segments in a small ball is
graph-carried, but its full-source horizontal square is infinite (and the vertical type is
unavailable). -/
def TypedRefinementMeasureStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    IsRegularlyRectifiableMeasure .mixed k μ →
    ∃ EH EV : Set (Space n), MeasurableSet EH ∧ MeasurableSet EV ∧ Disjoint EH EV ∧
      μ (EH ∪ EV)ᶜ = 0 ∧
      (Nonempty (Models n k .horizontal) →
        ∀ᵐ z ∂μ, z ∈ EH → squareEnergy μ k .horizontal 1 z < ⊤) ∧
      (Nonempty (Models n k .vertical) →
        ∀ᵐ z ∂μ, z ∈ EV → squareEnergy μ k .vertical 1 z < ⊤) ∧
      (∀ ε : ℝ, 0 < ε →
        HasTypedMeasureCover .horizontal k (μ.restrict EH) ε ∧
          HasTypedMeasureCover .vertical k (μ.restrict EV) ε) ∧
      (¬ Nonempty (Models n k .horizontal) → EH = ∅) ∧
      (¬ Nonempty (Models n k .vertical) → EV = ∅)

end ParabolicRectifiability.Characterization
