import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Foundations.ADR
import ParabolicRectifiability.Characterization.Carriers
import ParabolicRectifiability.Characterization.Partitions

/-! # Statements: transfer of square energies from an ADR reference

Six auxiliary statements used to transfer square-energy finiteness from an Ahlfors–David
regular reference measure to arbitrary sources: fivefold selection
(`FivefoldSelectionStatement`), Radon approximation (`RadonApproximationStatement`),
coordinate differentiation (`CoordinateDifferentiationStatement`), good-set domination
(`GoodDominationStatement`), bad-region replacement (`ReplacementStatement`) and source
transfer (`SourceTransferStatement`). The last three are stated under the reference
hypotheses `IsADRCarrier`. The corresponding theorems are `fivefold_selection`,
`radon_continuous_approximation`, `tendsto_partition_average`, `adrGoodSet_restrict_le`,
`exists_bad_region_replacement` and `squareEnergy_lt_top_of_adr_carrier`.

Conventions. `P(z,r)` is `Metric.ball z r`. The relative ball `B_Γ(z,r)` is
`Γ ∩ Metric.ball z r`, and its fivefold dilate `5B_Γ(z,r)` is `Γ ∩ Metric.ball z (5 * r)`.
The standing ambient assumption `n ≥ 1` is a hypothesis. Real constants
are compared through `ENNReal.ofReal`. A countable family is indexed by a subset of `ℕ`, as
in the existing graph covers. "Finite positive measure" means a finite nonnegative measure
(`IsFiniteMeasure`); the zero measure is allowed.

"`X` or a closed subspace of `X`" is encoded as a metric space `Y` with the Borel
σ-algebra and an isometric embedding `e : Y → X` with closed range. This class contains `X`
itself (`e = id`), every closed subset with its induced metric (`e = Subtype.val`), and the
intrinsic vertical bases `W × ℝ` (`subspaceInclusion W`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- **Fivefold selection.** In a separable metric space, every family of open balls `P(z_i, r_i)` with positive,
uniformly bounded radii has a countable pairwise disjoint subfamily (indexed by `J`) whose
fivefold dilates `P(z_j, 5 r_j)` cover all original centres `z_i`. -/
def FivefoldSelectionStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    (ι : Type) (z : ι → X) (r : ι → ℝ),
    (∀ i, 0 < r i) → (∃ R : ℝ, ∀ i, r i ≤ R) →
      ∃ J : Set ι, J.Countable ∧ J.PairwiseDisjoint (fun i => Metric.ball (z i) (r i)) ∧
        ∀ i, ∃ j ∈ J, z i ∈ Metric.ball (z j) (5 * r j)

/-- **Radon approximation.** Let `λ` be a locally finite Radon measure (finite on compacts and inner regular) on `X` or on
a closed subspace of `X` (the space `Y` with closed isometric embedding `e`), or the
restriction of such a measure to a Borel set `B`. Then continuous compactly supported
functions `g` on the ambient space `X`, restricted to the source (`g ∘ e`), are dense in
`L¹(λ)`: every integrable `f` is within `L¹` distance `ε` of such a restriction, for every
`ε > 0`. The values lie in any fixed finite-dimensional Euclidean space `E` (a
finite-dimensional real inner product space; `E = ℝ` is the scalar assertion). -/
def RadonApproximationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (Y : Type) [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] (e : Y → Space n),
    Isometry e → IsClosed (Set.range e) →
  ∀ ρ : Measure Y, IsFiniteMeasureOnCompacts ρ → ρ.InnerRegular →
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    (∀ f : Y → E, Integrable f ρ → ∀ ε : ℝ, 0 < ε →
      ∃ g : Space n → E, Continuous g ∧ HasCompactSupport g ∧
        ∫⁻ y, ‖f y - g (e y)‖ₑ ∂ρ < ENNReal.ofReal ε) ∧
    (∀ B : Set Y, MeasurableSet B →
      ∀ f : Y → E, Integrable f (ρ.restrict B) → ∀ ε : ℝ, 0 < ε →
        ∃ g : Space n → E, Continuous g ∧ HasCompactSupport g ∧
          ∫⁻ y, ‖f y - g (e y)‖ₑ ∂(ρ.restrict B) < ENNReal.ofReal ε)

/-- **Coordinate differentiation.** Let `R` be a bounded Borel subset of `X` or of a closed subspace (`Y` with closed isometric
embedding into `X`), let `λ` be a finite Radon source on `R` (a finite inner regular measure
on `Y` with `λ(Y \ R) = 0`), and let `𝒫_j`, `j ≥ 0`, be countable exact nested Borel
partitions of `R` whose cells `P_j(z)` satisfy `diam P_j(z) → 0` for every `z ∈ R`. Then
for every `h ∈ L¹(λ)`:
* the zero-mass cells of all generations have `λ`-null union (they are discarded); and
* for `λ`-a.e. `z`, `λ(P_j(z))⁻¹ ∫_{P_j(z)} h dλ → h(z)`.

The diameter is the extended diameter `Metric.ediam`, so an unbounded cell cannot have
diameter `0`. The average is the real one, `(λ(P_j(z))).toReal⁻¹ * ∫_{P_j(z)} h dλ`; by
the first conclusion every cell containing `λ`-a.e. `z` has positive mass. -/
def CoordinateDifferentiationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (Y : Type) [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y],
    (∃ e : Y → Space n, Isometry e ∧ IsClosed (Set.range e)) →
  ∀ R : Set Y, MeasurableSet R → Bornology.IsBounded R →
  ∀ ρ : Measure Y, IsFiniteMeasure ρ → ρ.InnerRegular → ρ Rᶜ = 0 →
  ∀ P : ℕ → Set (Set Y), IsExactNestedBorelPartitions R P →
    (∀ z ∈ R, Tendsto (fun j => Metric.ediam (partitionCell (P j) z)) atTop (𝓝 0)) →
  ∀ h : Y → ℝ, Integrable h ρ →
    ρ (⋃ j, ⋃₀ {Q | Q ∈ P j ∧ ρ Q = 0}) = 0 ∧
    ∀ᵐ z ∂ρ, Tendsto
      (fun j => (ρ (partitionCell (P j) z)).toReal⁻¹ * ∫ x in partitionCell (P j) z, h x ∂ρ)
      atTop (𝓝 (h z))

/-- **Good-set domination.** Under the reference hypotheses (`IsADRCarrier k c C Γ σ`), let `ν` be a finite
Borel measure carried by `Γ` and `A > 0`. For the good set
`G_A = {z ∈ Γ : ν(P(z,r)) ≤ A r^k for every r > 0}`, `ν⌊G_A ≤ (5^k / c) A σ`. -/
def GoodDominationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν Γᶜ = 0 →
  ∀ A : ℝ, 0 < A →
    ν.restrict (adrGoodSet Γ ν k A) ≤ ENNReal.ofReal (5 ^ k / c * A) • σ

/-- **Bad-region replacement.** There are constants `C₀, C₁ > 0` depending only on
`k, c, C` such that, under the reference hypotheses and for `ν` and `A` as in
`GoodDominationStatement`, with `Ω_A = Γ \ G_A`: there are countably
many relative balls `B_i = B_Γ(z_i, r_i)` (`z_i ∈ Γ`, `r_i > 0`), pairwise disjoint and
contained in `Ω_A`, and pairwise disjoint Borel sets `E_i ⊆ 5B_i` whose union is exactly
`Ω_A`, such that, with `m_i = ν(E_i)`,
* `σ(Ω_A) ≤ C₀ ν(Γ) / A` (bad-mass bound),
* `m_i ≤ 205^k A r_i^k` (piece bound),
* `ν_A := ν⌊G_A + Σ_i (m_i / σ(B_i)) σ⌊B_i ≤ C₁ A σ` and `ν_A(Γ) = ν(Γ)`
  (domination with mass preservation).

The constants are chosen before the ambient dimension `n`, the carrier and the source. -/
def ReplacementStatement : Prop :=
  ∀ (k : ℕ) (c C : ℝ), ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
  ∀ n : ℕ, 1 ≤ n →
  ∀ (Γ : Set (Space n)) (σ : Measure (Space n)), IsADRCarrier k c C Γ σ →
  ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν Γᶜ = 0 →
  ∀ A : ℝ, 0 < A →
    ∃ (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)),
      (∀ i, z i ∈ Γ ∧ 0 < r i) ∧
      Pairwise (Disjoint on fun i => Γ ∩ Metric.ball (z i) (r i)) ∧
      (∀ i, Γ ∩ Metric.ball (z i) (r i) ⊆ Γ \ adrGoodSet Γ ν k A) ∧
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i, E i ⊆ Γ ∩ Metric.ball (z i) (5 * r i)) ∧
      Pairwise (Disjoint on E) ∧
      (⋃ i, E i) = Γ \ adrGoodSet Γ ν k A ∧
      σ (Γ \ adrGoodSet Γ ν k A) ≤ ENNReal.ofReal (C₀ / A) * ν Γ ∧
      (∀ i, ν (E i) ≤ ENNReal.ofReal (205 ^ k * A * r i ^ k)) ∧
      (let νA : Measure (Space n) := ν.restrict (adrGoodSet Γ ν k A) +
          Measure.sum (fun i : I =>
            (ν (E i) / σ (Γ ∩ Metric.ball (z i) (r i))) •
              σ.restrict (Γ ∩ Metric.ball (z i) (r i)));
        νA ≤ ENNReal.ofReal (C₁ * A) • σ ∧ νA Γ = ν Γ)

/-- **ADR source transfer.** Under the reference hypotheses (`IsADRCarrier k c C Γ σ`), let `T` be an available
fixed horizontal or vertical model family, or their mixed family
(`Nonempty (Models n k T)`). If `S^1_{σ,T} < ∞` `σ`-a.e., then for every finite positive
ambient Borel measure `μ`, `S^1_{μ,T} < ∞` at `σ`-a.e. point of `Γ`. No support or absolute
continuity assumption on `μ` is made. -/
def SourceTransferStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
  ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ T : FamilyKind, Nonempty (Models n k T) →
    (∀ᵐ z ∂σ, squareEnergy σ k T 1 z < ⊤) →
    ∀ μ : Measure (Space n), IsFiniteMeasure μ →
      ∀ᵐ z ∂σ, z ∈ Γ → squareEnergy μ k T 1 z < ⊤

end ParabolicRectifiability.Characterization
