import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Differentiation along nested partitions: definitions and intermediate statements

Definitions (the partition filtration `b3_cd_filtration` and the cell average
`b3_cd_average`) and the three intermediate statements from which
`CoordinateDifferentiationStatement` is proved in `coordinate_differentiation_of_leaves`.

**Proof idea (Lévy's upward theorem).** For exact nested Borel partitions `𝒫_j` of `R`,
the partition filtration
`ℱ_j = {S Borel : ∀ Q ∈ 𝒫_j, Q ⊆ S ∨ Q ∩ S = ∅}`
is an increasing sequence of sub-σ-algebras of the Borel σ-algebra; the cell average `a_j`
(zero off `R`) is a version of `𝔼[h | ℱ_j]`; with shrinking cells, `⨆_j ℱ_j` is exactly the
Borel σ-algebra; Lévy's upward theorem then gives `a_j → h` a.e. The isometric embedding,
the boundedness of `R` and inner regularity are not used, nor is the Radon approximation.

The three intermediate statements are: (i) `CdCellAverageStatement` (filtration, null union
of zero-mass cells, integrability and identification of the cell averages); (ii.a)
`CdGenerationStatement` (Borel generation); (ii.b) `CdLevyStatement` (Lévy's theorem applied
with a strongly measurable representative).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.CoordinateDifferentiationTree

/-! ## Definitions -/

set_option warn.classDefReducibility false in
/-- The partition filtration of generation `j`:
`ℱ_j = {S measurable : ∀ Q ∈ 𝒫_j, Q ⊆ S ∨ Q ∩ S = ∅}`, a sub-σ-algebra of the ambient
σ-algebra `m`. Every cell of `𝒫_j` and every measurable set disjoint from all cells (for
example a measurable subset of `Rᶜ`) belongs to `ℱ_j`. It is an explicit sub-σ-algebra,
never an instance, so its default (semireducible) transparency is intended. -/
def b3_cd_filtration {Y : Type*} [m : MeasurableSpace Y] (P : ℕ → Set (Set Y)) (j : ℕ) :
    MeasurableSpace Y where
  MeasurableSet' S := MeasurableSet[m] S ∧ ∀ Q ∈ P j, Q ⊆ S ∨ Disjoint Q S
  measurableSet_empty := ⟨MeasurableSet.empty, fun Q _ => Or.inr (Set.disjoint_empty Q)⟩
  measurableSet_compl S hS := ⟨hS.1.compl, fun Q hQ => (hS.2 Q hQ).elim
      (fun h => Or.inr (Set.disjoint_compl_right_iff_subset.mpr h))
      (fun h => Or.inl (Set.subset_compl_iff_disjoint_right.mpr h))⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun Q hQ => by
      by_cases h : ∃ i, Q ⊆ f i
      · obtain ⟨i, hi⟩ := h
        exact Or.inl (hi.trans (Set.subset_iUnion f i))
      · exact Or.inr (Set.disjoint_iUnion_right.mpr fun i =>
          ((hf i).2 Q hQ).resolve_left (not_exists.mp h i))⟩

/-- The cell average of generation `j` at `z`: `ρ(P_j(z))⁻¹ ∫_{P_j(z)} h dρ` (real average,
the same expression as in `CoordinateDifferentiationStatement`). It vanishes off `R` (the
cell of a point outside `R` is empty) and on zero-mass cells (`(0 : ℝ)⁻¹ = 0`). -/
def b3_cd_average {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) (P : ℕ → Set (Set Y))
    (h : Y → ℝ) (j : ℕ) (z : Y) : ℝ :=
  (ρ (partitionCell (P j) z)).toReal⁻¹ * ∫ x in partitionCell (P j) z, h x ∂ρ

/-! ## Intermediate statements -/

/-- **(i) Partition filtration, null cells and conditional expectations.**

For a finite measure `ρ` with `ρ(Rᶜ) = 0`, exact nested Borel partitions `𝒫_j` of `R` and
an integrable `h`:
* `ℱ_j = b3_cd_filtration P j` is increasing in `j` and below the ambient σ-algebra;
* the zero-mass cells of all generations have null union (the first conclusion of
  `CoordinateDifferentiationStatement`);
* for every `j`, the cell average `a_j` is integrable and `a_j = 𝔼_ρ[h | ℱ_j]` `ρ`-a.e.

Proof route:
* monotonicity from `nested` (a cell of generation `j+1` lies in a cell of generation `j`),
  via `monotone_nat_of_le_succ`;
* null union: countable union (`P j` countable, `j ∈ ℕ`) of null sets (`measure_iUnion_null`,
  `measure_sUnion_null`);
* `R = ⋃₀ P j` is Borel; a cell `Q ∈ P j` belongs to `ℱ_j` (pairwise disjointness), and so
  does every measurable subset of `Rᶜ`; for `z ∈ Q ∈ P j`, `partitionCell (P j) z = Q`;
* `a_j` is constant on each cell and `0` on `Rᶜ`, hence `ℱ_j`-measurable;
* integrability: `∫|a_j| dρ = Σ_{Q ∈ P_j, ρ(Q) > 0} |∫_Q h dρ| ≤ ∫|h| dρ`;
* identification by `ae_eq_condExp_of_forall_setIntegral_eq` (finite measure, so the trim is
  sigma-finite): every `S ∈ ℱ_j` is the countable disjoint union of the cells it contains
  plus `S ∩ Rᶜ`, which is null; `integral_iUnion` and `∫_Q a_j = ∫_Q h` (a zero-mass cell
  contributes `0` to both sides). Retain the explicit null union of the zero-mass cells. -/
def CdCellAverageStatement : Prop :=
  ∀ (Y : Type) [m : MeasurableSpace Y] (R : Set Y) (ρ : Measure Y), IsFiniteMeasure ρ →
    ρ Rᶜ = 0 →
  ∀ P : ℕ → Set (Set Y), IsExactNestedBorelPartitions R P →
  ∀ h : Y → ℝ, Integrable h ρ →
    Monotone (b3_cd_filtration P) ∧ (∀ j, b3_cd_filtration P j ≤ m) ∧
    ρ (⋃ j, ⋃₀ {Q | Q ∈ P j ∧ ρ Q = 0}) = 0 ∧
    ∀ j, Integrable (b3_cd_average ρ P h j) ρ ∧
      b3_cd_average ρ P h j =ᵐ[ρ] condExp (b3_cd_filtration P j) ρ h

/-- **(ii.a) Borel generation.** For exact nested Borel partitions of `R` in a
metric space with its Borel σ-algebra, whose cells shrink (`ediam P_j(z) → 0` for `z ∈ R`),
the partition filtration generates exactly the Borel σ-algebra: `⨆_j ℱ_j = m`.

Proof route: `≤` since each `ℱ_j ≤ m`. For `≥`, use `BorelSpace.measurable_eq` and
`MeasurableSpace.generateFrom_le`: it suffices that every open `U` is `⨆ ℱ_j`-measurable.
Write `U = (U ∩ R) ∪ (U ∩ Rᶜ)`. Here `U ∩ Rᶜ` is Borel and disjoint from every cell, so it
lies in `ℱ_0`. And `U ∩ R = ⋃_j ⋃_{Q ∈ 𝒫_j, Q ⊆ U} Q` (a countable union of members of the
`ℱ_j`): for `z ∈ U ∩ R` pick `ε > 0` with `P(z,ε) ⊆ U` and `j` with
`ediam P_j(z) < ofReal ε`; then `P_j(z) ⊆ P(z,ε) ⊆ U` (`Metric.edist_le_ediam_of_mem`).
The equality is exact, not modulo null sets. -/
def CdGenerationStatement : Prop :=
  ∀ (Y : Type) [MetricSpace Y] [m : MeasurableSpace Y] [BorelSpace Y] (R : Set Y)
    (P : ℕ → Set (Set Y)), IsExactNestedBorelPartitions R P →
    (∀ z ∈ R, Tendsto (fun j => Metric.ediam (partitionCell (P j) z)) atTop (𝓝 0)) →
    (⨆ j, b3_cd_filtration P j) = m

/-- **(ii.b) Lévy's upward theorem.** For a finite measure, an increasing sequence of
sub-σ-algebras `ℱ_j` generating the ambient σ-algebra, an integrable `h` and versions
`a_j = 𝔼[h | ℱ_j]` a.e., `a_j(z) → h(z)` for a.e. `z`.

Proof route: build `MeasureTheory.Filtration` from `ℱ`, its monotonicity and `ℱ_j ≤ m`.
Either apply `MeasureTheory.Integrable.tendsto_ae_condExp` to a strongly measurable
representative `h'` of `h` (`AEStronglyMeasurable.mk`; it is `⨆ ℱ_j = m`-strongly
measurable) and transfer with `condExp_congr_ae`, or apply
`MeasureTheory.tendsto_ae_condExp` (limit `𝔼[h | ⨆ ℱ_j]`) and identify
`𝔼[h | m] = h` a.e. (`condExp_of_aestronglyMeasurable'`). Intersect the countably many
identification events (`ae_all_iff`) and conclude with `Tendsto.congr`. -/
def CdLevyStatement : Prop :=
  ∀ (Y : Type) [m : MeasurableSpace Y] (ρ : Measure Y), IsFiniteMeasure ρ →
  ∀ ℱ : ℕ → MeasurableSpace Y, Monotone ℱ → (∀ j, ℱ j ≤ m) → (⨆ j, ℱ j) = m →
  ∀ (a : ℕ → Y → ℝ) (h : Y → ℝ), Integrable h ρ →
    (∀ j, a j =ᵐ[ρ] condExp (ℱ j) ρ h) →
    ∀ᵐ z ∂ρ, Tendsto (fun j => a j z) atTop (𝓝 (h z))

end ParabolicRectifiability.Characterization.CoordinateDifferentiationTree
