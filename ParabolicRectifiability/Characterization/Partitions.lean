import ParabolicRectifiability.Basic

/-! # Exact nested Borel partitions

Definitions only, for the differentiation lemma along nested partitions
(`coordinate_differentiation`): countable exact nested
Borel partitions `𝒫_j`, `j ≥ 0`, of a set `R`, and the cell `P_j(z)` containing a point.

"Exact" means that every point of `R` lies in exactly one cell of each generation; no
boundary set is discarded.
A partition is a set of cells. The empty set may belong to a partition without effect: it is
never the cell of a point and is disjoint from every set.
-/

noncomputable section

open Set

namespace ParabolicRectifiability.Characterization

/-- `P j` (`j : ℕ`) is a sequence of countable exact nested Borel partitions of `R`: in each
generation the cells are Borel, pairwise disjoint and have union exactly `R`, and every cell
of generation `j + 1` lies in a cell of generation `j`. -/
structure IsExactNestedBorelPartitions {Y : Type*} [MeasurableSpace Y] (R : Set Y)
    (P : ℕ → Set (Set Y)) : Prop where
  countable : ∀ j, (P j).Countable
  measurableSet : ∀ j, ∀ Q ∈ P j, MeasurableSet Q
  pairwiseDisjoint : ∀ j, (P j).PairwiseDisjoint id
  sUnion_eq : ∀ j, ⋃₀ P j = R
  nested : ∀ j, ∀ Q ∈ P (j + 1), ∃ Q' ∈ P j, Q ⊆ Q'

/-- The cell of the partition `P` containing `z`, i.e. the union of the cells that contain
`z`. For a partition of `R` and `z ∈ R` this is the unique cell `P(z)` containing `z`; for
`z ∉ R` it is empty. -/
def partitionCell {Y : Type*} (P : Set (Set Y)) (z : Y) : Set Y :=
  ⋃₀ {Q | Q ∈ P ∧ z ∈ Q}

end ParabolicRectifiability.Characterization
