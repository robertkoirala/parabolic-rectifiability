import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.DifferentiationStatements
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Borel generation of the partition filtration

Proof of the named statement `CdGenerationStatement` (from `b3_cd_generation`).

Route: `⨆ ℱ_j ≤ m` since each
`ℱ_j ≤ m`. For `m ≤ ⨆ ℱ_j`, write `m = borel Y = generateFrom {open sets}`; for an open `U`,
`U = (⋃_j ⋃_{Q ∈ P_j, Q ⊆ U} Q) ∪ (U ∩ Rᶜ)`. Each cell `Q ∈ P_j` lies in `ℱ_j` (pairwise
disjointness), the index sets are countable, and `U ∩ Rᶜ ∈ ℱ_0` (disjoint from every cell).
The equality is exact: for `z ∈ U ∩ R` pick `ε > 0` with `P(z,ε) ⊆ U` and `j` with
`ediam P_j(z) < ofReal ε`; the cell `Q ∈ P_j` containing `z` satisfies
`Q ⊆ P_j(z) ⊆ P(z,ε) ⊆ U`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.CoordinateDifferentiationTree

/-- `CdGenerationStatement`: the partition filtration of shrinking exact nested Borel partitions
generates exactly the Borel σ-algebra. -/
theorem bp2_cd_generation_proof : CdGenerationStatement := by
  intro Y _ m _ R P hP hshrink
  -- Each generation sits below the ambient σ-algebra.
  have hle : ∀ j, b3_cd_filtration P j ≤ m := fun j S hS => hS.1
  -- Every cell of generation `j` belongs to `ℱ_j`.
  have hcell : ∀ j, ∀ Q ∈ P j, MeasurableSet[b3_cd_filtration P j] Q := by
    intro j Q hQ
    refine ⟨hP.measurableSet j Q hQ, fun Q' hQ' => ?_⟩
    by_cases hQQ : Q' = Q
    · exact Or.inl hQQ.le
    · exact Or.inr (hP.pairwiseDisjoint j hQ' hQ hQQ)
  have hsub : ∀ j, ∀ Q ∈ P j, Q ⊆ R := fun j Q hQ =>
    (hP.sUnion_eq j) ▸ subset_sUnion_of_mem hQ
  refine le_antisymm (iSup_le hle) ?_
  calc m = borel Y := BorelSpace.measurable_eq
    _ ≤ ⨆ j, b3_cd_filtration P j := by
      refine MeasurableSpace.generateFrom_le fun U hU => ?_
      have hU : IsOpen U := hU
      -- `U ∩ Rᶜ ∈ ℱ_0`.
      have hout : MeasurableSet[b3_cd_filtration P 0] (U ∩ Rᶜ) := by
        refine ⟨hU.measurableSet.inter (hP.sUnion_eq 0 ▸
          MeasurableSet.sUnion (hP.countable 0) (hP.measurableSet 0)).compl, fun Q hQ => ?_⟩
        exact Or.inr (Set.disjoint_of_subset_left (hsub 0 Q hQ)
          (Set.disjoint_of_subset_right Set.inter_subset_right disjoint_compl_right))
      -- `U ∩ R` is the union of the cells contained in `U`.
      have hin : U ∩ R = ⋃ j, ⋃ Q ∈ {Q | Q ∈ P j ∧ Q ⊆ U}, Q := by
        apply Subset.antisymm
        · rintro z ⟨hzU, hzR⟩
          obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hzU
          obtain ⟨j, hj⟩ := ((tendsto_order.1 (hshrink z hzR)).2 (ENNReal.ofReal ε)
            (ENNReal.ofReal_pos.2 hε)).exists
          have hzR' : z ∈ ⋃₀ P j := (hP.sUnion_eq j).symm ▸ hzR
          obtain ⟨Q, hQ, hzQ⟩ := hzR'
          have hQcell : Q ⊆ partitionCell (P j) z := subset_sUnion_of_mem ⟨hQ, hzQ⟩
          refine mem_iUnion.2 ⟨j, mem_biUnion ⟨hQ, fun y hy => hball ?_⟩ hzQ⟩
          rw [Metric.mem_ball, ← edist_lt_ofReal]
          exact (Metric.edist_le_ediam_of_mem (hQcell hy) (hQcell hzQ)).trans_lt hj
        · intro z hz
          obtain ⟨j, hz⟩ := mem_iUnion.1 hz
          obtain ⟨Q, ⟨hQ, hQU⟩, hzQ⟩ := mem_iUnion₂.1 hz
          exact ⟨hQU hzQ, hsub j Q hQ hzQ⟩
      have hU_eq : U = (U ∩ R) ∪ (U ∩ Rᶜ) := (Set.inter_union_compl U R).symm
      rw [hU_eq, hin]
      refine MeasurableSet.union (MeasurableSet.iUnion fun j => ?_)
        (le_iSup (b3_cd_filtration P) 0 _ hout)
      refine MeasurableSet.biUnion ((hP.countable j).mono fun Q hQ => hQ.1) fun Q hQ => ?_
      exact le_iSup (b3_cd_filtration P) j _ (hcell j Q hQ.1)

end ParabolicRectifiability.Characterization.CoordinateDifferentiationTree
