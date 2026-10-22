import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Characterization.Proofs.Fivefold
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.GoodDomination
import ParabolicRectifiability.Characterization.Proofs.Replacement.BadRegionReplacement
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.Transfer
import ParabolicRectifiability.Characterization.Proofs.RadonApproximation
import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.Differentiation

/-! # Arbitrary-source transfer from an ADR reference

This module proves the six source-transfer statements (`FivefoldSelectionStatement` and its
companions): fivefold selection, continuous compact approximation, differentiation along nested Borel
partitions, good-set domination, replacement of the bad region, and square-energy transfer.
The first three are reusable measure-theoretic tools; the last three use the closed ADR
reference carrier.

The transfer conclusion concerns every finite ambient source and is reference-almost
everywhere on the carrier. It neither restricts the ambient source to the carrier nor
requires absolute continuity with respect to the reference. The replacement construction
allocates the bad region exactly by disjoint Borel pieces and preserves total mass.
-/

namespace ParabolicRectifiability.Characterization

/-- **Fivefold selection.** A family of open balls with positive, uniformly bounded radii in
a separable metric space has a countable pairwise disjoint subfamily whose fivefold dilates
contain all original centres. -/
theorem fivefold_selection : FivefoldSelectionStatement := by
  exact ParabolicRectifiability.Characterization.fivefold_ball_selection_proof

/-- Continuous compactly supported ambient functions are dense in `L¹` for a locally
Radon source on a closed isometrically embedded subspace, and for each Borel restriction.
The target is any finite-dimensional real inner product space. The approximation is by
`g ∘ e` with error below every `ε > 0`. -/
theorem radon_continuous_approximation : RadonApproximationStatement := by
  exact ParabolicRectifiability.Characterization.bp2_radonApproximation_proof

/-- For a finite inner regular source carried by a bounded Borel set, averages of an
integrable real function over exact nested countable Borel partitions converge almost
everywhere when the containing-cell extended diameters tend to zero. The union of all
zero-mass cells is null. -/
theorem tendsto_partition_average : CoordinateDifferentiationStatement := by
  exact ParabolicRectifiability.Characterization.CoordinateDifferentiationTree.coordinate_differentiation_of_leaves

/-- **Good-set domination.** On the good set `G_A` of a global ADR reference `σ`, the
restricted source satisfies `ν⌊G_A ≤ (5^k/c) A σ`. -/
theorem adrGoodSet_restrict_le : GoodDominationStatement := by
  exact ParabolicRectifiability.Characterization.good_set_domination_proof

/-- **Bad-region replacement.** Disjoint Whitney balls in the bad region with exact Borel
allocation of its source mass, the bad-mass bound, the piece bound, and domination of the
replaced source with total-mass preservation. -/
theorem exists_bad_region_replacement : ReplacementStatement := by
  exact ParabolicRectifiability.Characterization.ReplacementTree.bad_region_replacement_of_leaves

/-- If an ADR reference source has finite own-family square energy at endpoint `1`
almost everywhere, then every finite ambient source has finite square energy there at
reference-almost every carrier point.
The energy source is the full ambient measure, including mass off the reference carrier. -/
theorem squareEnergy_lt_top_of_adr_carrier : SourceTransferStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.adr_source_transfer_of_leaves

end ParabolicRectifiability.Characterization
