import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ForwardCovering
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.NetExtension
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.NestedNets
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.ClosedCellBasics
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.UniqueInner
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.ChildrenCount
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.Assignment
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.ProtectedBalls
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.CoeffAnnulus
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.DescendantIntegral
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.ForestEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.CellMass
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.UpperRecentering
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.TubeMass
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.CovarianceLower
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.PlaneComparison
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.FittingGap

/-! # The partition-energy statement: composition of the proofs

The two `…_of` theorems assemble `d1a_directPartition_of` and `d1a_partitionEnergy_of` from their
ingredient statements; the closed theorems supply every ingredient by its proof:

* `d1acomp_partitionEnergy : PartitionEnergyStatement`, the type of `d1_hub_partitionEnergy`;
* `d1acomp_covarianceLower`, `d1acomp_planeComparison`, `d1acomp_fittingGap`, the closed
  statements used downstream.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-- **Assembly of the direct partitions.** The six branch-P statements give direct partitions of every closed set. -/
theorem d1acomp_directPartition_of (hNets : NestedNetsStatement)
    (hBasics : ClosedCellBasicsStatement) (hInner : UniqueInnerStatement)
    (hChildren : ChildrenCountStatement) (hAssign : AssignmentStatement)
    (hProtected : ProtectedBallsStatement) : DirectPartitionExistsStatement := by
  intro n E hE ℓ₀ hℓ₀
  obtain ⟨N⟩ := hNets n E hE ℓ₀ hℓ₀
  have hB : N.ClosedCellBasics := hBasics n E ℓ₀ N hE
  have hU : N.UniqueInner := hInner n E ℓ₀ N hE hB
  obtain ⟨C⟩ := hAssign n E ℓ₀ N hE hB hU
  exact ⟨{
    scale_pos := N.scale_pos
    center := N.center
    cell := C.cell
    parent := N.parent
    center_subset := N.center_subset
    center_countable := N.center_countable
    center_mono := N.center_mono
    center_separated := N.center_separated
    measurable_cell := C.measurable_cell
    cell_disjoint := C.cell_disjoint
    cell_cover := C.cell_cover
    inner_subset := C.inner_subset
    cell_subset_ball := fun j z hz =>
      (subset_closure.trans (C.closure_cell j z hz).le).trans
        (hB.closedCell_subset_ball j z hz)
    parent_mem := N.parent_mem
    cell_subset_parent := C.cell_subset_parent
    children_encard := hChildren n E ℓ₀ N
    protected_ball := hProtected n E ℓ₀ N hE hB hU C }⟩

/-- **Assembly.** Direct partitions of the closed support from `ℓ₀ = R` and the forest energy
for every such partition give `PartitionEnergyStatement`. -/
theorem d1acomp_partitionEnergy_of (hPart : DirectPartitionExistsStatement)
    (hEnergy : ForestEnergyStatement) : PartitionEnergyStatement := by
  intro n hn k hk hkn A hA Λ hΛ
  obtain ⟨CE, hCE, B, hB, h⟩ := hEnergy n hn k hk hkn A hA Λ hΛ
  refine ⟨CE, hCE, B, hB, ?_⟩
  intro μ hfin hreg a ha R hR M hM hloc
  obtain ⟨P⟩ := hPart n μ.support Measure.isClosed_support R hR
  exact ⟨P, h μ hfin hreg a ha R hR M hM hloc P⟩

/-- Direct partitions of every closed set. -/
theorem d1acomp_directPartition_exists : DirectPartitionExistsStatement :=
  d1acomp_directPartition_of (d1a_nestedNets_proof d1a_netExtension_proof) d1a_closedCellBasics_proof
    d1a_uniqueInner_proof d1a_childrenCount_proof d1a_assignment_proof d1a_protectedBalls_proof

/-- The forest energy. -/
theorem d1acomp_forestEnergy : ForestEnergyStatement :=
  d1a_forestEnergy_proof (d1a_descendantIntegral_proof d1a_coeffAnnulus_proof) d1a_cellMass_proof

/-- **Partition energy** (`PartitionEnergyStatement`, the type of `d1_hub_partitionEnergy`),
proved without further hypotheses. -/
theorem d1acomp_partitionEnergy : PartitionEnergyStatement :=
  d1acomp_partitionEnergy_of d1acomp_directPartition_exists d1acomp_forestEnergy

/-! ## Closed statements used downstream -/

/-- `CovarianceLowerStatement`, closed through upper recentring. -/
theorem d1acomp_covarianceLower : CovarianceLowerStatement :=
  d1a_covarianceLower_proof d1a_upperRecentering_proof

/-- `PlaneComparisonStatement`, closed through the covariance lower bound. -/
theorem d1acomp_planeComparison : PlaneComparisonStatement :=
  d1a_planeComparison_proof d1acomp_covarianceLower

/-- `FittingGapStatement`, closed through upper recentring. -/
theorem d1acomp_fittingGap : FittingGapStatement :=
  d1a_fittingGap_proof d1a_upperRecentering_proof

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
