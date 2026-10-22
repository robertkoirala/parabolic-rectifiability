import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.DifferentiationStatements
import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.CellAverages
import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.BorelGeneration
import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.LevyConvergence

/-! # Differentiation along nested partitions: the three intermediate statements

The three intermediate statements used to prove `CoordinateDifferentiationStatement`
(see `coordinate_differentiation_of_leaves`), each obtained from its proof module:
`b3_cd_cells` (partition filtration and conditional expectations), `b3_cd_generation`
(Borel generation) and `b3_cd_levy` (Lévy's upward theorem). The Lévy argument does not use
the Radon approximation `radon_approximation`. Statement (ii.b) takes the conclusions of (i)
and (ii.a) only as hypotheses of its own generic statement.
-/

noncomputable section

namespace ParabolicRectifiability.Characterization.CoordinateDifferentiationTree

/-- **(i)** `CdCellAverageStatement`: the partition filtration, the null union of zero-mass
cells, integrability of the cell averages (`∫|a_j| dρ ≤ ∫|h| dρ`) and their a.e.
identification with `𝔼[h | ℱ_j]` (proof sketch in the docstring of the statement). -/
theorem b3_cd_cells : CdCellAverageStatement := by
  exact ParabolicRectifiability.Characterization.CoordinateDifferentiationTree.bp2_cd_cells_proof

/-- **(ii.a)** `CdGenerationStatement`: Borel generation of the partition filtration under
shrinking cells (proof sketch in the docstring of the statement). -/
theorem b3_cd_generation : CdGenerationStatement := by
  exact ParabolicRectifiability.Characterization.CoordinateDifferentiationTree.bp2_cd_generation_proof

/-- **(ii.b)** `CdLevyStatement`: a.e. convergence of versions of `𝔼[h | ℱ_j]` by Lévy's
upward theorem (proof sketch in the docstring of the statement). -/
theorem b3_cd_levy : CdLevyStatement := by
  exact ParabolicRectifiability.Characterization.CoordinateDifferentiationTree.bp2_cd_levy_proof

end ParabolicRectifiability.Characterization.CoordinateDifferentiationTree
