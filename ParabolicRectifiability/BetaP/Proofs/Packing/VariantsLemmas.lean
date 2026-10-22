import ParabolicRectifiability.BetaP.Proofs.Packing.VariantsStatements
import ParabolicRectifiability.BetaP.Proofs.Packing.CellPartition
import ParabolicRectifiability.BetaP.Proofs.Packing.Subfamily
import ParabolicRectifiability.BetaP.Proofs.Packing.CellTail

/-! # Variants of active-radius packing: the intermediate results

The three intermediate results used by `c2_activeRadiusPacking_variants` (cell partition,
subfamilies, cell tail), each a restatement of the corresponding `…_proof` theorem. The other
inputs are the all-scale bound `ActiveRadiusPackingBound` (a hypothesis of
`activeRadiusPacking_variants`), `cpk2_betaPow_mono_measure` and the radius bound
`radius_le_of_ball_subset`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Cell partition** (`c2_CellPartitionStatement`), used for the unit-parent bound. -/
theorem c2_cellPartition : c2_CellPartitionStatement := by exact ParabolicRectifiability.BetaP.c2_cellPartition_proof

/-- **Subfamilies** (`c2_SubfamilyStatement`), used for the cells of the unit-parent bound and
for the complement of the exceptional set in both exceptional bounds. -/
theorem c2_subfamily : c2_SubfamilyStatement := by exact ParabolicRectifiability.BetaP.c2_subfamily_proof

/-- **Cell tail** (`c2_CellTailStatement`), used for the unit-parent bound. -/
theorem c2_cellTail : c2_CellTailStatement := by exact ParabolicRectifiability.BetaP.c2_cellTail_proof

end ParabolicRectifiability.BetaP
