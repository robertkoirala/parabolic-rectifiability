import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.PackingMass
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperDomination
import ParabolicRectifiability.Foundations.Assembly.DensityBridges

/-! # The three density lemmas

Each theorem below has the exact type of the corresponding statement definition
(`PackingMassStatement`, `UpperDensityDominationStatement`, `ACBridgeStatement`):
`packing_mass_bound` is proved by `fpack_packing_mass`, `hausdorffP_le_of_upperDensity` by
`fupdom_upper_density_domination` and `absolutelyContinuous_of_lowerDensity_squareEnergy` by
`ac_bridge_skeleton`.

* `packing_mass_bound` and `hausdorffP_le_of_upperDensity` are covering
  arguments (fivefold selection).
* `absolutelyContinuous_of_lowerDensity_squareEnergy` consumes the core rectifiable Reifenberg theorem
  with its packing output (`family_rectifiable_reifenberg`) together with
  `packing_mass_bound`.
-/

namespace ParabolicRectifiability.Foundations

/-- Packing turns lower density into retained mass. Proved by `fpack_packing_mass`. -/
theorem packing_mass_bound : PackingMassStatement := by
  exact ParabolicRectifiability.Foundations.fpack_packing_mass

/-- Positive upper density gives Hausdorff domination. Proved by
`fupdom_upper_density_domination`. -/
theorem hausdorffP_le_of_upperDensity : UpperDensityDominationStatement := by
  exact ParabolicRectifiability.Foundations.fupdom_upper_density_domination

/-- The absolute-continuity bridge. Proved by `ac_bridge_skeleton`, which combines the packing
lemma, the bounded-growth constant and the growth criterion for absolute continuity. -/
theorem absolutelyContinuous_of_lowerDensity_squareEnergy : ACBridgeStatement := by
  exact ParabolicRectifiability.Foundations.ac_bridge_skeleton

end ParabolicRectifiability.Foundations
