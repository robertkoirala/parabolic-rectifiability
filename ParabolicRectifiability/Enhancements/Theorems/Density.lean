import ParabolicRectifiability.Enhancements.Statements.Density
import ParabolicRectifiability.Enhancements.Assembly.Density
import ParabolicRectifiability.Composition.MainTheoremOne
import ParabolicRectifiability.Foundations.Proofs.EnergyRescaling
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.PackingMass
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.UpperDomination
import ParabolicRectifiability.Foundations.Assembly.DensityBridges
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.DensityMeasurability
import ParabolicRectifiability.Enhancements.Proofs.Domination.EnergyDomination
import ParabolicRectifiability.Foundations.Proofs.RestrictRadon
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.Criterion

/-! # Density corollaries

The density corollaries of the rectifiable Reifenberg theorem: `density_three_parts`,
`density_rectifiable_reifenberg` and `density_scaling`. Each is obtained from the corresponding
implication `…_of_providers` by supplying the compact bridge, energy rescaling, packing mass,
upper density domination, the absolute-continuity bridge, density measurability, beta/energy
domination, restriction of Radon measures and the finite-Hausdorff criterion.
-/

namespace ParabolicRectifiability.Enhancements

/-- **All three density conclusions.** Statement: `DensityThreePartsStatement`. -/
theorem density_three_parts : DensityThreePartsStatement := by
  exact density_three_parts_of_providers Composition.compactBridgeCover_proof
    Foundations.squareEnergy_rescaledSource_eq_proof Foundations.fpack_packing_mass
    Foundations.fupdom_upper_density_domination Foundations.ac_bridge_skeleton
    Foundations.fmeas1_density_measurability
    Foundations.fmeas3_betaSq_squareEnergy_le_of_le_ofReal_smul
    Foundations.restrict_isFiniteMeasureOnCompacts_innerRegular_proof
    Characterization.b4_finite_hausdorff_criterion

/-- **Rectifiable Reifenberg density bounds.** Statement: `DensityRectifiableReifenbergStatement`. -/
theorem density_rectifiable_reifenberg : DensityRectifiableReifenbergStatement := by
  exact density_rectifiable_reifenberg_of_providers Composition.compactBridgeCover_proof
    Foundations.fpack_packing_mass Foundations.fupdom_upper_density_domination
    Foundations.fmeas1_density_measurability
    Foundations.restrict_isFiniteMeasureOnCompacts_innerRegular_proof

/-- **All local scales and their exact normalization.** Statement:
`DensityScalingStatement`. -/
theorem density_scaling : DensityScalingStatement := by
  exact density_scaling_of_providers Composition.compactBridgeCover_proof
    Foundations.squareEnergy_rescaledSource_eq_proof Foundations.fpack_packing_mass
    Foundations.fupdom_upper_density_domination Foundations.ac_bridge_skeleton
    Foundations.fmeas1_density_measurability
    Foundations.fmeas3_betaSq_squareEnergy_le_of_le_ofReal_smul
    Foundations.restrict_isFiniteMeasureOnCompacts_innerRegular_proof
    Characterization.b4_finite_hausdorff_criterion

end ParabolicRectifiability.Enhancements
