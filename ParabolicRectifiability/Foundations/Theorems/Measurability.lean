import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.DensityMeasurability
import ParabolicRectifiability.Foundations.Proofs.RestrictRadon
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergyTwo
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergySmul
import ParabolicRectifiability.Foundations.Proofs.SquareEnergySmul
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo
import ParabolicRectifiability.Enhancements.Proofs.Domination.EnergyDomination
import ParabolicRectifiability.Foundations.Proofs.EnergyRescaling

/-! # Measurability, monotonicity, finite annuli, scaling; beta-`p` compatibility

Each theorem below has the exact type of the corresponding statement definition
(`DensityMeasurabilityStatement`, `AnnulusBoundStatement`, `SquareEnergyRescalingStatement`,
`BetaPowTwoStatement`, and so on).
-/

namespace ParabolicRectifiability.Foundations

/-- Borel measurability of both densities for a locally Radon source. Proved by
`fmeas1_density_measurability`. -/
theorem measurable_densities : DensityMeasurabilityStatement := by
  exact ParabolicRectifiability.Foundations.fmeas1_density_measurability

/-- Borel restrictions of a locally Radon source are locally Radon. Proved by
`restrict_isFiniteMeasureOnCompacts_innerRegular_proof`. -/
theorem restrict_locallyRadon : RestrictLocallyRadonStatement := by
  exact ParabolicRectifiability.Foundations.restrict_isFiniteMeasureOnCompacts_innerRegular_proof

/-- `ν ≤ c μ` gives `b_ν ≤ c b_μ` and `S_ν ≤ c S_μ`. -/
theorem betaSq_squareEnergy_le_of_le_smul : BetaEnergyDominationStatement := by
  exact ParabolicRectifiability.Foundations.fmeas3_betaSq_squareEnergy_le_of_le_ofReal_smul

/-- The finite-annulus bound. Proved by `lintegral_betaSq_Ioo_le_annulus_proof`. -/
theorem lintegral_betaSq_annulus_le : AnnulusBoundStatement := by
  exact ParabolicRectifiability.Foundations.lintegral_betaSq_Ioo_le_annulus_proof

/-- Square finiteness is independent of the finite positive endpoint. Proved by
`squareEnergy_lt_top_iff_of_endpoints_proof`. -/
theorem squareEnergy_lt_top_iff_of_pos : SquareFinitenessEndpointStatement := by
  exact ParabolicRectifiability.Foundations.squareEnergy_lt_top_iff_of_endpoints_proof

/-- The dilation identity `S_{μ_{q,R}}^A(z) = S_μ^{RA}(q + δ_R z)`. -/
theorem squareEnergy_rescaledSource : SquareEnergyRescalingStatement := by
  exact ParabolicRectifiability.Foundations.squareEnergy_rescaledSource_eq_proof

/-- `S_{cμ}^A = c S_μ^A` for real `c > 0` and every family. -/
theorem squareEnergy_ofReal_smul : SquareEnergySmulStatement := by
  exact ParabolicRectifiability.Foundations.f2i_squareEnergySmul_proof

/-- `B_2 = betaSq`. -/
theorem betaPow_two_eq_betaSq : BetaPowTwoStatement := by
  exact ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof

/-- `S_2^a = T_2^a = squareEnergy`. -/
theorem energyS_energyT_two_eq_squareEnergy : EnergyTwoStatement := by
  exact ParabolicRectifiability.Foundations.f2c_energyTwo_proof

/-- The amplitude laws `S_{p,cμ} = c^{2/p} S_{p,μ}` and `T_{p,cμ} = c T_{p,μ}`. -/
theorem energyS_energyT_ofReal_smul : EnergyPowSmulStatement := by
  exact ParabolicRectifiability.Foundations.f2c_energyPowSmul_proof

end ParabolicRectifiability.Foundations
