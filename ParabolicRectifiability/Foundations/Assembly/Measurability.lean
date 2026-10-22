import ParabolicRectifiability.Foundations.Assembly.ProvedStatements

/-! # Measurability, scaling and beta-`p` compatibility

Each statement (`DensityMeasurabilityStatement`, `SquareEnergyRescalingStatement`,
`BetaPowTwoStatement`, and so on: measurability, scaling and the compatibility claims for the
beta-`p` quantities) is an independent lemma, proved by the corresponding theorem
(`densities_measurable_of_locallyRadon`, `squareEnergy_rescaledSource_eq`, and so on).
-/

namespace ParabolicRectifiability.Foundations

/-- Borel densities of a locally Radon source. -/
theorem density_measurability_skeleton : DensityMeasurabilityStatement :=
  densities_measurable_of_locallyRadon

/-- Borel restrictions of a locally Radon source are locally Radon. -/
theorem restrict_locallyRadon_skeleton : RestrictLocallyRadonStatement :=
  restrict_isFiniteMeasureOnCompacts_innerRegular

/-- Domination of beta and energy. -/
theorem beta_energy_domination_skeleton : BetaEnergyDominationStatement :=
  betaSq_squareEnergy_le_of_le_ofReal_smul

/-- The finite-annulus bound. -/
theorem annulus_bound_skeleton : AnnulusBoundStatement :=
  lintegral_betaSq_Ioo_le_annulus

/-- Endpoint independence of finiteness of the square energy. -/
theorem square_finiteness_endpoint_skeleton : SquareFinitenessEndpointStatement :=
  squareEnergy_lt_top_iff_of_endpoints

/-- Dilation law of the square energy. -/
theorem square_energy_rescaling_skeleton : SquareEnergyRescalingStatement :=
  squareEnergy_rescaledSource_eq

/-- Scalar law of the square energy. -/
theorem square_energy_smul_skeleton : SquareEnergySmulStatement :=
  squareEnergy_ofReal_smul_eq

/-- `B_2 = b`. -/
theorem beta_pow_two_skeleton : BetaPowTwoStatement :=
  betaPow_two_eq_betaSq_all

/-- `S_2 = T_2 = S`. -/
theorem energy_two_skeleton : EnergyTwoStatement :=
  energyS_energyT_two_eq

/-- Amplitude laws of the beta-`p` energies. -/
theorem energy_pow_smul_skeleton : EnergyPowSmulStatement :=
  energyS_energyT_ofReal_smul_eq

end ParabolicRectifiability.Foundations
