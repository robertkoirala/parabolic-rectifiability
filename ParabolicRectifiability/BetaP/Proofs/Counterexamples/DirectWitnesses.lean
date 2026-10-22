import ParabolicRectifiability.BetaP.Proofs.Corollaries.WitnessRows

/-! # Direct witnesses and remainder failures

* The witness `E₋`: the elementary digit construction (`belowTwoDigitWitness_exists`) gives the
  planar conclusions, `belowTwoDigitWitness_pure_of_graphSource` gives pure unrectifiability
  and graph-intersection nullity from `Characterization.GraphSourceStatement`, the time-slice
  transfer and `EnergyTwoStatement`, and `directWitnessMinusStatement_iff` reassembles the
  statement.
* The direct-witness statement is the conjunction of `E₋`, the witness above two and the
  time-slice transfer.
* Each failure theorem is its implication-form statement applied to its inputs: `E₋` and the
  transfer for the `S_p` failure; the lacunary frequency existence and the lacunary witness
  statements (hypotheses) for the two `T_p` failures.
-/

noncomputable section

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **The witness `E₋`** (part (a) of the direct witnesses). Inputs: `GraphSourceStatement` and
`EnergyTwoStatement`, together with the digit witness and the time-slice transfer. -/
theorem directWitnessMinus_of_providers (hGS : Characterization.GraphSourceStatement)
    (hE2 : EnergyTwoStatement) : DirectWitnessMinusStatement := by
  obtain ⟨E, hE⟩ := belowTwoDigitWitness_exists
  exact directWitnessMinusStatement_iff.mpr
    ⟨E, hE, belowTwoDigitWitness_pure_of_graphSource hGS timeSliceTransfer_obligation hE2 hE⟩

/-- **Direct witnesses.** Inputs (through `E₋`): `GraphSourceStatement` and
`EnergyTwoStatement`. -/
theorem betaPDirectWitnesses_of_providers (hGS : Characterization.GraphSourceStatement)
    (hE2 : EnergyTwoStatement) : DirectWitnessesStatement :=
  ⟨directWitnessMinus_of_providers hGS hE2, directWitnessPlus_obligation,
    timeSliceTransfer_obligation⟩

/-- **Remainder failures.** Inputs: `GraphSourceStatement` and `EnergyTwoStatement` (through
`E₋`), and `ExponentWitnessAboveCarrierStatement` and `ExponentWitnessAboveEnergyStatement`. -/
theorem betaPFailures_of_providers (hGS : Characterization.GraphSourceStatement)
    (hE2 : EnergyTwoStatement) (hEWAC : Examples.ExponentWitnessAboveCarrierStatement)
    (hEWAE : Examples.ExponentWitnessAboveEnergyStatement) : BetaPFailuresStatement :=
  ⟨spBelowTwo_noVanishingRemainder_of_witness (directWitnessMinus_of_providers hGS hE2)
      timeSliceTransfer_obligation,
    tpAboveTwo_noVanishingRemainder_of_witness lacunaryFrequencyExistence_obligation hEWAC hEWAE,
    tpAboveTwo_noIntegratedRemainder_of_witness lacunaryFrequencyExistence_obligation hEWAC
      hEWAE⟩

end ParabolicRectifiability.BetaP
