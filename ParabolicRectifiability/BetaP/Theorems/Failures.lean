import ParabolicRectifiability.Examples.Assembly.Lacunary
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.AboveTwoWitness
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.DirectWitnesses
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFiniteness
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergyTwo
import ParabolicRectifiability.BetaP.Statements.Failures
import ParabolicRectifiability.BetaP.Proofs.Counterexamples.TimeSliceTransfer

/-! # Direct witnesses and failures of vanishing remainder bounds

`betaP_directWitnesses` collects two planar Hausdorff-source witnesses with opposite
`S_p` behavior and their constant-time transfer to `Space 2`, parabolic dimension `1`.
The transfer is an exact beta/energy and restricted-Hausdorff identity; it is specific
to sources supported on one time slice.

`betaP_failures` denies vanishing remainder estimates in the ranges excluded by the
support theorem: `S_p` for `0 < p < 2` at `n = 2`, `k = 1`, and `T_p` for `p > 2` at
`n = 1`, `k = 2`. These statements permit weaker good carriers than the support theorem,
so their conclusions are stronger impossibility assertions. The integrated `T_p` failure
uses the actual finite integrated energy, with no monotonicity or zero-value condition on
the proposed modulus.

Exact predicates and quantifiers are in the `…Statement` definitions; the proofs use
the time-slice, direct-witness, and lacunary constructions.
-/

namespace ParabolicRectifiability.BetaP

/-- Constant-time transfer at `n = 2`, `k = 1`: every planar source has exactly the
Euclidean horizontal/mixed `B_p` at every radius and `S_p^a` at every `a > 0`.
For Borel `E`, the time-slice pushforward of `H¹⌊E` is `H_P¹⌊ι(E)`
(`TimeSliceTransferStatement`). -/
theorem timeSlice_transfer : TimeSliceTransferStatement := by
  exact ParabolicRectifiability.BetaP.c2_timeSliceTransfer

/-- A compact purely one-unrectifiable planar set of Hausdorff measure `1` has
positive bounded upper density and bounded finite-endpoint `S_p`, for every `0 < p < 2`.
On one common full-measure set all positive-endpoint `S_2` diverge and lower density is
zero. Its constant-time image has Hausdorff-null intersection with every horizontal graph
(part (a); `DirectWitnessMinusStatement`). -/
theorem directWitness_minus : DirectWitnessMinusStatement := by
  exact directWitnessMinus_of_providers Characterization.b2_graph_source_square_finite Foundations.f2c_energyTwo_proof

/-- A bounded Borel union of nondegenerate planar horizontal segments has Hausdorff
measure in `[1,100/99]` and density ratio tending to `2` almost everywhere, while outside
one countable set all `S_p^a` diverge simultaneously for `p > 2`, `a > 0`. Its constant-time
image is exactly covered by slope-zero horizontal graphs (part (b);
`DirectWitnessPlusStatement`). -/
theorem directWitness_plus : DirectWitnessPlusStatement := by
  exact c2_directWitnessPlus

/-- The two direct Hausdorff-source witnesses and their exact constant-time transfer,
assembled as `DirectWitnessesStatement`. The minus witness
disproves sufficiency below `2`; the plus witness disproves necessity above `2` for `S_p`. -/
theorem betaP_directWitnesses : DirectWitnessesStatement :=
  ⟨directWitness_minus, directWitness_plus, timeSlice_transfer⟩

/-- For `0 < p < 2`, no nonnegative modulus `Φ(M) → 0` as `M ↓ 0` gives a universal
`S_p^2` threshold remainder bound `Φ(M) + Γ` at `n = 2`, `k = 1`, even allowing
one good measure carried by a compact set covered modulo `H_P¹` by finite-slope horizontal
graphs. Thresholds have `M > 0`, `Γ ≥ 0`. -/
theorem spBelowTwo_noVanishingRemainder : SpBelowTwoNoVanishingRemainderStatement := by
  exact spBelowTwo_noVanishingRemainder_of_witness (directWitnessMinus_of_providers Characterization.b2_graph_source_square_finite Foundations.f2c_energyTwo_proof) timeSliceTransfer_obligation

/-- For `p > 2`, no nonnegative modulus `Φ(M) → 0` as `M ↓ 0` gives a universal
`T_p^2` threshold remainder bound `Φ(M) + Γ` at `n = 1`, `k = 2`, even allowing
one good measure on an arbitrary countably regular carrier modulo a Hausdorff-null set. -/
theorem tpAboveTwo_noVanishingRemainder : TpAboveTwoNoVanishingRemainderStatement := by
  exact tpAboveTwo_noVanishingRemainder_of_witness lacunaryFrequencyExistence_obligation (Examples.exponent_witness_above_carrier_of_providers Characterization.b2_graph_source_square_finite Foundations.f2c_energyTwo_proof) Examples.exponent_witness_above_energy_skeleton

/-- For `p > 2`, no nonnegative modulus `Ψ(e) → 0` as `e ↓ 0` bounds the unit-ball
remainder by `Ψ(e)` for every locally Radon source at `n = 1`, `k = 2` with finite actual
energy `e = ∫_{P(0,1)} T_p^2 dμ`, even with arbitrary countably regular good carriers
modulo Hausdorff-null residuals. No monotonicity or prescribed value at zero is assumed
for `Ψ`. -/
theorem tpAboveTwo_noIntegratedRemainder : TpAboveTwoNoIntegratedRemainderStatement := by
  exact tpAboveTwo_noIntegratedRemainder_of_witness lacunaryFrequencyExistence_obligation (Examples.exponent_witness_above_carrier_of_providers Characterization.b2_graph_source_square_finite Foundations.f2c_energyTwo_proof) Examples.exponent_witness_above_energy_skeleton

/-- The three impossibility assertions outside the support ranges, assembled as
`BetaPFailuresStatement`: below-two `S_p` threshold loss, above-two
`T_p` threshold loss, and above-two integrated `T_p` loss, each in its specified dimension. -/
theorem betaP_failures : BetaPFailuresStatement :=
  ⟨spBelowTwo_noVanishingRemainder, tpAboveTwo_noVanishingRemainder,
    tpAboveTwo_noIntegratedRemainder⟩

end ParabolicRectifiability.BetaP
