import ParabolicRectifiability.Foundations.Theorems.Ambient
import ParabolicRectifiability.Examples.Assembly.Lacunary
import ParabolicRectifiability.BetaP.Statements.Corollaries
import ParabolicRectifiability.BetaP.Proofs.Corollaries.Classification
import ParabolicRectifiability.Characterization.Theorems.Main
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergyTwo
import ParabolicRectifiability.Characterization.Assembly.Branches
import ParabolicRectifiability.BetaP.Proofs.Corollaries.GraphEnhancement
import ParabolicRectifiability.Composition.MainTheoremOne
import ParabolicRectifiability.Foundations.Proofs.Ambient.LocalCore
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.Criterion
import ParabolicRectifiability.Enhancements.Assembly.GraphDomains
import ParabolicRectifiability.BetaP.Proofs.Corollaries.IntegratedRates
import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTests
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergySmul

/-! # Graph domains, integral rates, and the beta-`p` classification

`betaP_graphEnhancement` strengthens the support theorem with graph-domain covers of the
same fixed supports at every positive tolerance and mesh. `betaP_integratedRate` gives
the remainder bounds obtained from finite integrated full-source energy, and
`betaP_integratedSharpness` proves that the displayed amplitude powers are forced for
bounds uniform over all amplitudes of the diffuse source.

`betaP_classification` collects the necessity/sufficiency table for `S_p` and `T_p` under
positive finite upper density, the ambient endpoint, and positive-endpoint invariance.
The positive implications are universal over the stated dimensions and sources; the
negative entries give counterexamples in their stated dimensions. The corresponding
`…Statement` definitions record all hypotheses and the distinction between
`IsRegularlyRectifiableMeasure` and the stronger conclusion with arbitrary-tolerance covers.

The proofs use the qualitative characterization, the graph-domain results and the examples.
-/

namespace ParabolicRectifiability.BetaP

/-- The beta-`p` support decomposition with graph-domain cost bounds on its own supports
(`BetaPGraphEnhancementStatement`). It has the same unit, localized, ambient, and
zero-threshold clauses as `BetaPSupportStatement`. The measures and actual compact supports are chosen
before every positive graph tolerance and mesh; `HasGraphDomainCostBounds` adds total
cost `C R^k` and local cost `C s^k` for `0 < s ≤ R`. -/
theorem betaP_graphEnhancement : BetaPGraphEnhancementStatement := by exact ParabolicRectifiability.BetaP.betaPGraphEnhancement_of_providers ParabolicRectifiability.Composition.rectifiable_reifenberg_theorem ParabolicRectifiability.Foundations.f3_ambient_local_core_bounds_proof ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof ParabolicRectifiability.Characterization.b4_finite_hausdorff_criterion ParabolicRectifiability.Characterization.typed_refinement_set_skeleton ParabolicRectifiability.Enhancements.fixed_carrier_graph_domain_skeleton

/-- Finite integrated full-source energy gives the support and graph-domain conclusions
with local remainder `C R^{2k/(p+2)} ℰ^{p/(p+2)}` for `p ≥ 2`, where
`ℰ = ∫_{P(q,R)} S_p^{2R} dμ`, or `C R^{k/2} 𝒯^{1/2}` for `0 < p ≤ 2`, where
`𝒯 = ∫_{P(q,R)} T_p^{2R} dμ`. Zero integrated energy gives zero local remainder
(exact hypotheses in `BetaPIntegratedRateStatement`). -/
theorem betaP_integratedRate : BetaPIntegratedRateStatement := by exact ParabolicRectifiability.BetaP.betaPIntegratedRate_of_providers ParabolicRectifiability.Composition.rectifiable_reifenberg_theorem ParabolicRectifiability.Foundations.f3_ambient_local_core_bounds_proof ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof ParabolicRectifiability.Characterization.b4_finite_hausdorff_criterion ParabolicRectifiability.Characterization.typed_refinement_set_skeleton ParabolicRectifiability.Enhancements.fixed_carrier_graph_domain_skeleton

/-- The amplitude powers `p/(p+2)` for integrated `S_p`, `p ≥ 2`, and `1/2` for
integrated `T_p`, `0 < p ≤ 2`, are forced for pure-power bounds uniform over all
amplitudes `c > 0` of the diffuse source, when `1 ≤ k < n + 2`.
The negative assertion already allows one good measure on any sigma-finite Hausdorff
carrier; it does not claim an optimal numerical constant. -/
theorem betaP_integratedSharpness : BetaPIntegratedSharpnessStatement := by
  exact ParabolicRectifiability.BetaP.betaPIntegratedSharpness_of_providers ParabolicRectifiability.Foundations.f2c_energyPowSmul_proof ParabolicRectifiability.Examples.e2_diffuseTest

/-- For each `0 < p < 2` and `a > 0`, there is a locally Radon source in `Space 2`
with positive finite upper `1`-density and finite `S_p^a` almost everywhere that is not
regularly rectifiable. This is the negative sufficiency entry at `n = 2`, `k = 1`.
See `SpBelowTwoNotSufficientStatement` for the full specification. -/
theorem spBelowTwo_notSufficient : SpBelowTwoNotSufficientStatement := by
  exact spBelowTwo_notSufficient_of_witness (directWitnessMinus_of_providers Characterization.b2_graph_source_square_finite Foundations.f2c_energyTwo_proof) timeSliceTransfer_obligation

/-- For `1 ≤ k < n + 2`, regular mixed measure rectifiability implies full-source
`S_p^a < ∞` almost everywhere for every fixed `0 < p < 2` and `a > 0`.
The source is locally Radon and has positive finite upper density almost everywhere.
See `SpBelowTwoNecessaryStatement` for the full specification. -/
theorem spBelowTwo_necessary : SpBelowTwoNecessaryStatement := by exact ParabolicRectifiability.BetaP.spBelowTwoNecessary_glue ParabolicRectifiability.Characterization.necessity_skeleton

/-- For `1 ≤ k < n + 2`, finiteness almost everywhere of either `S_2^a` or `T_2^a`,
`a > 0`, implies regular mixed measure rectifiability and covers at every positive bound.
The source is locally Radon and has positive finite upper density almost everywhere.
See `SquareSufficientStatement` for the full specification. -/
theorem square_sufficient : SquareSufficientStatement := by exact ParabolicRectifiability.BetaP.squareSufficient_glue ParabolicRectifiability.Characterization.qualitative_characterization ParabolicRectifiability.Foundations.f2c_energyTwo_proof

/-- For `1 ≤ k < n + 2`, regular mixed measure rectifiability implies both
`S_2^a < ∞` and `T_2^a < ∞` almost everywhere at every fixed `a > 0`.
The source is locally Radon and has positive finite upper density almost everywhere.
See `SquareNecessaryStatement` for the full specification. -/
theorem square_necessary : SquareNecessaryStatement := by exact ParabolicRectifiability.BetaP.squareNecessary_glue ParabolicRectifiability.Characterization.necessity_skeleton ParabolicRectifiability.Foundations.f2c_energyTwo_proof

/-- For `1 ≤ k < n + 2`, `p > 2`, and `a > 0`, full-source `S_p^a` finiteness
almost everywhere implies regular mixed measure rectifiability with arbitrary-positive-bound
covers. The source is locally Radon and has positive finite upper density almost everywhere.
See `SpAboveTwoSufficientStatement` for the full specification. -/
theorem spAboveTwo_sufficient : SpAboveTwoSufficientStatement := by exact ParabolicRectifiability.BetaP.spAboveTwoSufficient_glue ParabolicRectifiability.Characterization.qualitative_characterization

/-- For each `p > 2` and `a > 0`, there is a locally Radon source in `Space 2`
with positive finite upper `1`-density, regular rectifiability and covers at every positive
slope, for which `S_p^a` finiteness fails on a set of positive source mass.
See `SpAboveTwoNotNecessaryStatement` for the full specification. -/
theorem spAboveTwo_notNecessary : SpAboveTwoNotNecessaryStatement := by
  exact spAboveTwo_notNecessary_of_witness directWitnessPlus_obligation timeSliceTransfer_obligation

/-- For `1 ≤ k < n + 2`, `0 < p < 2`, and `a > 0`, full-source `T_p^a` finiteness
almost everywhere implies regular mixed measure rectifiability with covers at every positive
bound. The source is locally Radon and has positive finite upper density almost everywhere.
See `TpBelowTwoSufficientStatement` for the full specification. -/
theorem tpBelowTwo_sufficient : TpBelowTwoSufficientStatement := by exact ParabolicRectifiability.BetaP.tpBelowTwoSufficient_glue ParabolicRectifiability.Characterization.qualitative_characterization ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof

/-- For each `0 < p < 2` and `a > 0`, there is a locally Radon source in `Space 1`
with positive finite upper `2`-density, regular rectifiability and arbitrary-positive-bound
covers, for which `T_p^a` finiteness fails on a set of positive source mass.
See `TpBelowTwoNotNecessaryStatement` for the full specification. -/
theorem tpBelowTwo_notNecessary : TpBelowTwoNotNecessaryStatement := by
  obtain ⟨hIso, hBall, hHs, hDensity, hFull, hUpper, hLower, hSmall⟩ := Examples.lacunary_estimates_bundle
  exact tpBelowTwo_notNecessary_of_witness lacunaryFrequencyExistence_obligation Examples.exponent_witness_below_bundle hFull hHs Characterization.qualitative_characterization

/-- For each `p > 2` and `a > 0`, there is a locally Radon source in `Space 1`
with positive finite upper `2`-density and finite `T_p^a` almost everywhere that is not
regularly rectifiable. This is the negative sufficiency entry at `n = 1`, `k = 2`.
See `TpAboveTwoNotSufficientStatement` for the full specification. -/
theorem tpAboveTwo_notSufficient : TpAboveTwoNotSufficientStatement := by
  obtain ⟨hIso, hBall, hHs, hDensity, hFull, hUpper, hLower, hSmall⟩ := Examples.lacunary_estimates_bundle
  exact tpAboveTwo_notSufficient_of_witness lacunaryFrequencyExistence_obligation (Examples.exponent_witness_above_carrier_of_providers Characterization.b2_graph_source_square_finite Foundations.f2c_energyTwo_proof) Examples.exponent_witness_above_energy_skeleton hDensity

/-- For `1 ≤ k < n + 2`, regular mixed measure rectifiability implies full-source
`T_p^a < ∞` almost everywhere for every fixed `p > 2` and `a > 0`.
The source is locally Radon and has positive finite upper density almost everywhere.
See `TpAboveTwoNecessaryStatement` for the full specification. -/
theorem tpAboveTwo_necessary : TpAboveTwoNecessaryStatement := by exact ParabolicRectifiability.BetaP.tpAboveTwoNecessary_glue ParabolicRectifiability.Characterization.necessity_skeleton ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof

/-- At `k = n + 2`, a locally Radon source with positive finite upper density is
regularly rectifiable with arbitrary-positive-bound covers. For every `p > 0`, `a > 0`,
and available family, both energies vanish identically; their finiteness is therefore
both necessary and sufficient in this setting.
See `ClassificationAmbientStatement` for the full specification. -/
theorem classification_ambient : ClassificationAmbientStatement := by
  exact classificationAmbient_glue Foundations.ambient_characterization Foundations.ambient_zero_graph_cover_all_proof

/-- For a locally Radon source, every family, `p > 0`, and centre, finiteness of
each of `S_p^a` and `T_p^a` is independent of the positive endpoint `a`. Unavailable
families are included: both energies are infinite at every positive endpoint.
See `BetaPEndpointInvarianceStatement` for the full specification. -/
theorem betaP_endpointInvariance : BetaPEndpointInvarianceStatement := by exact ParabolicRectifiability.BetaP.betaPEndpointInvariance_skeleton

/-- The complete beta-`p` classification: the ten
necessity/sufficiency entries for `k < n + 2`, the ambient endpoint, and endpoint invariance.
The universal positive implications retain the density hypothesis; the negative entries
are existential counterexamples in the exact dimensions specified by their statements.
See `BetaPClassificationStatement` for the full specification. -/
theorem betaP_classification : BetaPClassificationStatement :=
  ⟨spBelowTwo_notSufficient, spBelowTwo_necessary, square_sufficient, square_necessary,
    spAboveTwo_sufficient, spAboveTwo_notNecessary, tpBelowTwo_sufficient,
    tpBelowTwo_notNecessary, tpAboveTwo_notSufficient, tpAboveTwo_necessary,
    classification_ambient, betaP_endpointInvariance⟩

end ParabolicRectifiability.BetaP
