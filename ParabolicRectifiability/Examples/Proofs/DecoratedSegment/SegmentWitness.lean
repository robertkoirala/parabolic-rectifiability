import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentLemmas
import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitLemmas
import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityLemmas

/-! # The decorated-segment witness: assembled properties

Combines the intermediate lemmas about the decorated-segment set `E = e2_sapSet` (proved in
`AboveTwoSegmentLeaves`), together with `e2_planarLine` (`E2PlanarLine`) and `e2_sb_slopeGraph`
(`E2sbSlopeGraph`), into the unconditional properties of `E` used for
`BetaP.DirectWitnessPlusStatement`: label bounds, Borel and bounded, mass bounds, the band bound
for the beta numbers, divergence of the energy off the endpoints, density, the zero-slope cover,
and countability of the endpoint set.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

/-- The bounds of the labelled segments. -/
theorem e2_sap_labelHub : E2sapLabelBounds :=
  e2_sap_labelBounds e2_sap_weights

/-- `E` is Borel and bounded. -/
theorem e2_sap_basicHub : E2sapSetBasic :=
  e2_sap_setBasic e2_sap_labelHub

/-- `1 ≤ H¹(E) ≤ 100/99`. -/
theorem e2_sap_massHub : E2sapMass :=
  e2_sap_mass (e2_sap_segment e2_sap_levelMeasure) e2_sap_labelHub
    (e2_sap_treeLength e2_sap_weights (e2_sap_generation e2_sap_weights))

/-- The band lower bound for the beta numbers of the full measure `H¹⌊E`. -/
theorem e2_sap_bandHub : E2sapBandBeta :=
  e2_sap_bandBeta
    (e2_sap_pairCost e2_planarLine (e2_sap_segment e2_sap_levelMeasure)
      (e2_sap_fit e2_sap_fitTilted))
    e2_sap_ballContain

/-- Divergence of the energy outside the endpoint set. -/
theorem e2_sap_divergenceHub : E2sapDivergenceOff :=
  e2_sap_divergence e2_sap_weights e2_sap_weightsDiverge e2_sap_labelHub e2_sap_bandHub
    e2_sap_cell e2_sap_bandEnergy

/-- Density `2` almost everywhere for countable unions of horizontal segments. -/
theorem e2_sap_densityHub : E2sapDensity :=
  e2_sap_density (e2_sap_levels e2_sap_levelMeasure) e2_sap_levelPoint e2_sap_levelAE

/-- The exact cover by horizontal graphs of slope zero. -/
theorem e2_sap_coverHub : E2sapCover :=
  e2_sap_cover e2_sb_slopeGraph

/-- The endpoint set `Z` is countable: a countable union of two-point sets. -/
theorem e2_sapEndpoints_countable : e2_sapEndpoints.Countable :=
  Set.countable_iUnion fun _ => (Set.toFinite _).countable

end ParabolicRectifiability.Examples
