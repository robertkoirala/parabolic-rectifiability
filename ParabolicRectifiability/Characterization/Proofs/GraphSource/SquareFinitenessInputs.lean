import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceEstimates
import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.Transfer
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds
import ParabolicRectifiability.Foundations.Proofs.AmbientEnergy
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Input statements for square finiteness and density bounds of graph sources

Each declaration is a statement established elsewhere in the library, restated here with its
type so that the arguments for `b2_graph_source_square_finite` and `b2_graph_density_bounds` can use it.
They are stated (and used) as separate declarations so that no import cycle arises.
-/

noncomputable section

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- Uniform ADR and Carleson energy of every typed `L`-reference
(`QuantitativeCharacterization.reference_estimates`). Used by `b2_reference_adr_square`. -/
theorem b2_input_reference_estimates : ReferenceEstimatesStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.ba1_reference_estimates

/-- Transfer of square finiteness from an ADR measure to a source
(`Characterization.adr_source_transfer`). Used by `b2_reference_source_null`. -/
theorem b2_input_source_transfer : SourceTransferStatement := by
  exact ParabolicRectifiability.Characterization.SourceTransferTree.adr_source_transfer_of_leaves

/-- Finiteness of the square at a point does not depend on the positive endpoint
(`Foundations.squareEnergy_lt_top_iff_of_endpoints`). Used by `b2_endpoint_null`: finite
annuli give every endpoint. -/
theorem b2_input_square_finiteness_endpoint : SquareFinitenessEndpointStatement := by
  exact ParabolicRectifiability.Foundations.squareEnergy_lt_top_iff_of_endpoints_proof

/-- At `k = n + 2` the available squares vanish identically
(`Foundations.ambient_betaSq_squareEnergy_eq_zero`, whose statement form is
`AmbientEnergyZeroStatement`). Used by the ambient branch of
`b2_graph_source_square_finite`: at `k = n+2` the only graph and model are the whole ambient
space, so the square is identically zero. -/
theorem b2_input_ambient_energy_zero : AmbientEnergyZeroStatement := by
  exact fun n hn μ _ _ T hT => ParabolicRectifiability.Foundations.ambient_betaSq_squareEnergy_eq_zero_proof n hn μ T hT

end ParabolicRectifiability.Characterization
