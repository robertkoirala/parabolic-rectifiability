import ParabolicRectifiability.QuantitativeCharacterization.Statements.Pieces
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Pieces
import ParabolicRectifiability.Characterization.Assembly.Branches
import ParabolicRectifiability.Foundations.Proofs.RestrictRadon

/-! # Endpoints: quantitative coverings and qualitative regular rectifiability

The theorems assemble the exact specifications in the `Statements` module of the same name.
-/

set_option autoImplicit false

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **A measure with a quantitative covering is rectifiable.** The proof uses the reference
estimates and intrinsic sufficiency. Statement: `AnyCoverRectifiableStatement`. -/
theorem any_cover_rectifiable : AnyCoverRectifiableStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.any_cover_rectifiable_of_providers ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton

/-- **Countable quantitative pieces.** The proof uses typed refinement and
`any_cover_rectifiable`. Statement: `CountableQuantitativePiecesStatement`. -/
theorem countable_quantitative_pieces : CountableQuantitativePiecesStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.countable_quantitative_pieces_of_providers ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton ParabolicRectifiability.Characterization.typed_refinement_measure_skeleton ParabolicRectifiability.Foundations.restrict_isFiniteMeasureOnCompacts_innerRegular_proof

end ParabolicRectifiability.QuantitativeCharacterization
