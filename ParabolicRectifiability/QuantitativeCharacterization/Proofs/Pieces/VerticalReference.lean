import ParabolicRectifiability.QuantitativeCharacterization.Statements.PiecesComponents
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapters
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Monotonicity

/-! # Vertical references

`dp2_vertical_reference_proof` (statement `dp2_VerticalReferenceStatement`). The adapter at `ε = 1`
gives a vertical `(1 + 1)`-reference with carrier `G.image`; `VerticalReference.mono` lifts it to
`L_* = max 2 √(1+n)` with the same data. -/

set_option autoImplicit false

namespace ParabolicRectifiability.QuantitativeCharacterization

theorem dp2_vertical_reference_proof : dp2_VerticalReferenceStatement := by
  intro n k hk G
  obtain ⟨V, hV⟩ := ParabolicRectifiability.Characterization.b2_vertical_graph_reference n k hk 1 G
  exact ⟨V.mono (by norm_num [le_max_iff]), hV⟩

end ParabolicRectifiability.QuantitativeCharacterization
