import ParabolicRectifiability.Geometry.Graphs

/-! # The closed-domain horizontal envelope

Defines `HorizontalClosedEnvelopeStatement`: every horizontal graph lies in a horizontal graph
of the same slope bound with closed domain. It is proved by
`fgenv_horizontal_closed_extension`; the variant with the conjunction reversed and the
compact-cover argument are derived from it.
-/

namespace ParabolicRectifiability.Foundations

/-- **Closed-domain horizontal envelope.**

Every horizontal graph `G` of slope at most `ε` over an arbitrary domain lies in a horizontal
graph `G'` of the same slope bound whose domain is closed in its direction.

Scope: the statement supplies a same-bound containing graph with closed domain, nothing more.
Preservation of direction and offset, literal equality `G'.domain = closure G.domain`,
uniqueness and equality of `G'.image` with the closure of `G.image` belong to the intended
construction but are not exposed by this type. Closure enlargement is not Hausdorff-null in
general: the flat graph over `ℚ ∩ [0,1]` has zero length, while its closure contains a unit
segment. -/
def HorizontalClosedEnvelopeStatement : Prop :=
  ∀ (n k : ℕ) (ε : ℝ) (G : HorizontalGraph n k ε),
    ∃ G' : HorizontalGraph n k ε, G.image ⊆ G'.image ∧ IsClosed G'.domain

end ParabolicRectifiability.Foundations
