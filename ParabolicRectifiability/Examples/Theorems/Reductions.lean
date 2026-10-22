import ParabolicRectifiability.Examples.Statements.Reductions
import ParabolicRectifiability.Examples.Assembly.Reductions

/-! # Exact time-slice and stationary-product reductions

`exact_reductions` proves `ReductionsStatement`, a conjunction of four exact
identities and comparisons. A source carried by one constant time slice has
the Euclidean beta-`p` quantities and energies; its ambient tube volume is the spatial
tube volume multiplied by `2r²`. These identities concern a special space-time source,
and do not assert a general statement about slices of an arbitrary source.

The stationary-product clauses instead concern `ν ⊗ (L¹⌊[-1,1])`: the vertical square
has an exact time-length factor, while the mixed square is comparable to its Euclidean
spatial counterpart for `0 < r ≤ 2`. The graph extension clause produces a full
time-independent general regular vertical graph from an arbitrary spatial subset graph.
-/

namespace ParabolicRectifiability.Examples

/-- The exact Euclidean reductions: constant-time pushforwards
preserve horizontal and mixed beta-`p` energies; slice tubes have time factor `2r²`;
stationary products have the vertical identity and mixed comparison for `0 < r ≤ 2`;
and spatial subset graphs extend to full stationary general regular vertical graphs.
The four specifications and their dimension ranges are in `ReductionsStatement`. -/
theorem exact_reductions : ReductionsStatement := by
  exact ParabolicRectifiability.Examples.reductions_skeleton

end ParabolicRectifiability.Examples
