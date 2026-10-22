import ParabolicRectifiability.Enhancements.Statements.MainTheorem
import ParabolicRectifiability.Composition.MainTheoremOne

/-!
# Rectifiable Reifenberg theorem with the general graph classes

`rectifiable_reifenberg_theorem` exports the mixed, available fixed-family and ambient
clauses of `RectifiableReifenbergTheoremStatement`. It retains the arbitrary
Radon source, Borel restrictions, compact actual supports fixed before every
graph tolerance, and remainder bound `C * M + Γ`. The compact-extension graphs
of the main statement are embedded in the general homogeneous regular class by the
compact bridge. `Composition.rectifiable_reifenberg_theorem` assembles this bridge and
the global and local support bounds. Graph-domain data are added separately
in `graph_enhanced_rectifiable_reifenberg`.
-/

namespace ParabolicRectifiability.Enhancements

/-- The rectifiable Reifenberg theorem: the mixed, available fixed-family and
ambient rectifiable Reifenberg conclusions with the general regular graph class.
`RectifiableReifenbergTheoremStatement` preserves all quantitative support bounds,
the zero threshold, and coefficient one on the exceptional mass `Γ`. -/
theorem rectifiable_reifenberg_theorem : RectifiableReifenbergTheoremStatement := by
  exact Composition.rectifiable_reifenberg_theorem

end ParabolicRectifiability.Enhancements
