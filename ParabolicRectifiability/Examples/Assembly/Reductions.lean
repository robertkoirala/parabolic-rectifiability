import ParabolicRectifiability.Examples.Assembly.IntermediateStatements

/-! # Exact reduction witnesses

The exact time-slice and stationary-product reductions do not depend on other results of
the library; `ReductionsStatement` is obtained directly from `reductions_bundle`.
-/

namespace ParabolicRectifiability.Examples

/-- The exact reductions `ReductionsStatement`, from `reductions_bundle`. -/
theorem reductions_skeleton : ReductionsStatement :=
  reductions_bundle

end ParabolicRectifiability.Examples
