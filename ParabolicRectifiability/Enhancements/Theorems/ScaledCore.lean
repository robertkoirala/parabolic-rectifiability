import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Enhancements.Assembly.ScaledCore
import ParabolicRectifiability.Composition.MainTheoremOne
import ParabolicRectifiability.Foundations.Assembly.ProvedStatements

/-! # The rectifiable Reifenberg decomposition on an arbitrary parent ball

Positive parabolic rescaling transports the unit theorem to `P(q,R)` and
energy scales `(0,2R)`. The remainder is bounded by `C * M * R^k + Γ`, with
the corresponding scaled local support bounds. The source remains the original
locally Radon measure. The precise mixed, fixed-family and ambient clauses are
in `ScaledRectifiableReifenbergCoreStatement`.

`scaled_rectifiable_reifenberg_core_of_providers` expresses the proof as an implication
from the unit theorem and energy rescaling; this file supplies both.
Graph-domain covers are added by `scaled_rectifiable_reifenberg`.
-/

namespace ParabolicRectifiability.Enhancements

/-- **Scaled rectifiable Reifenberg theorem without graph-domain covers**: the scaled rectifiable Reifenberg
theorem on an arbitrary parent ball `P(q,R)`, without the graph-domain clause. It follows
from the unit theorem `Composition.rectifiable_reifenberg_theorem` and the energy rescaling
identity `Foundations.squareEnergy_rescaledSource_eq`. -/
theorem scaled_rectifiable_reifenberg_core : ScaledRectifiableReifenbergCoreStatement := by
  exact scaled_rectifiable_reifenberg_core_of_providers Composition.rectifiable_reifenberg_theorem
    Foundations.squareEnergy_rescaledSource_eq

end ParabolicRectifiability.Enhancements
