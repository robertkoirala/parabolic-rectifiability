import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Foundations.Statements.CompactBridge
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.SubspaceCoordinates
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.Theorems.CompactBridge` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace ParabolicRectifiability.Foundations
/-- Representative identification for the compact bridge. Statement:
`CompactBridgeRepresentativeStatement` (no compact-support or Lipschitz
hypothesis). The proof uses `|D_t|^{1/2}φ ∈ L¹`,
`∫ |D_t|^{1/2}φ = 0`, Fubini for the product-integrable pairing, which also yields the
inner and window integrability clauses, and the limit of the time windows.
It is the input of the two inclusions below. -/
theorem representsGeneralHalfTimeDerivative_of_compactPerturbation :
    CompactBridgeRepresentativeStatement := by
  sorry

/-- Function inclusion at the same tolerance. The proof keeps the
same representative `g`, Lipschitz bound `L` and BMO bound `B`. It uses
`representsGeneralHalfTimeDerivative_of_compactPerturbation`. -/
theorem isGeneralRegularVerticalFunction_of_isRegularVerticalFunction :
    CompactBridgeFunctionStatement := by
  sorry

/-- Cover inclusion without loss of tolerance. Each core graph
keeps its direction, offset and function. It uses
`representsGeneralHalfTimeDerivative_of_compactPerturbation`. -/
theorem hasGeneralRegularVerticalGraphCover_of_hasRegularVerticalGraphCover :
    CompactBridgeCoverStatement := by
  sorry

end ParabolicRectifiability.Foundations
