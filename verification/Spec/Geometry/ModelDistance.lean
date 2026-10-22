import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Geometry.ModelDistance` used by the headline statements. -/

noncomputable section
namespace ParabolicRectifiability
open scoped ENNReal
/-- Squared distance to the represented set in the parabolic metric. -/
def modelCost {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n) : ℝ≥0∞ :=
  (Metric.infEDist z (modelSet L)) ^ 2

namespace AffineSpatialPlane
variable {n m : ℕ}
end AffineSpatialPlane
namespace HorizontalModel
variable {n k : ℕ}
end HorizontalModel
namespace VerticalModel
variable {n k : ℕ}
end VerticalModel
end ParabolicRectifiability
