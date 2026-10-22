import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IsLUB
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.ModelDistance
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Measure.CountableFitting` used by the headline statements. -/

noncomputable section
open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal
namespace ParabolicRectifiability
/-- Unnormalized integral of the already squared geometric distance. -/
def fit {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in Metric.ball z r, modelCost L w ∂μ

end ParabolicRectifiability
