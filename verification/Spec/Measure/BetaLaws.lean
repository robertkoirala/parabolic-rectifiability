import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Analysis.Coordinates
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.ModelDistance
import Spec.Measure.Beta
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Measure
import Spec.Metric.Similarity
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Measure.BetaLaws` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability
/-- The original source rescaled by its model dimension k, not ambient dimension. -/
def rescaledSource {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (q : Space n) (a : ℝ) (ha : 0 < a) : Measure (Space n) :=
  (ENNReal.ofReal a)⁻¹ ^ k • μ.map (similarity q a ha)

end ParabolicRectifiability
