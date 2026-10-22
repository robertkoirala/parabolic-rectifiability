import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Regular
import Spec.Basic
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Metric.Hausdorff` used by the headline statements. -/

noncomputable section
namespace ParabolicRectifiability
open MeasureTheory Set
open scoped ENNReal NNReal
/-- Unnormalized `k`-dimensional Hausdorff measure for the parabolic metric. -/
def hausdorffP (n k : ℕ) : Measure (Space n) :=
  Measure.hausdorffMeasure (k : ℝ)

section MetricSpaces
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
end MetricSpaces
section CompactRestriction
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
end CompactRestriction
end ParabolicRectifiability
