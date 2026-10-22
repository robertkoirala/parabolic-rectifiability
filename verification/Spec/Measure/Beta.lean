import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.ModelDistance
import Spec.Measure.CountableFitting
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Measure.Beta` used by the headline statements. -/

noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
namespace ParabolicRectifiability
/-- Natural squared beta number: for `r > 0`, this is
`r^(-k-2) * inf_L ∫_{ball z r} dist(w,L)^2 dμ(w)`, valued in `ℝ≥0∞`.
There is no division by ball mass and the measure is the supplied source.
For `r ≤ 0` the value is zero. An unavailable family has value infinity at
every positive radius, including for the zero source; the zero-source law
therefore explicitly requires an available family. -/
def betaSq {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  if 0 < r then (ENNReal.ofReal r)⁻¹ ^ (k + 2) * ⨅ L : Models n k T, fit μ L z r else 0

end ParabolicRectifiability
