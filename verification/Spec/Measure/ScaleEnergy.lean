import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.ModelDistance
import Spec.Measure.Beta
import Spec.Measure.CountableFitting
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Measure.ScaleEnergy` used by the headline statements. -/

noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
namespace ParabolicRectifiability
/-- Lebesgue measure on positive radii with exactly the density `1/r`. -/
def scaleMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun r => ENNReal.ofReal (1 / r))

/-- The extended nonnegative scale integral of `betaSq` against `dr/r`
on `0 < r < R`. The integrand is already squared; no second square or
mass normalization is applied. The result can be infinite, and is zero
when `R ≤ 0`. Its source is exactly the supplied `μ`. -/
def squareEnergy {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (R : ℝ) (z : Space n) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 R, betaSq μ k T z r ∂scaleMeasure

/-- Points in the open unit parabolic ball where the mixed-family energy
of the original source, integrated over `0 < r < 2`, exceeds `ofReal M`.
The main theorem uses `M ≥ 0` and bounds this set in the original measure. -/
def exceptionalSet {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (M : ℝ) : Set (Space n) :=
  Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < squareEnergy μ k .mixed 2 z}

end ParabolicRectifiability
