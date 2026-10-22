import Spec.Basic
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Analysis.Coordinates` used by the headline statements. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ParabolicRectifiability
/-- Ordinary Euclidean analytic space, with the L² product inner product. -/
abbrev FourierSpace (m : ℕ) := WithLp 2 (Coordinates m)

/-- Ordinary spatial and time coordinates of the Euclidean L² product. -/
def fourierCoordinatesHomeomorph (m : ℕ) : FourierSpace m ≃ₜ Coordinates m :=
  WithLp.homeomorphProd 2 (Spatial m) ℝ

end ParabolicRectifiability
