import Spec.Analysis.Coordinates
import Spec.Basic
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Metric.Measure` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability
/-- Product of ordinary Euclidean spatial volume and one-dimensional
Lebesgue time measure; the coordinate dimension is `n + 1`. -/
def coordinateVolume (n : ℕ) : Measure (Coordinates n) :=
  (volume : Measure (Spatial n)).prod (volume : Measure ℝ)

/-- Coordinate Lebesgue volume transported to `Space n`. For `r > 0`,
a parabolic ball has measure `2 * omega n * r^(n+2)`. This volume is distinct
from the unnormalized Hausdorff measures `hausdorffP n k`. -/
def parabolicVolume (n : ℕ) : Measure (Space n) :=
  Measure.map (coordinatesHomeomorph n).symm (coordinateVolume n)

def fourierToParabolic (n : ℕ) : FourierSpace n ≃ₜ Space n :=
  (fourierCoordinatesHomeomorph n).trans (coordinatesHomeomorph n).symm

def coordinateDilationHomeomorph (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Coordinates n ≃ₜ Coordinates n :=
  (Homeomorph.smulOfNeZero a ha.ne' : Spatial n ≃ₜ Spatial n).prodCongr
    (Homeomorph.smulOfNeZero (a ^ 2) (pow_ne_zero _ ha.ne') : ℝ ≃ₜ ℝ)

/-- The invertible version of the existing parabolic dilation. -/
def dilationHomeomorph (n : ℕ) (a : ℝ) (ha : 0 < a) : Space n ≃ₜ Space n :=
  ((coordinatesHomeomorph n).trans (coordinateDilationHomeomorph n a ha)).trans
    (coordinatesHomeomorph n).symm

end ParabolicRectifiability
