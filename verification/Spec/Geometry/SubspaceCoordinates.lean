import Spec.Analysis.Coordinates
import Spec.Basic
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Geometry.SubspaceCoordinates` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability
variable {n : ℕ}
/-- Orthonormal coordinates constructed on the intrinsic spatial subspace. -/
def subspaceCoordinates (W : Submodule ℝ (Spatial n)) :
    W ≃ₗᵢ[ℝ] Spatial (Module.finrank ℝ W) :=
  (stdOrthonormalBasis ℝ W).repr

/-- Orthonormal coordinates constructed on the actual normal subspace. -/
def normalCoordinates (W : Submodule ℝ (Spatial n)) :
    W.orthogonal ≃ₗᵢ[ℝ] Spatial (Module.finrank ℝ W.orthogonal) :=
  subspaceCoordinates W.orthogonal

def subspaceCoordinatesHomeomorph (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ₜ Coordinates (Module.finrank ℝ W) :=
  (subspaceCoordinates W).toHomeomorph.prodCongr (Homeomorph.refl ℝ)

def subspaceCoordinatesMeasurableEquiv (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ᵐ Coordinates (Module.finrank ℝ W) :=
  (subspaceCoordinatesHomeomorph W).toMeasurableEquiv

def subspaceToFourierHomeomorph (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ₜ FourierSpace (Module.finrank ℝ W) :=
  (subspaceCoordinatesHomeomorph W).trans (fourierCoordinatesHomeomorph (Module.finrank ℝ W)).symm

def subspaceToFourier (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ᵐ FourierSpace (Module.finrank ℝ W) :=
  (subspaceToFourierHomeomorph W).toMeasurableEquiv

/-- The intrinsic vertical base with the inherited maximum parabolic metric. -/
abbrev SubspaceSpace (W : Submodule ℝ (Spatial n)) := W × Time

def subspaceTimeHomeomorph (W : Submodule ℝ (Spatial n)) : SubspaceSpace W ≃ₜ W × ℝ :=
  (Homeomorph.refl W).prodCongr Metric.Snowflaking.homeomorph

def subspaceTimeMeasurableEquiv (W : Submodule ℝ (Spatial n)) : SubspaceSpace W ≃ᵐ W × ℝ :=
  (subspaceTimeHomeomorph W).toMeasurableEquiv

/-- Intrinsic reference volume: spatial inner-product volume times real time volume,
transported only through the inverse snowflake time coordinate map. -/
def intrinsicParabolicVolume (W : Submodule ℝ (Spatial n)) : Measure (SubspaceSpace W) :=
  Measure.map (subspaceTimeHomeomorph W).symm
    ((volume : Measure W).prod (volume : Measure ℝ))

def subspaceFourierToParabolic (W : Submodule ℝ (Spatial n)) :
    FourierSpace (Module.finrank ℝ W) ≃ᵐ SubspaceSpace W :=
  (subspaceToFourier W).symm.trans (subspaceTimeMeasurableEquiv W).symm

end ParabolicRectifiability
