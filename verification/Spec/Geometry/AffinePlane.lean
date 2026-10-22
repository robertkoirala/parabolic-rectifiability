import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Spec.Basic

/-! Specification: the definitions of `ParabolicRectifiability.Geometry.AffinePlane` used by the headline statements. -/

noncomputable section
namespace ParabolicRectifiability
open Module
/-- An affine spatial plane, anchored at its point closest to the origin. -/
structure AffineSpatialPlane (n m : ℕ) where
  direction : Submodule ℝ (Spatial n)
  rank_eq : finrank ℝ direction = m
  anchor : Spatial n
  anchor_orthogonal : anchor ∈ directionᗮ

namespace AffineSpatialPlane
variable {n m : ℕ}
/-- The represented affine set. -/
def toSet (L : AffineSpatialPlane n m) : Set (Spatial n) :=
  {x | x - L.anchor ∈ L.direction}

end AffineSpatialPlane
end ParabolicRectifiability
