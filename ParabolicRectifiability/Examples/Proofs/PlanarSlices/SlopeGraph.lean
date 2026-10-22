import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import ParabolicRectifiability.Geometry.Horizontal.Cover

/-! # A planar slope graph in the zero-time slice

Apply the horizontal graph extraction theorem to the time-zero image. Its spatial
slope is the given bound, and its time-flatness coefficient is zero.
-/

namespace ParabolicRectifiability.Examples

open BetaP

/-- Every planar slope set has its time-zero image in one horizontal graph. -/
theorem e2_sb_slopeGraph_proof : E2sbSlopeGraph := by
  intro S V θ hV hθ hslope
  refine exists_horizontalGraph_of_flat_slope (s := θ) (ε₀ := 0)
    V hV (timeSlice '' S) le_rfl (le_refl 0) (by simpa using hθ) ?_ ?_
  · rintro z ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩
    exact hslope x hx y hy
  · rintro z ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩
    simp [timeSlice, point]

end ParabolicRectifiability.Examples
