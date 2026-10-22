import ParabolicRectifiability.Examples.Proofs.Reductions.TimeSliceStatements
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalBeta

/-! # Enlarging an affine spatial plane

For `q ≤ m ≤ n`, every affine spatial `q`-plane of `ℝⁿ` lies in an affine spatial `m`-plane
(`e2_affinePlane_enlarge_proof`). The direction is extended to a subspace of rank `m` with
`b1hbeta_exists_le_finrank_eq`, and the plane is re-anchored with
`AffineSpatialPlane.ofTranslate`. This is used in the time-slice identity
`e2_timeSlice_betaPow_of_enlarge_proof`. -/

noncomputable section

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations Module

/-- Every affine spatial `q`-plane is contained in some affine spatial `m`-plane, `q ≤ m ≤ n`. -/
theorem e2_affinePlane_enlarge_proof : E2AffineEnlargementStatement := by
  intro n q m hqm hmn U
  obtain ⟨V, hUV, hV⟩ := QuantitativeCharacterization.b1hbeta_exists_le_finrank_eq
    (E := Spatial n) (m - q) U.direction
    (by rw [U.rank_eq, finrank_euclideanSpace_fin]; omega)
  have hVm : finrank ℝ V = m := by rw [hV, U.rank_eq]; omega
  refine ⟨AffineSpatialPlane.ofTranslate V hVm U.anchor, ?_⟩
  rw [AffineSpatialPlane.ofTranslate_toSet]
  intro x hx
  exact hUV hx

end ParabolicRectifiability.Examples
