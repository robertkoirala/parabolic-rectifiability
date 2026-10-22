import ParabolicRectifiability.Examples.Proofs.Reductions.TimeSliceStatements
import ParabolicRectifiability.Examples.Proofs.TimeSlices.AffinePlaneEnlarge
import ParabolicRectifiability.Examples.Proofs.TimeSlices.BetaPow
import ParabolicRectifiability.Examples.Proofs.TimeSlices.Tube

/-! # Statements of the time-slice identity

Each statement is proved by the corresponding module.
-/

namespace ParabolicRectifiability.Examples

/-- **Affine enlargement.** Route: apply
`QuantitativeCharacterization.b1hbeta_exists_le_finrank_eq` with
`p := U.direction`, `d := m - q`; its hypothesis `q + (m - q) ≤ n` follows from `U.rank_eq`
and `finrank_euclideanSpace_fin`. It gives `V ≥ U.direction` with `finrank V = q + (m - q) = m`.
Then `U' = AffineSpatialPlane.ofTranslate V hV U.anchor` and
`ofTranslate_toSet` give `{x | x - U.anchor ∈ V} ⊇ {x | x - U.anchor ∈ U.direction} =
U.toSet`, despite the canonical re-anchoring. -/
theorem e2_affinePlane_enlarge : E2AffineEnlargementStatement := by
  exact e2_affinePlane_enlarge_proof

/-- **The shared slice identity**, in implication form over the affine enlargement.
Route, pointwise before any power or infimum (valid for all `p > 0`, `ENNReal.rpow_le_rpow` only):
* change of variables `setLIntegral_map` (no finiteness of `ν`; `measurable_point`,
  `measurable_infEDist`, `Measurable.pow_const`), with `ι⁻¹(P(ιx,r)) = B(x,r)` (`dist_point`);
* horizontal candidate `U × {τ}`: `infEDist(ιy, ·) = max(infEDist(y,U), √|t₀-τ|) ≥ infEDist(y,U)`,
  equality at `τ = t₀` (`HorizontalModel.infEDist_eq_projection`, `dist_projection_sq`): the horizontal infimum equals the Euclidean one, with no
  interchange of infimum and integral;
* mixed family, vertical candidate `V × ℝ` (rank `k - 2 ≤ n`): by the affine enlargement enlarge `V` to a
  `k`-plane `U ⊇ V`; then `infEDist(y,U) ≤ infEDist(y,V) = infEDist(ιy, V × ℝ)`
  (`VerticalModel.dist_projection_sq`), so vertical candidates never go below the
  horizontal infimum (`iInf_sum` over `HorizontalModel ⊕ VerticalModel`); at `k = 1` there are no
  vertical models (`VerticalModel.one_isEmpty`);
* the normalizations `(ofReal r)⁻¹ ^ (k + p)` agree, and both sides are `0` for `r ≤ 0`. -/
theorem e2_timeSlice_betaPow_of_enlarge :
    E2AffineEnlargementStatement → E2TimeSliceBetaPowStatement := by
  exact e2_timeSlice_betaPow_of_enlarge_proof

/-- **Tube identity** `TimeSliceTubeStatement`. Route: for every
spatial `A` (including `∅`) and `r > 0`, the coordinate preimage of
`{z : infEDist(z, A × {t₀}) < r}` is `A_r × (t₀ - r², t₀ + r²)` with
`A_r = {y : infEDist(y,A) < r}` (`Metric.infEDist_prod`, `Metric.infEDist_singleton`, or
`Metric.infEDist_lt_iff`); then `parabolicVolume_apply`,
`Measure.prod_prod`, `Real.volume_Ioo`. No measurability or finiteness of `A` is assumed
(product of an arbitrary set with an interval: use `Measure.prod_prod` for arbitrary sets). -/
theorem e2_timeSlice_tube : TimeSliceTubeStatement := by
  exact e2_timeSlice_tube_proof

end ParabolicRectifiability.Examples
