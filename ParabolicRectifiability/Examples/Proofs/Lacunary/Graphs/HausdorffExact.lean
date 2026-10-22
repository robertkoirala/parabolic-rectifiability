import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support

/-! # Exact Hausdorff measure of the lacunary graph

The snowflaked-time identity transfers to every graph image by the isometry
provided by the graph-distance hypothesis. No measurability of the set is needed.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

/-- Transfer the time Hausdorff identity through the lacunary isometry. -/
theorem e2_lacunary_hausdorffExact_proof :
    E2TimeHausdorffStatement → LacunaryIsometryStatement → E2HausdorffExactStatement := by
  intro htime hisometry ε a N hε hε' hd E
  let G : Time → Space 1 := fun τ => lacunaryGraphMap ε a N τ.val
  have hG : Isometry G :=
    e2_isometry_time_of_dist (hisometry ε a N hε hε' hd)
  have himage : G '' ((Metric.Snowflaking.toSnowflaking : ℝ ≃ Time) '' E) =
      lacunaryGraphMap ε a N '' E := by
    rw [Set.image_image]
    rfl
  rw [hausdorffP_eq, Nat.cast_ofNat, ← himage,
    hG.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 2))]
  exact htime E

end ParabolicRectifiability.Examples
