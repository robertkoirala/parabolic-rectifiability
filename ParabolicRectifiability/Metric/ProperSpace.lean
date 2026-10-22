import ParabolicRectifiability.Metric.Space

/-!
# Properness and a concrete compact exhaustion

For nonnegative radii, snowflaked time closed balls correspond to ordinary
compact intervals with radius `r²`. We prove their compactness through the
snowflake homeomorphism; the library properness reduction handles the remaining
radii. Spatial and product properness are then inherited from mathlib, as is
sigma compactness. The concrete exhaustion below uses only generic metric
ball lemmas and the library `CompactExhaustion` interface.
-/

noncomputable section

namespace ParabolicRectifiability

/-- A snowflaked time closed ball has an ordinary closed interval as its image. -/
theorem image_time_closedBall (t : Time) (r : ℝ) (hr : 0 ≤ r) :
    (Metric.Snowflaking.homeomorph : Time ≃ₜ ℝ) '' Metric.closedBall t r =
      Set.Icc (t.val - r ^ 2) (t.val + r ^ 2) := by
  change Metric.Snowflaking.ofSnowflaking '' Metric.closedBall t r = _
  rw [Metric.Snowflaking.image_ofSnowflaking_closedBall t hr, Real.closedBall_eq_Icc]
  norm_num [Real.rpow_two]
  rfl

instance instProperSpaceTime : ProperSpace Time :=
  ProperSpace.of_isCompact_closedBall_of_le 0 fun t r hr => by
    apply (Metric.Snowflaking.homeomorph : Time ≃ₜ ℝ).isCompact_image.mp
    rw [image_time_closedBall t r hr]
    exact isCompact_Icc

/-- Increasing compact closed balls about the origin, with radii `j + 1`.

Compactness, monotonicity, containment in the interior of the next set, and
coverage of the whole space are available from the `CompactExhaustion` API.
-/
def compactExhaustion (n : ℕ) : CompactExhaustion (Space n) where
  toFun j := Metric.closedBall (point (0 : Spatial n) 0) ((j : ℝ) + 1)
  isCompact' j := isCompact_closedBall _ _
  subset_interior_succ' j := by
    apply (Metric.closedBall_subset_ball ?_).trans Metric.ball_subset_interior_closedBall
    push_cast
    linarith
  iUnion_eq' := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← Metric.iUnion_closedBall_nat (point (0 : Spatial n) 0)]
    exact Set.iUnion_mono fun j => Metric.closedBall_subset_closedBall (by linarith)

@[simp]
theorem compactExhaustion_apply (n j : ℕ) :
    compactExhaustion n j = Metric.closedBall (point (0 : Spatial n) 0) ((j : ℝ) + 1) :=
  rfl

end ParabolicRectifiability
