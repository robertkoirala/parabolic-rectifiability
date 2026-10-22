import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Scalar snowflake extension to a full ordinary vertical graph

The given half-Hölder estimate is exactly a Lipschitz estimate on `Time`.
The scalar McShane extension preserves its constant on every subset, including
the empty set. Lifting the extension into the normal space of the zero spatial
direction gives a full graph: the normal distance is the scalar distance, while
projection onto time is nonexpanding for the maximum product metric.
-/

noncomputable section

open Set
open scoped NNReal

namespace ParabolicRectifiability.Examples

open Foundations

/-- Every scalar half-Hölder graph over an arbitrary set lies in a full ordinary
vertical graph with the same slope bound. -/
theorem e2_snowflake_extension_proof : E2SnowflakeExtensionStatement := by
  intro η hη A g hg
  let K : ℝ≥0 := ⟨η, hη.le⟩
  have htime (t s : Time) : dist t s = Real.sqrt |t.val - s.val| := by
    rcases t with ⟨t⟩
    rcases s with ⟨s⟩
    change dist (Metric.Snowflaking.toSnowflaking t : Time)
      (Metric.Snowflaking.toSnowflaking s) = Real.sqrt |t - s|
    rw [Metric.Snowflaking.dist_toSnowflaking_toSnowflaking, Real.dist_eq,
      Real.sqrt_eq_rpow]
  have hgTime : LipschitzOnWith K (fun t : Time => g t.val) {t | t.val ∈ A} := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    change dist (g t.val) (g s.val) ≤ η * dist t s
    rw [Real.dist_eq, htime]
    exact hg t.val ht s.val hs
  obtain ⟨f, hf, hfg⟩ := hgTime.extend_real
  let G : OrdinaryVerticalGraph 1 2 η :=
    { vertical_dimension := le_rfl
      direction := zeroDirection
      rank_eq := by simp [zeroDirection]
      offset := 0
      function := zeroBaseLift (fun t => f (Metric.Snowflaking.toSnowflaking t))
      lipschitz := by
        refine ⟨K, LipschitzWith.of_dist_le_mul ?_, le_rfl⟩
        intro p q
        change dist (EuclideanSpace.single (0 : Fin 1) (f p.2))
          (EuclideanSpace.single (0 : Fin 1) (f q.2)) ≤ η * dist p q
        rw [PiLp.dist_single_same]
        exact (hf.dist_le_mul p.2 q.2).trans
          (mul_le_mul_of_nonneg_left (by rw [Prod.dist_eq]; exact le_max_right _ _) hη.le) }
  refine ⟨G, ?_⟩
  rintro z ⟨t, ht, rfl⟩
  refine ⟨(0, Metric.Snowflaking.toSnowflaking t), ?_⟩
  apply Prod.ext
  · change (0 : Spatial 1) + 0 + EuclideanSpace.single 0
        (f (Metric.Snowflaking.toSnowflaking t)) = EuclideanSpace.single 0 (g t)
    simp only [zero_add]
    exact congrArg (EuclideanSpace.single (0 : Fin 1))
      (hfg (show (Metric.Snowflaking.toSnowflaking t : Time).val ∈ A from ht)).symm
  · rfl

end ParabolicRectifiability.Examples
