import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-!
# Zero-base Lipschitz adapter

The square-root modulus in time is exactly the metric modulus on the zero spatial base.
The spatial factor of the base is a singleton, while the normal coordinate is an isometric
copy of `ℝ` through `EuclideanSpace.single`.
-/

noncomputable section

namespace ParabolicRectifiability.Examples

open scoped NNReal

/-- A square-root modulus on `ℝ` gives the same Lipschitz bound on the parabolic zero base. -/
theorem e2_zeroBase_lipschitz_proof : E2ZeroBaseLipschitzStatement := by
  intro g C hmod
  have hC : 0 ≤ C := by
    have h01 := hmod 0 1
    norm_num at h01
    exact (abs_nonneg _).trans h01
  let L : ℝ≥0 := C.toNNReal
  have hL : (L : ℝ) = C := by
    dsimp [L]
    exact Real.coe_toNNReal C hC
  refine ⟨L, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun p q => ?_
    have hspace : p.1 = q.1 := Subsingleton.elim _ _
    have htime : dist p.2 q.2 = Real.sqrt |p.2.val - q.2.val| := by
      change dist (Metric.Snowflaking.toSnowflaking p.2.val)
        (Metric.Snowflaking.toSnowflaking q.2.val) = _
      simp only [Metric.Snowflaking.dist_toSnowflaking_toSnowflaking, dist_eq_norm,
        Real.norm_eq_abs, Real.sqrt_eq_rpow]
    have hbase : Real.sqrt |p.2.val - q.2.val| ≤ dist p q := by
      rw [Prod.dist_eq, hspace, dist_self, ← htime]
      exact le_max_right _ _
    have hnormal : dist (zeroBaseLift g p) (zeroBaseLift g q) =
        |g p.2.val - g q.2.val| := by
      change dist (EuclideanSpace.single (0 : Fin 1) (g p.2.val))
        (EuclideanSpace.single (0 : Fin 1) (g q.2.val)) = _
      rw [EuclideanSpace.single, PiLp.dist_single_same]
      simp only [dist_eq_norm, Real.norm_eq_abs]
    calc
      dist (zeroBaseLift g p) (zeroBaseLift g q) =
          |g p.2.val - g q.2.val| := hnormal
      _ ≤ C * Real.sqrt |p.2.val - q.2.val| := hmod _ _
      _ ≤ C * dist p q := mul_le_mul_of_nonneg_left hbase hC
      _ = (L : ℝ) * dist p q := by rw [← hL]
  · exact hL.le

end ParabolicRectifiability.Examples
