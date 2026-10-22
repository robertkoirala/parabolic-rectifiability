import Mathlib

/-!
# Parabolic metric foundations

Spatial distance is Euclidean and time has the square-root metric, so
`dist (point x t) (point y s) = max ‖x-y‖ (sqrt |t-s|)`. A radius-`r`
ball has spatial radius `r` and time half-length `r²`. Dilations send
`(x,t)` to `(r*x,r²*t)` and multiply distance by `r` for `r ≥ 0`.

The `Metric` area supplies ordinary coordinates, the Borel structure and
coordinate volume, whose dilation exponent is
`n + 2` although the ordinary coordinate dimension is `n + 1`. Fourier and
differential analysis use the ordinary coordinates, not a normed structure on
snowflaked time. All metric formulas here also include `n = 0`.
-/

noncomputable section

namespace ParabolicRectifiability

/-- Euclidean `n`-space with its `ℓ²` norm, including the one-point space at `n = 0`. -/
abbrev Spatial (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Time with the square-root metric, as a distinct type. -/
abbrev Time := Metric.Snowflaking ℝ (1 / 2) (by norm_num) (by norm_num)

/-- The product metric is the maximum of the spatial and snowflaked time metrics. -/
abbrev Space (n : ℕ) := Spatial n × Time

/-- Insert ordinary spatial and time coordinates into the parabolic metric space. -/
def point {n : ℕ} (x : Spatial n) (t : ℝ) : Space n :=
  (x, Metric.Snowflaking.toSnowflaking t)

theorem dist_point {n : ℕ} (x y : Spatial n) (t s : ℝ) :
    dist (point x t) (point y s) = max ‖x - y‖ (Real.sqrt |t - s|) := by
  simp only [point, Prod.dist_eq, Metric.Snowflaking.dist_toSnowflaking_toSnowflaking,
    dist_eq_norm, Real.norm_eq_abs, Real.sqrt_eq_rpow]

theorem mem_ball_point {n : ℕ} (x y : Spatial n) (t s r : ℝ) (hr : 0 < r) :
    point y s ∈ Metric.ball (point x t) r ↔
      ‖y - x‖ < r ∧ |s - t| < r ^ 2 := by
  rw [Metric.mem_ball, dist_point, max_lt_iff,
    Real.sqrt_lt (abs_nonneg _) hr.le]

theorem mem_closedBall_point {n : ℕ} (x y : Spatial n) (t s r : ℝ)
    (hr : 0 ≤ r) :
    point y s ∈ Metric.closedBall (point x t) r ↔
      ‖y - x‖ ≤ r ∧ |s - t| ≤ r ^ 2 := by
  rw [Metric.mem_closedBall, dist_point, max_le_iff, Real.sqrt_le_left hr]

/-- Parabolic dilation `(x,t) ↦ (r*x,r²*t)`. The formula is total in `r`;
positive radii give the geometric similarities, and `r = 0` collapses to the origin. -/
def dilate {n : ℕ} (r : ℝ) (z : Space n) : Space n :=
  point (r • z.1) (r ^ 2 * z.2.val)

theorem dist_dilate {n : ℕ} (r : ℝ) (hr : 0 ≤ r) (z w : Space n) :
    dist (dilate r z) (dilate r w) = r * dist z w := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases w with ⟨y, ⟨s⟩⟩
  change dist (point (r • x) (r ^ 2 * t)) (point (r • y) (r ^ 2 * s)) =
    r * dist (point x t) (point y s)
  rw [dist_point, dist_point, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r),
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
  exact (mul_max_of_nonneg _ _ hr).symm

end ParabolicRectifiability
