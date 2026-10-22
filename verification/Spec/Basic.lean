import Mathlib

/-! Specification: the definitions of `ParabolicRectifiability.Basic` used by the headline statements. -/

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

end ParabolicRectifiability
