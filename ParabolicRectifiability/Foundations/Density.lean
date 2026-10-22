import ParabolicRectifiability.Metric.Space

/-! # Lower and upper parabolic densities

```
Θ_*^k(μ,z) = liminf_{r↓0} r^{-k} μ(P(z,r)),   Θ^{k,*}(μ,z) = limsup_{r↓0} r^{-k} μ(P(z,r)).
```
The ball `P(z,r)` is the open parabolic ball `Metric.ball z r`, and `r ↓ 0` is the
filter `𝓝[>] 0` of positive radii tending to zero. The ratio is formed in `ℝ≥0∞`
with `ENNReal.ofReal r ^ k`; at positive radii this is a finite nonzero number, so the
division is an honest division. The densities keep extended values: an atom has
infinite density in every positive dimension, and this is not truncated.

No regularity of `μ` enters the definitions; locally Radon hypotheses appear only in
the statements that use them.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The ball-mass ratio `r^{-k} μ(P(z,r)) = μ(P(z,r)) / r^k`, in `ℝ≥0∞`.
Only its values at positive radii enter the densities below. -/
def densityRatio {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.ball z r) / ENNReal.ofReal r ^ k

/-- Lower `k`-density `Θ_*^k(μ,z) = liminf_{r↓0} r^{-k} μ(P(z,r))`. Extended valued. -/
def lowerDensity {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n) : ℝ≥0∞ :=
  liminf (densityRatio μ k z) (𝓝[>] (0 : ℝ))

/-- Upper `k`-density `Θ^{k,*}(μ,z) = limsup_{r↓0} r^{-k} μ(P(z,r))`. Extended valued. -/
def upperDensity {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n) : ℝ≥0∞ :=
  limsup (densityRatio μ k z) (𝓝[>] (0 : ℝ))

end ParabolicRectifiability.Foundations
