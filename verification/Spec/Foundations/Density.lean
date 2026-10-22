import Spec.Basic
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.Density` used by the headline statements. -/

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
