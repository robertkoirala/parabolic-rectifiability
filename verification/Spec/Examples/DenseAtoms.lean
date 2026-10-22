import Spec.Basic
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Examples.DenseAtoms` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Examples
/-- The dense-atom weights `w`, in the Lean index:
`w j = 2^{-(j+1)} / (1 + Σ_{i<j} w i · (d_P(z i, z j)^k)⁻¹)`. -/
def denseAtomWeight {n : ℕ} (k : ℕ) (z : ℕ → Space n) (j : ℕ) : ℝ :=
  ((2 : ℝ) ^ (j + 1))⁻¹ /
    (1 + ∑ i : Fin j, denseAtomWeight k z i * (dist (z i) (z j) ^ k)⁻¹)
termination_by j
decreasing_by exact i.isLt

/-- The dense-atom measure `μ = Σ_j w_j δ_{z_j}`. -/
def denseAtomMeasure {n : ℕ} (k : ℕ) (z : ℕ → Space n) : Measure (Space n) :=
  Measure.sum fun j => ENNReal.ofReal (denseAtomWeight k z j) • Measure.dirac (z j)

end ParabolicRectifiability.Examples
