import ParabolicRectifiability.Metric.Space

/-! # The dense-atom measure

Given points `z_j` and an exponent `k`, the dense-atom weights and measure are
```
w_1 = 1/2,   w_j = 2^{-j} / (1 + Σ_{i<j} w_i d_P(z_i,z_j)^{-k})  (j ≥ 2),
μ = Σ_{j≥1} w_j δ_{z_j}.
```

**Indexing.** The points and weights are sequences on `ℕ`; the Lean index `j` is the
mathematical index `j + 1`. The recursion is written uniformly as
`w j = 2^{-(j+1)} / (1 + Σ_{i<j} w i · d_P(z i, z j)^{-k})` for every `j`. At `j = 0` the
sum is empty and the formula gives exactly `w 0 = 2^{-1}/1 = 1/2`, the weight `w_1` above;
for `j ≥ 1` it is the recursion above with index `j + 1`.

The definitions are total: no hypothesis on `z` is needed to form them. The statements
assume `z` injective, with values in `D = closedBall (point 0 0) (1/4)` and dense there. For
distinct points every distance is positive, so `d_P^{-k}` is an honest real number.
-/

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
