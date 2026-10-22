import ParabolicRectifiability.Examples.Statements.DensityExamples

/-! # Named statements of the dense-atoms example

Definitions and proposition definitions only. The statements are assembled, with explicit
ambient-nullity and atom-density inputs, in `e2_dense_atoms_of`.

Target: `Examples.dense_atoms_bundle : DenseAtomsStatement` and the endpoint
`Examples.dense_atoms_density_support`.

Notation: `w = denseAtomWeight k z`, `μ = denseAtomMeasure k z = Σ_j w_j δ_{z_j}`,
`d_{ij} = d_P(z_i, z_j)`, `D = \overline{P(0,1/4)}` (`Metric.closedBall (point 0 0) (1/4)`).
Lean indices are the indices of the informal construction minus one;
`d^{-k}` is `(d ^ k)⁻¹`, which is `0` at `d = 0` in Lean when `k ≥ 1` (the energy range); at
`k = 0` it is `1`, and the weight and measure statements use only its nonnegativity.

Statements:
* weights `E2DenseWeightStatement`: positivity, `w_j ≤ 2^{-(j+1)}`, and the recursion bound
  `w_j Σ_{i<j} w_i d_{ij}^{-k} ≤ 2^{-(j+1)}`;
* measure `E2DenseMeasureStatement`: finite, inner regular, nonzero, `Σ w ≤ 1`, finite pair sum;
* atomic square bound `E2AtomicSquareBoundStatement`: `S²_{2,μ}(x) ≤ (k+2)^{-1} Σ_j w_j d(x,z_j)^{-k}`
  at every centre, for every countable atomic source;
* integrated energy `E2DenseEnergyStatement`: the integrated energy is finite;
* densities `E2DenseDensityStatement`: infinite densities at the atoms, and `Θ^{k,*} ≥ a` a.e.;
* support `E2DenseSupportStatement`: `supp μ = D`;
* volume `E2DenseVolumeStatement`: `D` has positive ambient volume;
* `E2DenseNotRectifiableStatement`: `D` is not regularly rectifiable.
`H_P^k(D) = ∞` follows from the ambient nullity of graphs and the volume statement.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **Weights.** For every `n`, `k` and every point sequence `z`: every weight is
positive, `w_j ≤ 2^{-(j+1)}`, and `Σ_{i<j} w_i w_j d_{ij}^{-k} ≤ 2^{-(j+1)}` (the weights are
defined by `w_j (1 + Σ_{i<j} w_i d_{ij}^{-k}) = 2^{-(j+1)}`). -/
def E2DenseWeightStatement : Prop :=
  ∀ (n k : ℕ) (z : ℕ → Space n),
    (∀ j, 0 < denseAtomWeight k z j) ∧ (∀ j, denseAtomWeight k z j ≤ ((2 : ℝ) ^ (j + 1))⁻¹) ∧
    ∀ j, ∑ i ∈ Finset.range j,
        denseAtomWeight k z i * denseAtomWeight k z j * (dist (z i) (z j) ^ k)⁻¹ ≤
      ((2 : ℝ) ^ (j + 1))⁻¹

/-- **The measure.** `μ` is finite, inner regular and nonzero,
`Σ_j w_j ≤ 1`, and the pair sum `Σ_{i<j} w_i w_j d_{ij}^{-k}` is finite. No hypothesis on `z`. -/
def E2DenseMeasureStatement : Prop :=
  ∀ (n k : ℕ) (z : ℕ → Space n),
    IsFiniteMeasure (denseAtomMeasure k z) ∧ (denseAtomMeasure k z).InnerRegular ∧
    denseAtomMeasure k z ≠ 0 ∧ ∑' j, ENNReal.ofReal (denseAtomWeight k z j) ≤ 1 ∧
    ∑' j, ∑ i ∈ Finset.range j,
        ENNReal.ofReal (denseAtomWeight k z i * denseAtomWeight k z j *
          (dist (z i) (z j) ^ k)⁻¹) < ⊤

/-- **Atomic square bound.** For `n ≥ 1`, `1 ≤ k < n + 2`, every point sequence
`z`, nonnegative weights `w` and every centre `x`, the mixed square energy at endpoint `2` of
`Σ_j w_j δ_{z_j}` satisfies `S²(x) ≤ (k+2)^{-1} Σ_j w_j d(x,z_j)^{-k}` (test a fixed admissible model through `x`; Tonelli; `d² ∫_d^2 r^{-k-3} dr ≤ d^{-k}/(k+2)`). An atom
at `x` itself contributes `0` on both sides. -/
def E2AtomicSquareBoundStatement : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k < n + 2 → ∀ (z : ℕ → Space n) (w : ℕ → ℝ), (∀ j, 0 ≤ w j) →
    ∀ x : Space n,
      squareEnergy (Measure.sum fun j => ENNReal.ofReal (w j) • Measure.dirac (z j)) k .mixed 2 x ≤
        ENNReal.ofReal (1 / ((k : ℝ) + 2)) * ∑' j, ENNReal.ofReal (w j * (dist x (z j) ^ k)⁻¹)

/-- **Integrated energy.** For `n ≥ 1`, `1 ≤ k < n + 2` and every `z`:
`∫_{P(0,1)} S²_{2,μ} dμ < ∞` (with `𝓔 ≤ (2/(k+2)) Σ_{i<j} w_i w_j d_{ij}^{-k}`). -/
def E2DenseEnergyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ z : ℕ → Space n,
    ∫⁻ x in Metric.ball (point 0 0) 1, squareEnergy (denseAtomMeasure k z) k .mixed 2 x
        ∂(denseAtomMeasure k z) < ⊤

/-- **Densities.** For `k ≥ 1` and every `z`: both `k`-densities of `μ` are
infinite at every atom, and `Θ^{k,*}(μ, ·) ≥ a` holds `μ`-almost everywhere for every finite `a > 0`. -/
def E2DenseDensityStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → ∀ z : ℕ → Space n,
    (∀ j, lowerDensity (denseAtomMeasure k z) k (z j) = ⊤ ∧
        upperDensity (denseAtomMeasure k z) k (z j) = ⊤) ∧
    ∀ a : ℝ, 0 < a →
      ∀ᵐ x ∂(denseAtomMeasure k z), ENNReal.ofReal a ≤ upperDensity (denseAtomMeasure k z) k x

/-- **Support.** If the atoms lie in `D` and are dense there, `supp μ = D`
(every dense atom has positive mass). -/
def E2DenseSupportStatement : Prop :=
  ∀ (n k : ℕ) (z : ℕ → Space n), (∀ i, z i ∈ Metric.closedBall (point 0 0) (1 / 4)) →
    Metric.closedBall (point 0 0) (1 / 4) ⊆ closure (range z) →
      (denseAtomMeasure k z).support = Metric.closedBall (point 0 0) (1 / 4)

/-- **Positive volume.** The closed cylinder `D = \overline{P(0,1/4)}` has positive
ambient parabolic volume. -/
def E2DenseVolumeStatement : Prop :=
  ∀ n : ℕ, 0 < parabolicVolume n (Metric.closedBall (point (0 : Spatial n) 0) (1 / 4))

/-- **Not regularly rectifiable.** For `n ≥ 1`, `1 ≤ k < n + 2`, the set `D` is not
regularly rectifiable (mixed family) (every allowed graph is σ-finite for
`H_P^k`, hence ambient null, and so is a Hausdorff-null residual). -/
def E2DenseNotRectifiableStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
    ¬ IsRegularlyRectifiableSet .mixed k (Metric.closedBall (point (0 : Spatial n) 0) (1 / 4))

end ParabolicRectifiability.Examples
