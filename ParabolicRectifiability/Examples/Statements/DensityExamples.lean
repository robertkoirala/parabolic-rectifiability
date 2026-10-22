import ParabolicRectifiability.Examples.DenseAtoms
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Measure.ScaleEnergy
import ParabolicRectifiability.Metric.Measure
import Mathlib.MeasureTheory.Measure.Support

/-! # Statements: the density and mass test examples

The dense-atom example (`DenseAtomsStatement`) and the flat, diffuse and atomic density
tests (`DensityTestsStatement`). These propositions are proved by
`dense_atoms_density_support` and `density_tests`.

Conventions.
* `n ≥ 1`. The dimension range is the one stated by each example: `1 ≤ k < n + 2` for the
  dense atoms and the diffuse source, `1 ≤ k ≤ n + 2` for the flat patch and the atom.
* `P(0,ρ)` is `Metric.ball (point 0 0) ρ`; its closure `\overline{P(0,1/4)}` is
  `Metric.closedBall (point 0 0) (1/4)`. `L^{n+1}` is `parabolicVolume n`, `H_P^k` is
  `hausdorffP n k`, densities are `Foundations.lowerDensity`/`upperDensity`, and the support
  is mathlib's `Measure.support` (as in `RetainedSets`).
* "Square" and "energy" are the mixed-family `squareEnergy μ k .mixed` (the default `A_k`),
  with endpoint `2` for `S²`. The integrated energy is that of the density theorem,
  `E = ∫_{P(0,1)} S²_{μ} dμ`.
* "Carried by" and "null" use the measure on arbitrary sets (outer measure).
* Constants left implicit in the informal statements ("`O(c)`", "a positive constant times `c²`") are
  existential, chosen after `n`, `k` and before the amplitude `c`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Densities and supports: the dense atoms -/

/-- **Dense atoms.** For `n ≥ 1`, `1 ≤ k < n + 2` and distinct points `z_i` dense in
`D = \overline{P(0,1/4)}` (values in `D`, `D ⊆ closure {z_i}`), the measure
`μ = Σ_j w_j δ_{z_j}` of `denseAtomMeasure` is a finite nonzero Radon source with
* `Σ_j w_j ≤ 1`;
* `Σ_{i<j} w_i w_j d_P(z_i,z_j)^{-k} < ∞`;
* `∫_{P(0,1)} S²_{2,μ} dμ < ∞`;
* infinite upper and lower `k`-densities at every atom;
* `Θ^{k,*}(μ,·) ≥ a` `μ`-almost everywhere, for every finite `a > 0`;
* `supp μ = D`, `H_P^k(D) = ∞`, and `D` is not regularly rectifiable as a set (mixed
  family). -/
def DenseAtomsStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
  ∀ z : ℕ → Space n, Function.Injective z →
    (∀ i, z i ∈ Metric.closedBall (point 0 0) (1 / 4)) →
    Metric.closedBall (point 0 0) (1 / 4) ⊆ closure (range z) →
      IsFiniteMeasure (denseAtomMeasure k z) ∧ (denseAtomMeasure k z).InnerRegular ∧
      denseAtomMeasure k z ≠ 0 ∧
      ∑' j, ENNReal.ofReal (denseAtomWeight k z j) ≤ 1 ∧
      ∑' j, ∑ i ∈ Finset.range j,
          ENNReal.ofReal (denseAtomWeight k z i * denseAtomWeight k z j *
            (dist (z i) (z j) ^ k)⁻¹) < ⊤ ∧
      ∫⁻ x in Metric.ball (point 0 0) 1, squareEnergy (denseAtomMeasure k z) k .mixed 2 x
          ∂(denseAtomMeasure k z) < ⊤ ∧
      (∀ j, lowerDensity (denseAtomMeasure k z) k (z j) = ⊤ ∧
        upperDensity (denseAtomMeasure k z) k (z j) = ⊤) ∧
      (∀ a : ℝ, 0 < a →
        ∀ᵐ x ∂(denseAtomMeasure k z), ENNReal.ofReal a ≤ upperDensity (denseAtomMeasure k z) k x) ∧
      (denseAtomMeasure k z).support = Metric.closedBall (point 0 0) (1 / 4) ∧
      hausdorffP n k (Metric.closedBall (point 0 0) (1 / 4)) = ⊤ ∧
      ¬ IsRegularlyRectifiableSet .mixed k (Metric.closedBall (point (0 : Spatial n) 0) (1 / 4))

/-! ## Density tests -/

/-- Density tests, flat patch. For `1 ≤ k ≤ n + 2`, a model `L` of the mixed family (an
available flat `k`-plane), a bounded set `D ⊆ L` with `H_P^k(D) > 0`, and `c > 0`, the source
`μ = c H_P^k⌊D` has zero square (`S^R_μ(z) = 0` for every endpoint `R` and centre `z`) and
positive carrier measure (every set carrying `μ` has positive `H_P^k` measure). -/
def FlatPatchTestStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ (L : Models n k .mixed) (D : Set (Space n)), D ⊆ modelSet L → Bornology.IsBounded D →
    0 < hausdorffP n k D →
  ∀ c : ℝ, 0 < c →
    (∀ (R : ℝ) (z : Space n),
      squareEnergy (ENNReal.ofReal c • (hausdorffP n k).restrict D) k .mixed R z = 0) ∧
    (∀ X : Set (Space n), (ENNReal.ofReal c • (hausdorffP n k).restrict D) Xᶜ = 0 →
      0 < hausdorffP n k X)

/-- Density tests, diffuse source. For `1 ≤ k < n + 2` there are constants `C, κ > 0` (depending only on
`n`, `k`) such that for every `c > 0` the source `μ_c = c L^{n+1}⌊P(0,1/4)` satisfies:
* zero `k`-density almost everywhere (`Θ_*^k = Θ^{k,*} = 0`, `μ_c`-a.e.);
* finite positive integrated energy `0 < ∫_{P(0,1)} S²_{μ_c} dμ_c < ∞`;
* `μ_c(N) = 0` for every `H_P^k`-null `N` (`μ_c ≪ H_P^k`);
* every `σ`-finite `H_P^k` set is `μ_c`-null;
* pointwise square `O(c)`: `S²_{μ_c}(z) ≤ C c` at every `z`;
* integrated square equal to a positive constant times `c²`: `∫_{P(0,1)} S²_{μ_c} dμ_c = κ c²`;
* every finite-Hausdorff good measure is zero: a measure `ν ≤ μ_c` carried by a set `K` with
  `H_P^k(K) < ∞` is zero. -/
def DiffuseTestStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
  ∀ c : ℝ, 0 < c →
    let μ : Measure (Space n) :=
      ENNReal.ofReal c • (parabolicVolume n).restrict (Metric.ball (point 0 0) (1 / 4))
    (∀ᵐ z ∂μ, lowerDensity μ k z = 0 ∧ upperDensity μ k z = 0) ∧
    0 < ∫⁻ z in Metric.ball (point 0 0) 1, squareEnergy μ k .mixed 2 z ∂μ ∧
    ∫⁻ z in Metric.ball (point 0 0) 1, squareEnergy μ k .mixed 2 z ∂μ < ⊤ ∧
    μ ≪ hausdorffP n k ∧
    (∀ A : ℕ → Set (Space n), (∀ i, hausdorffP n k (A i) < ⊤) → μ (⋃ i, A i) = 0) ∧
    (∀ z : Space n, squareEnergy μ k .mixed 2 z ≤ ENNReal.ofReal (C * c)) ∧
    ∫⁻ z in Metric.ball (point 0 0) 1, squareEnergy μ k .mixed 2 z ∂μ =
      ENNReal.ofReal (κ * c ^ 2) ∧
    (∀ ν : Measure (Space n), ν ≤ μ → ∀ K : Set (Space n), hausdorffP n k K < ⊤ →
      ν Kᶜ = 0 → ν = 0)

/-- Density tests, atom. For `1 ≤ k ≤ n + 2`, a point `z` and a
mass `A > 0` (arbitrary), the atom `μ = A δ_z` has zero square at every centre and endpoint,
mass `A`, the Hausdorff-null carrier `{z}`, infinite lower and upper `k`-density at `z`, and is
not absolutely continuous with respect to `H_P^k`; the carrier `{z}` is regularly rectifiable
as a set while `μ` is not regularly rectifiable as a measure (mixed family). -/
def AtomTestStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ (z : Space n) (A : ℝ), 0 < A →
    (∀ (R : ℝ) (w : Space n), squareEnergy (ENNReal.ofReal A • Measure.dirac z) k .mixed R w = 0) ∧
    (ENNReal.ofReal A • Measure.dirac z) univ = ENNReal.ofReal A ∧
    hausdorffP n k {z} = 0 ∧ (ENNReal.ofReal A • Measure.dirac z) {z}ᶜ = 0 ∧
    lowerDensity (ENNReal.ofReal A • Measure.dirac z) k z = ⊤ ∧
    upperDensity (ENNReal.ofReal A • Measure.dirac z) k z = ⊤ ∧
    ¬ (ENNReal.ofReal A • Measure.dirac z) ≪ hausdorffP n k ∧
    IsRegularlyRectifiableSet .mixed k {z} ∧
    ¬ IsRegularlyRectifiableMeasure .mixed k (ENNReal.ofReal A • Measure.dirac z)

/-- The density tests: the flat, diffuse and atomic tests. -/
def DensityTestsStatement : Prop :=
  FlatPatchTestStatement ∧ DiffuseTestStatement ∧ AtomTestStatement

end ParabolicRectifiability.Examples
