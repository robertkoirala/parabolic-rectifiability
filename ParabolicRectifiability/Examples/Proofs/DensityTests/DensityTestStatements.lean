import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements
import ParabolicRectifiability.Examples.Statements.DensityExamples
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Named statements of the density-test examples

Definitions and proposition definitions only. Target: `Examples.density_tests_bundle :
DensityTestsStatement`, the conjunction
`FlatPatchTestStatement ∧ DiffuseTestStatement ∧ AtomTestStatement`.

**Diffuse conjunct** (the shared diffuse estimates are the statements `E2Diffuse…`):
* `E2DiffuseSquareStatement`: quadratic specialization of the shared output, in implication
  form over `EnergyTwoStatement` (`Foundations.f2c_energyTwo_proof`).
* `E2DiffuseDensityZeroStatement`: zero lower and upper densities at **every** point.
* `E2AmbientNullStatement`: `H_P^k(K) < ⊤ ⇒ λ(K) = 0` and its three consequences
  (absolute continuity, σ-finite nullity, vanishing of finite-Hausdorff good measures).
* `E2DiffuseAmplitudeStatement`: the constants `C, κ` (`squareEnergy_smul`).

**Flat and atom conjuncts**:
* `E2ModelCarriedSquareZeroStatement`: a measure carried by one model's set has zero square
  energy at every centre and endpoint (shared by flat and atom).
* `E2FlatPatchStatement`: the flat conjunct (implication form over the previous one).
* `E2AtomDensityStatement`: infinite lower and upper `k`-density of an atom at its point.
* `E2AtomStatement`: the atom conjunct (implication form over the model-carried and atom-density
  statements).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Diffuse conjunct -/

/-- The quadratic base data of the diffuse source: a real pointwise bound on the mixed square
energy of `ω` at endpoint `2`, and a positive finite outer integral over `P(0,1)`. -/
def E2DiffuseSquareBase (n k : ℕ) : Prop :=
  ∃ A : ℝ, 0 < A ∧
    (∀ z : Space n, squareEnergy (e2_diffuseBase n) k .mixed 2 z ≤ ENNReal.ofReal A) ∧
    0 < ∫⁻ z in Metric.ball (point 0 0) 1, squareEnergy (e2_diffuseBase n) k .mixed 2 z
      ∂(e2_diffuseBase n) ∧
    ∫⁻ z in Metric.ball (point 0 0) 1, squareEnergy (e2_diffuseBase n) k .mixed 2 z
      ∂(e2_diffuseBase n) < ⊤

/-- **Quadratic specialization.** Given `EnergyTwoStatement`
(`T_2^a = S^a`, used at endpoint `a = 2`), the shared output at `p = 2`, mixed family, gives the
quadratic base data. -/
def E2DiffuseSquareStatement : Prop :=
  EnergyTwoStatement →
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k < n + 2 →
      E2DiffuseEnergyBounds n k .mixed 2 →
      E2DiffuseSquareBase n k

/-- **Zero densities everywhere.** From the ball bound of `E2DiffuseSourceStatement`,
`0 ≤ μ_c(P(z,r))/r^k ≤ 2cω_n r^{n+2-k} → 0`, so both `k`-densities of `μ_c = c ω` vanish at
**every** point. -/
def E2DiffuseDensityZeroStatement : Prop :=
  E2DiffuseSourceStatement → ∀ n k : ℕ, k < n + 2 → ∀ (c : ℝ) (z : Space n),
    lowerDensity (ENNReal.ofReal c • e2_diffuseBase n) k z = 0 ∧
      upperDensity (ENNReal.ofReal c • e2_diffuseBase n) k z = 0

/-- **Ambient nullity and consequences.** For `k < n + 2`, every set of
finite `H_P^k` measure is ambient null, and therefore `μ_c = c ω` is absolutely continuous with
respect to `H_P^k`, vanishes on σ-finite `H_P^k` sets, and every measure `ν ≤ μ_c` carried by a
set of finite `H_P^k` measure is zero. -/
def E2AmbientNullStatement : Prop :=
  ∀ n k : ℕ, k < n + 2 →
    (∀ K : Set (Space n), hausdorffP n k K < ⊤ → parabolicVolume n K = 0) ∧
    ∀ c : ℝ,
      ENNReal.ofReal c • e2_diffuseBase n ≪ hausdorffP n k ∧
      (∀ A : ℕ → Set (Space n), (∀ i, hausdorffP n k (A i) < ⊤) →
        (ENNReal.ofReal c • e2_diffuseBase n) (⋃ i, A i) = 0) ∧
      (∀ ν : Measure (Space n), ν ≤ ENNReal.ofReal c • e2_diffuseBase n →
        ∀ K : Set (Space n), hausdorffP n k K < ⊤ → ν Kᶜ = 0 → ν = 0)

/-- **Quadratic amplitude constants.** From the quadratic base data there
are `C, κ > 0` with `S²_{μ_c} ≤ C c` everywhere and `∫_{P(0,1)} S²_{μ_c} dμ_c = κ c²` for every
`c > 0`. -/
def E2DiffuseAmplitudeStatement : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k < n + 2 → E2DiffuseSquareBase n k →
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ c : ℝ, 0 < c →
      (∀ z : Space n,
        squareEnergy (ENNReal.ofReal c • e2_diffuseBase n) k .mixed 2 z ≤
          ENNReal.ofReal (C * c)) ∧
      ∫⁻ z in Metric.ball (point 0 0) 1,
          squareEnergy (ENNReal.ofReal c • e2_diffuseBase n) k .mixed 2 z
            ∂(ENNReal.ofReal c • e2_diffuseBase n) =
        ENNReal.ofReal (κ * c ^ 2)

/-! ## Flat and atom conjuncts -/

/-- **Model-carried sources have zero square.** If a measure vanishes off
the set of one model `L` of the family `T`, its natural square energy vanishes at every centre
and every endpoint (a plane through `z` has zero fitting
error at every testing center and scale). -/
def E2ModelCarriedSquareZeroStatement : Prop :=
  ∀ (n k : ℕ) (T : FamilyKind) (μ : Measure (Space n)) (L : Models n k T),
    μ (modelSet L)ᶜ = 0 → ∀ (R : ℝ) (z : Space n), squareEnergy μ k T R z = 0

/-- **Flat patch.** The flat conjunct, in implication form over
`E2ModelCarriedSquareZeroStatement`. -/
def E2FlatPatchStatement : Prop :=
  E2ModelCarriedSquareZeroStatement → FlatPatchTestStatement

/-- **Atom densities.** For `k ≥ 1` and `A > 0`, the atom `A δ_z` has
infinite lower and upper `k`-density at `z`: `A δ_z(P(z,r))/r^k = A r^{-k} → ∞` -/
def E2AtomDensityStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → ∀ (z : Space n) (A : ℝ), 0 < A →
    lowerDensity (ENNReal.ofReal A • Measure.dirac z) k z = ⊤ ∧
      upperDensity (ENNReal.ofReal A • Measure.dirac z) k z = ⊤

/-- **Atom.** The atom conjunct, in implication form over
`E2ModelCarriedSquareZeroStatement` and `E2AtomDensityStatement`. -/
def E2AtomStatement : Prop :=
  E2ModelCarriedSquareZeroStatement → E2AtomDensityStatement → AtomTestStatement

end ParabolicRectifiability.Examples
