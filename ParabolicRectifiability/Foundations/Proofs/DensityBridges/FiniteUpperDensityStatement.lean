import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Metric.Hausdorff

/-! # Finite upper density implies absolute continuity: the statement

The statement `f2i_UpperDensityACStatement`: finite upper `k`-density almost everywhere forces
`μ ≪ H_P^k`. It is the energy-free clause of the density bridge, the step "finite upper density
exhausts the source by the classes `F_{a,j,N}`" of the canonical decomposition, and, at
`k = n + 2`, the implication from positive finite upper density to absolute continuity in the
ambient characterization.

The statement is in implication form: it takes the local upper-density bound as a hypothesis,
written out inline as the body of `BetaP.c2_UpperDensityBoundStatement`. That bound is proved as
`Foundations.f2c_upperDensity_bound_proof : f2c_UpperDensityBoundStatement` (same body) and is
not reproved here.

It is used by `f2i_ambient_rectifiable_iff_ac_iff_density` and by
`IntegralCanonical.i2_isIntrinsicSource_of_hasPositiveFiniteUpperDensity`.

Proposition definitions only.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Finite upper density implies absolute continuity** (implication form). Hypothesis: the
local upper-density bound (the body of `BetaP.c2_UpperDensityBoundStatement`): at every point of finite upper
`k`-density there are a finite `A` and a radius `ρ > 0` with `Θ(z,r) ≤ A` for `0 < r < ρ`.
Conclusion: for `n ≥ 1`, `1 ≤ k ≤ n + 2` and a locally Radon `μ` (finite on compacts and inner
regular), if `Θ^{k,*}(μ,z) < ∞` for `μ`-almost every `z`, then `μ ≪ H_P^k` (`hausdorffP n k`,
absolute continuity on arbitrary sets). No positive density, square function or carrier
hypothesis. -/
def f2i_UpperDensityACStatement : Prop :=
  (∀ {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n), upperDensity μ k z < ⊤ →
    ∃ (A : ℝ≥0∞) (ρ : ℝ), A ≠ ⊤ ∧ 0 < ρ ∧
      ∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A) →
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    (∀ᵐ z ∂μ, upperDensity μ k z < ⊤) → μ ≪ hausdorffP n k

end ParabolicRectifiability.Foundations
