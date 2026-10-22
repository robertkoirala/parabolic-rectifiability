import ParabolicRectifiability.Foundations.Proofs.DensityBridges.FiniteUpperDensityStatement
import ParabolicRectifiability.Foundations.Proofs.UpperDensityBound
import ParabolicRectifiability.Foundations.Proofs.DensityBridges.FiniteUpperDensity

/-! # Finite upper density implies absolute continuity

The declarations delegate to the corresponding proof modules.
* `f2i_absolutelyContinuous_of_upperDensity_lt_top` states that finite upper `k`-density
  `μ`-a.e. implies `μ ≪ H_P^k`. Its proof is
  `f2i_absolutelyContinuous_of_upperDensity_lt_top_proof : f2i_UpperDensityACStatement`.
* `f2i_input_upperDensityBound` is the local upper-density bound used as a hypothesis. Its type
  is the body of `BetaP.c2_UpperDensityBoundStatement`; it is supplied by
  `Foundations.f2c_upperDensity_bound_proof : f2c_UpperDensityBoundStatement`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- **Local upper-density bound**, supplied by `f2c_upperDensity_bound_proof`. Body of
`BetaP.c2_UpperDensityBoundStatement`: if
`Θ^{k,*}(μ,z) < ∞`, there are a finite `A` and a radius `ρ > 0` with `Θ(z,r) ≤ A` for every
`0 < r < ρ`. Every measure; no regularity. It is the first
step of the density bridge. The wrapper below applies `f2c_upperDensity_bound_proof`. -/
theorem f2i_input_upperDensityBound :
    ∀ {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n), upperDensity μ k z < ⊤ →
      ∃ (A : ℝ≥0∞) (ρ : ℝ), A ≠ ⊤ ∧ 0 < ρ ∧
        ∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A := by
  exact ParabolicRectifiability.Foundations.f2c_upperDensity_bound_proof

/-- **Finite upper density implies absolute continuity.** `f2i_UpperDensityACStatement`: given
the local upper-density bound as a hypothesis, finite upper `k`-density `μ`-a.e. implies
`μ ≪ H_P^k`, for a locally Radon `μ`, `n ≥ 1`, `1 ≤ k ≤ n + 2`.

Route (integer classes, made global):
1. Classes. Consume the local upper-density bound, the hypothesis of the statement: at a point
   with `Θ^{k,*}(μ,z) < ∞` it gives a finite `A` and `ρ > 0` with `densityRatio μ k z r ≤ A` on
   `(0,ρ)`. Choose an integer `a ≥ A.toReal` and `j` with `1/(j+1) < ρ`; then `z` lies in
   `F a j = {z | ∀ r, 0 < r → r < 1/(j+1) → μ (ball z r) ≤ ofReal (a+1) * ofReal r ^ k}`
   (ratio to mass: `ENNReal.div_le_iff`, as in `fbfb1_mass_le_of_ratio_lt`).
   The bound itself is not reproved here.
2. All-centre growth of `ν = μ.restrict (F a j)` at radii `0 < r ≤ r₀ = 1/(4(j+1))`: if
   `ball p r` meets `F a j` at `z`, then `ball p r ⊆ ball z (2r)` with `2r < 1/(j+1)`, so
   `ν (ball p r) ≤ μ (ball z (2r)) ≤ (a+1) 2^k r^k`; otherwise `ν (ball p r) = 0`
   (`Measure.restrict_apply measurableSet_ball`). No measurability of `F a j` is needed.
3. `ν` is finite on compacts and inner regular (mathlib instances
   `InnerRegularCompactLTTop.restrict` and `source_sigmaFinite`, as in
   `restrict_isFiniteMeasureOnCompacts_innerRegular_proof`); then
   `fgac_absolutelyContinuous_hausdorffP_of_growth_proof`
   gives `ν ≪ H_P^k`.
4. If `H_P^k Z = 0`, then `μ (Z ∩ F a j) ≤ ν Z = 0` (`Measure.le_restrict_apply`), and
   `Z \ ⋃ F a j ⊆ {z | ¬ Θ^{k,*} < ∞}`, which is `μ`-null by hypothesis (`ae_iff`); conclude by
   `measure_iUnion_null` and `measure_union_null`.
A spatial bound `z ∈ P̄(0,N)` is not needed: the growth bound of step 2 holds at
every centre. The local upper-density bound remains an explicit input;
`f2i_input_upperDensityBound` supplies it. -/
theorem f2i_absolutelyContinuous_of_upperDensity_lt_top : f2i_UpperDensityACStatement := by
  exact ParabolicRectifiability.Foundations.f2i_absolutelyContinuous_of_upperDensity_lt_top_proof

end ParabolicRectifiability.Foundations
