import ParabolicRectifiability.Examples.Statements.Lacunary
import ParabolicRectifiability.Examples.Statements.DensityExamples
import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Closure
import ParabolicRectifiability.Examples.Statements.Reductions
import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTests
import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies
import ParabolicRectifiability.Examples.Proofs.Reductions.Reductions
import ParabolicRectifiability.Examples.Proofs.Lacunary.SourceRegularity
import ParabolicRectifiability.Examples.Proofs.Lacunary.Estimates
import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Witness
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.Assembly

/-! # Intermediate statements for the examples

Each declaration below states one intermediate result used to prove the example theorems,
and obtains it from the corresponding proof in the example modules. The implication
`e2_exponent_witness_below_of` keeps its lower-energy estimate as an explicit input; here
`exponent_witness_below_bundle` supplies it from `e2_lacunary_estimates`.

| Statement | Content | Used by |
|---|---|---|
| `lacunary_series_convergence` | convergence of the lacunary primitive | `lacunary_convergence_skeleton` |
| `lacunary_estimates_bundle` | the lacunary graph estimates | `lacunary_estimates_skeleton`, the nonregular and witness proofs |
| `lacunarySource_finite_innerRegular_ac` | restricted sources are finite Radon and `≪ H_P²` | `lacunarySource_graph_image_eq_zero` |
| `exists_restriction_carried_by_graph` | restriction to the preimage of a regular graph | `lacunarySource_graph_image_eq_zero` |
| `lacunaryGraphMap_mem_ball_of_quarter` | the quarter graph lies in `P(0,1)` | `exponent_witness_above_carrier_of_providers` |
| `lintegral_energyT_quarter_pos` | positive energy of the `p > 2` witness | `exponent_witness_above_energy_skeleton` |
| `exponent_witness_below_bundle` | the `p < 2` exponent witness | `exponent_witnesses_of_providers` |
| `dense_atoms_bundle` | the dense-atom example | `dense_atoms_skeleton` |
| `density_tests_bundle` | the flat, diffuse and atomic tests | `density_tests_skeleton` |
| `reductions_bundle` | the exact reductions | `reductions_skeleton` |
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **Convergence of the lacunary primitive.**

This is `LacunaryConvergenceStatement`: under `0 < ε ≤ 3/16` and
`IsLacunaryData a N`, the series `Σ_j a_j N_j^{-1/2} cos(N_j t)` is absolutely summable at
every `t`, and the partial sums converge uniformly to `lacunaryFunction ε a N`. The proof is
the Weierstrass test with the geometric decay `a_{j+1}/√N_{j+1} ≤ a_j/(1000 √N_j)`. -/
theorem lacunary_series_convergence : LacunaryConvergenceStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_convergence

/-- **The lacunary estimates.**

This is `LacunaryEstimatesStatement`, the conjunction of the isometry, the
exact ball identity, the Hausdorff identity `H_P²(F(E)) = c_H |E|`, the density limit, the
full-interval regularity, the all-scale upper `T_q` bound (`q ≥ 1`), the restriction-stable
lower `T_q` bound (`q > 0`, with `j₀` chosen before `q`), and the small-slope ordinary covers.
The nonregular example and the exponent witness above `2` use its conjuncts. -/
theorem lacunary_estimates_bundle : LacunaryEstimatesStatement := by
  exact ParabolicRectifiability.Examples.e2_lacunary_estimates

/-- **Restricted lacunary sources are finite Radon and absolutely continuous.**

For `0 < ε ≤ 3/16`, lacunary data `a`, `N`, and every Lebesgue measurable
`E ⊆ J`, the source `ν_E = F_#(L¹⌊E)` is a finite measure, inner regular, and
`ν_E ≪ H_P²` (on arbitrary sets). The absolute continuity is the Hausdorff identity
`H_P²(F(E')) = c_H |E'|` applied to `E' = E ∩ F⁻¹(A')` for a Borel `H_P²`-null hull `A'`;
finiteness is `|E| ≤ 2`; inner regularity holds for finite Borel measures on the Polish space
`Space 1`.

Used in `lacunarySource_graph_image_eq_zero` (the graph-source contradiction), the
divergence lemma `lacunarySource_ae_squareEnergy_eq_top`, and the Hausdorff-null residual
clauses of the nonregular example and the exponent witnesses. -/
theorem lacunarySource_finite_innerRegular_ac :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
      IsFiniteMeasure (lacunarySource ε a N E) ∧ (lacunarySource ε a N E).InnerRegular ∧
        lacunarySource ε a N E ≪ hausdorffP 1 2 := by
  exact ParabolicRectifiability.Examples.e2_lacunarySource_finite_innerRegular_ac

/-- **The Borel preimage of a regular graph.** If `ν_J(G) > 0`, the Borel preimage
`E = F⁻¹(G) ∩ J` has positive measure.

Precisely: for `0 < ε ≤ 3/16`, lacunary data, a Lebesgue measurable `E₀ ⊆ J` and every
full general regular vertical graph `G` of `Space 1` in dimension `2` (any norm `η`), there is
a Lebesgue measurable `E ⊆ E₀` (namely `E₀ ∩ F⁻¹(G)`) whose restricted source has total mass
`ν_E(X) = ν_{E₀}(G)` and is carried by `G`: `ν_E(Gᶜ) = 0`. The image of `G` is closed (the
graph of a Lipschitz function over `W × ℝ`), so the preimage is Borel. The statement is made
for every `E₀ ⊆ J` because the exponent witness uses `E₀ = [-1/4,1/4]`.

Used in `lacunarySource_graph_image_eq_zero`. -/
theorem exists_restriction_carried_by_graph :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E₀ : Set ℝ, NullMeasurableSet E₀ volume → E₀ ⊆ lacunaryInterval →
    ∀ (η : ℝ) (G : GeneralRegularVerticalGraph 1 2 η),
      ∃ E : Set ℝ, NullMeasurableSet E volume ∧ E ⊆ E₀ ∧
        lacunarySource ε a N E univ = lacunarySource ε a N E₀ G.image ∧
        lacunarySource ε a N E (G.image)ᶜ = 0 := by
  exact ParabolicRectifiability.Examples.e2_exists_restriction_carried_by_graph

/-- **The quarter graph lies in the unit cylinder**, so the witness above `2` is supported
in `P(0,1)`.

For `0 < ε ≤ 3/16` and lacunary data, `F(t) ∈ P(0,1)` for every
`t ∈ [-1/4,1/4]`. Indeed `|f(t)| ≤ ε Σ_j a_j N_j^{-1/2} ≤ (3/16)(1000/999) < 1` by the
geometric decay of `a_j N_j^{-1/2}`, and the time part is `√|t| ≤ 1/2`.

Used for the support clause of `exponent_witness_above_carrier_of_providers`. -/
theorem lacunaryGraphMap_mem_ball_of_quarter :
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ t ∈ Icc (-1 / 4 : ℝ) (1 / 4), lacunaryGraphMap ε a N t ∈ Metric.ball (point 0 0) 1 := by
  exact ParabolicRectifiability.Examples.e2_lacunaryGraphMap_mem_ball_of_quarter

/-- **Positive energy of the `p > 2` witness**, a consequence of the lower energy estimate.

For every `p > 0`, `0 < ε ≤ 3/16` and lacunary data,
`0 < ∫ T²_{p,ν} dν` for `ν = ν_{[-1/4,1/4]}`. Proof route (a compact measurable minorant;
measurability of the whole energy `z ↦ T²_{p,ν}(z)` is not needed): put `I = [-1/8,1/8]` and
`K = F(I)`, which is compact, with `ν(K) ≥ |I| = 1/4`. Choose one sufficiently large `j` such
that, for every `t ∈ I`, its period interval stays inside the quarter interval and its scale band
lies below the endpoint `2`. The plateau and lower estimates then give,
uniformly in `t ∈ I`, `T²_{p,ν}(F(t)) ≥ c(p) ε^p a_j^p =: b > 0`. Hence `b 1_K ≤ T²_{p,ν}`, and
by monotonicity of the lower Lebesgue integral `∫⁻ T²_{p,ν} dν ≥ b ν(K) ≥ b/4 > 0`. Borel
measurability of the beta-`p` energies (`BetaPowMeasurabilityStatement`) is not needed for
this argument.

Used in `exponent_witness_above_energy_skeleton`. -/
theorem lintegral_energyT_quarter_pos :
    ∀ p : ℝ, 0 < p → ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 →
    IsLacunaryData a N →
      0 < ∫⁻ z, energyT (lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) 2 .mixed p 2 z
        ∂(lacunarySource ε a N (Icc (-1 / 4) (1 / 4))) := by
  exact ParabolicRectifiability.Examples.e2_lintegral_energyT_quarter_pos

/-- **The `p < 2` exponent witness.**

This is `ExponentWitnessBelowStatement`: for `a_j = c₀/(√j log(j+1))`, `a ∈ ℓ²`,
`a ∉ ℓ^p` (`p < 2`), the full function is general regular on the zero vertical base with
`Lip_P f ≤ C ε ‖a‖_∞`, `[h]_BMO ≤ C ε ‖a‖₂` for a `2π`-periodic representative `h` that is the
periodic `L²` limit of `(2π)^{-1/2} ε Σ_j a_j cos(N_j t)`, and `T^R_{p,ν_J}(F(t)) = ∞` for
`0 < p < 2`. The lower energy estimate is taken from `e2_lacunary_estimates`.

Used in `exponent_witnesses_of_providers`. -/
theorem exponent_witness_below_bundle : ExponentWitnessBelowStatement := by
  obtain ⟨hIsometry, hBall, hHausdorff, hDensity, hFullInterval, hUpperEnergy,
    hLowerEnergy, hSmallSlope⟩ := e2_lacunary_estimates
  exact e2_exponent_witness_below_of hLowerEnergy
    (e2_lacunary_kernelBound e2_lacunaryWeight) e2_kernelSum_le
    e2_lacunary_invSqrtDecay e2_lacunary_convergence fhpa_halfTimeBracketIntegrable

/-- **The dense atoms example.**

This is `DenseAtomsStatement` (finite nonzero Radon, `Σ w ≤ 1`, finite pair
sum and integrated energy, infinite densities at the atoms, `Θ^{k,*} ≥ a` a.e., `supp μ = D`,
`H_P^k(D) = ∞`, `D` not regularly rectifiable). -/
theorem dense_atoms_bundle : DenseAtomsStatement := by
  exact e2_dense_atoms

/-- **The flat, diffuse and atomic density tests**, that is, `DensityTestsStatement`. -/
theorem density_tests_bundle : DensityTestsStatement := by
  exact ParabolicRectifiability.Examples.e2_density_tests

/-- **Exact reduction witnesses**, that is, `ReductionsStatement` (time-slice identity and
tube identity, stationary-product comparison, stationary graph extensions). -/
theorem reductions_bundle : ReductionsStatement := by
  exact ParabolicRectifiability.Examples.e2_reductions

end ParabolicRectifiability.Examples
