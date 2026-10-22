import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Examples.Proofs.AtomsAndPatches.AmbientNull
import ParabolicRectifiability.Examples.Proofs.AtomsAndPatches.Atom
import ParabolicRectifiability.Examples.Proofs.AtomsAndPatches.AtomDensity
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.SquareEnergy
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.Amplitude
import ParabolicRectifiability.Examples.Proofs.DiffuseMeasures.DensityZero
import ParabolicRectifiability.Examples.Proofs.AtomsAndPatches.FlatPatch
import ParabolicRectifiability.Examples.Proofs.AtomsAndPatches.ModelCarriedSquareZero
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergyTwo

/-! # Statements specific to the density tests

Each statement is proved by the corresponding module.
-/

namespace ParabolicRectifiability.Examples

/-! ## The energy identity at endpoint two -/

/-- **The energy identity `EnergyTwoStatement`.** The diffuse statements consume it as an
input rather than re-deriving it, so that the quadratic energy identity has one source.
It is closed by `Foundations.f2c_energyTwo_proof` (the implication-form assembly
`e2_density_tests_of Foundations.f2c_energyTwo_proof` can be used directly). It is not
`Foundations.energyS_energyT_two_eq`. Used by `e2_diffuseTest` (through `e2_diffuseTest_of`). -/
theorem e2_input_energyTwo : Foundations.EnergyTwoStatement := by
  exact Foundations.f2c_energyTwo_proof

/-! ## Diffuse, flat and atom statements -/

/-- **Quadratic specialization.** Implication form over `EnergyTwoStatement`. Route: the hypothesis
`EnergyTwoStatement` at endpoint `a = 2 > 0`, mixed family, gives
`energyT ω k .mixed 2 2 z = squareEnergy ω k .mixed 2 z` at every `z` (its second conjunct;
`1 ≤ n`, `1 ≤ k`, `k ≤ n + 2` from the hypotheses). Rewrite the `T`-clauses of the shared output
`E2DiffuseEnergyBounds n k .mixed 2` with it and take `A = A_T`. -/
theorem e2_diffuse_square : E2DiffuseSquareStatement := by
  exact e2e1_diffuse_square_proof

/-- **Zero densities everywhere.** Implication form over the source bounds. Route: for `r > 0`,
`densityRatio (c•ω) k z r = c ω(P(z,r))/r^k ≤ 2cω_n r^{n+2-k}` (`Measure.smul_apply`, the source bounds,
`ENNReal.div_le_of_le_mul`); the right side tends to `0` as `r ↓ 0` because `n + 2 - k ≥ 1`
(`ENNReal.Tendsto.const_mul`, `ENNReal.tendsto_pow_atTop`-type continuity of `ofReal r ^ m` at
`0`); then `limsup = 0` (`ENNReal` squeeze, `Filter.limsup_le_of_le`) and
`liminf ≤ limsup`. A nonpositive `c` gives the zero measure. -/
theorem e2_diffuse_densityZero : E2DiffuseDensityZeroStatement := by
  exact e2_diffuse_densityZero_proof

/-- **Ambient nullity and its consequences.** Route: `hausdorffMeasure_zero_or_top`
with `k < n + 2` turns `H_P^k(K) < ⊤` into
`H_P^{n+2}(K) = 0`; `parabolicVolume_smul_le_hausdorff` and
`(2ω_n)⁻¹ ≠ 0` give `λ(K) = 0`. Consequences for `μ_c = c ω`, arbitrary (non-measurable) sets:
`μ_c(N) ≤ c λ(N)` (`Measure.restrict_le_self`); a Hausdorff-null set has finite measure, hence
`μ_c ≪ H_P^k`; countable unions by `measure_iUnion_null`; for `ν ≤ μ_c` carried by `K`,
`ν univ ≤ ν K + ν Kᶜ ≤ μ_c K = 0` (`measure_univ_le_add_compl`, `Measure.le_iff'`). -/
theorem e2_ambientNull : E2AmbientNullStatement := by
  exact e2_ambientNull_proof

/-- **Quadratic amplitude constants.** Route: `squareEnergy_smul` (with the
instance `Nonempty (Models n k .mixed)` from `AdmissibleModel.nonempty_of_range`) gives
`S²_{cω} = c S²_ω ≤ c A`, so `C = A`; for the outer integral `Measure.restrict_smul`,
`lintegral_smul_measure` and `lintegral_const_mul'` give `c² · E_0` with `E_0` the positive finite
base integral; `κ = E_0.toReal > 0` and `ofReal (κ c²) = ofReal c ^ 2 · E_0`
(`ENNReal.ofReal_mul`, `ENNReal.ofReal_toReal`). -/
theorem e2_diffuse_amplitude : E2DiffuseAmplitudeStatement := by
  exact e2_diffuse_amplitude_proof

/-- **Model-carried sources have zero square.** Route: for `r > 0`, `betaSq μ k T z r ≤ r^{-(k+2)} fit μ L z r`
(`betaSq_of_pos`; `iInf_le`), and
`fit μ L z r = ∫_{P(z,r)} modelCost L dμ = 0` because `modelCost L = infEDist(·, modelSet L)^2`
vanishes on `modelSet L` (`Metric.infEDist_zero_of_mem`) and `μ (modelSet L)ᶜ = 0`
(`setLIntegral` of an a.e.-zero function: `ae_iff`, `lintegral_eq_zero_iff`-free route via
`setLIntegral_congr_fun`-type a.e. congruence on `ae_restrict_of_ae`); nonpositive radii give `0`
by definition; then `squareEnergy = ∫ 0 = 0`. -/
theorem e2_squareEnergy_zero_of_modelCarried : E2ModelCarriedSquareZeroStatement := by
  exact e2_squareEnergy_zero_of_modelCarried_proof

/-- **Flat patch.**
Implication form over the model-carried statement. Route: zero square by it with the given model `L`, since
`(c • H_P^k⌊D)((modelSet L)ᶜ) = c H_P^k((modelSet L)ᶜ ∩ D) = 0` (`modelSet_isClosed`,
`Measure.restrict_apply`, `D ⊆ modelSet L`). Carrier: if `H_P^k(X) = 0` then
`H_P^k(D) = (H_P^k⌊D)(univ) ≤ (H_P^k⌊D)(X) + (H_P^k⌊D)(Xᶜ) ≤ H_P^k(X) + 0 = 0`
(`Measure.restrict_le_self`, `measure_univ_le_add_compl`, `c > 0`), contradicting `0 < H_P^k(D)`.
`D` need not be measurable. -/
theorem e2_flatPatch : E2FlatPatchStatement := by
  exact e2_flatPatch_proof

/-- **Atom densities.** Route: for
`r > 0`, `z ∈ P(z,r)` so `densityRatio (A δ_z) k z r = ofReal A / ofReal r ^ k`; as `r ↓ 0`,
`ofReal r ^ k → 0⁺` (`k ≥ 1`) and `ofReal A ≠ 0`, so the ratio tends to `⊤`
(`ENNReal.Tendsto.div_const`-type / `ENNReal.tendsto_inv_iff`); `liminf` and `limsup` of a
function tending to `⊤` along `𝓝[>] 0` are `⊤` (`Filter.Tendsto.liminf_eq`,
`Filter.Tendsto.limsup_eq`). -/
theorem e2_atom_density : E2AtomDensityStatement := by
  exact e2_atom_density_proof

/-- **Atom.**
Implication form over the model-carried and atom-density statements. Route: zero square by the former with a mixed model through `z`
(`AdmissibleModel.nonempty_of_range`, `exists_model_mem`; `Measure.dirac_apply'` on the closed
`(modelSet L)ᶜ`); mass `ofReal A`; `H_P^k{z} = 0` (`Measure.noAtoms_hausdorff`, `k > 0`);
`(A δ_z){z}ᶜ = 0`; densities by the atom-density statement; `¬ μ ≪ H_P^k` from `μ{z} = A > 0`; the set `{z}` is
regularly rectifiable: at every tolerance `ε > 0` apply
`Characterization.hasTypedGraphCover_of_null .mixed ε` to the Hausdorff-null singleton
(reusing the existing empty families); the measure is not, by the
failed absolute continuity (`IsRegularlyRectifiableMeasure`). -/
theorem e2_atom : E2AtomStatement := by
  exact e2_atom_proof

end ParabolicRectifiability.Examples
