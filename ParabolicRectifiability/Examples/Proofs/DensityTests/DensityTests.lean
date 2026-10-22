import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestLemmas
import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimates

/-! # Assembly of the density tests

* `e2_diffuseTest_of (hE2 : EnergyTwoStatement) : DiffuseTestStatement`: the diffuse conjunct,
  assembled from the shared output `e2_diffuse_energyBounds` (at `p = 2`, mixed family) and the
  four statements specific to this example, with `EnergyTwoStatement` as a declared input.
  Positivity and finiteness of the quadratic integral follow from the `κ c²` identity.
* `e2_density_tests_of (hE2 : EnergyTwoStatement) : DensityTestsStatement`: the bundle, in the
  same implication form. It is applied to `Foundations.f2c_energyTwo_proof`.
* `e2_diffuseTest`, `e2_density_tests`: the same, with `EnergyTwoStatement` supplied by
  `e2_input_energyTwo`. `e2_density_tests` has exactly the type of
  `density_tests_bundle`.

The sharpness argument uses from `DiffuseTestStatement` only the σ-finite nullity clause,
which comes from `E2AmbientNullStatement` alone.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- **The diffuse conjunct** `DiffuseTestStatement`, with `EnergyTwoStatement` as a
declared input. -/
theorem e2_diffuseTest_of (hE2 : EnergyTwoStatement) : DiffuseTestStatement := by
  intro n hn k hk hkn
  have hmix : Nonempty (Models n k .mixed) :=
    (AdmissibleModel.nonempty_of_range hn hk hkn.le : Nonempty (AdmissibleModel n k))
  obtain ⟨C, κ, hC, hκ, hamp⟩ := e2_diffuse_amplitude n k hn hk hkn
    (e2_diffuse_square hE2 n k hn hk hkn
      (e2_diffuse_energyBounds n k .mixed 2 hkn hmix two_pos))
  obtain ⟨-, hnull⟩ := e2_ambientNull n k hkn
  refine ⟨C, κ, hC, hκ, fun c hc => ?_⟩
  obtain ⟨hpt, hint⟩ := hamp c hc
  obtain ⟨hac, hsig, hgood⟩ := hnull c
  have hpos : 0 < ENNReal.ofReal (κ * c ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
  intro μ
  exact ⟨Filter.Eventually.of_forall fun z =>
      e2_diffuse_densityZero e2_diffuse_source n k hkn c z,
    lt_of_lt_of_eq hpos hint.symm, hint.trans_lt ENNReal.ofReal_lt_top, hac, hsig, hpt, hint,
    hgood⟩

/-- **The density tests in implication form over `EnergyTwoStatement`.** Applying it to
`Foundations.f2c_energyTwo_proof` gives the unconditional statement. -/
theorem e2_density_tests_of (hE2 : EnergyTwoStatement) : DensityTestsStatement :=
  ⟨e2_flatPatch e2_squareEnergy_zero_of_modelCarried, e2_diffuseTest_of hE2,
    e2_atom e2_squareEnergy_zero_of_modelCarried e2_atom_density⟩

/-- The diffuse conjunct with `EnergyTwoStatement` from `e2_input_energyTwo`. -/
theorem e2_diffuseTest : DiffuseTestStatement :=
  e2_diffuseTest_of e2_input_energyTwo

/-- **The density tests**: exactly the type of `density_tests_bundle`, with
`EnergyTwoStatement` from `e2_input_energyTwo`. -/
theorem e2_density_tests : DensityTestsStatement :=
  e2_density_tests_of e2_input_energyTwo

end ParabolicRectifiability.Examples
