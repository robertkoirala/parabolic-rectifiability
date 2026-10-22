import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateLemmas

/-! # Assembly of the shared diffuse estimates

* `e2_diffuse_fitLower`: the uniform lower-fit interface for every family, from the horizontal
  and vertical lower-fit statements (cases on the family and, for the mixed family, on the
  model).
* `e2_diffuse_energyBounds`: the shared output `E2DiffuseEnergyBounds n k T p` for every
  available family and every `p > 0`, the common input of the diffuse test for the
  square-function sharpness statements and of the diffuse conjunct of the density tests.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The uniform lower fit (the horizontal and vertical lower fits combined): one constant
`min a_H a_V > 0` for every model of every family. -/
theorem e2_diffuse_fitLower (n k : ℕ) (T : FamilyKind) (p : ℝ) (hkn : k < n + 2) (hp : 0 < p) :
    E2DiffuseFitLower n k T p := by
  obtain ⟨ah, hah, hH⟩ := e2_diffuse_horizontalLower n k p hp
  obtain ⟨av, hav, hV⟩ := e2_diffuse_verticalLower n k p hkn hp
  have hmH : ∀ x : ℝ≥0∞, ENNReal.ofReal (min ah av) * x ≤ ENNReal.ofReal ah * x := fun x =>
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_left _ _)) x
  have hmV : ∀ x : ℝ≥0∞, ENNReal.ofReal (min ah av) * x ≤ ENNReal.ofReal av * x := fun x =>
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (min_le_right _ _)) x
  refine ⟨min ah av, lt_min hah hav, fun L z hz r hr => ?_⟩
  cases T with
  | horizontal => exact (hmH _).trans (hH L z hz r hr)
  | vertical => exact (hmV _).trans (hV L z hz r hr)
  | mixed =>
    rcases L with L | L
    · exact (hmH _).trans (hH L z hz r hr)
    · exact (hmV _).trans (hV L z hz r hr)

/-- **The shared diffuse output**: for `k < n + 2`, every available family and
every `p > 0`, both energies of `ω` at endpoint `2` are bounded everywhere and have positive
finite outer integrals over `P(0,1)`. -/
theorem e2_diffuse_energyBounds (n k : ℕ) (T : FamilyKind) (p : ℝ) (hkn : k < n + 2)
    (hT : Nonempty (Models n k T)) (hp : 0 < p) : E2DiffuseEnergyBounds n k T p :=
  e2_diffuse_energy e2_diffuse_source e2_diffuse_betaUpper e2_scaleIntegral n k T p hkn hT hp
    (e2_diffuse_betaLower n k T p hkn hp (e2_diffuse_fitLower n k T p hkn hp))

end ParabolicRectifiability.Examples
