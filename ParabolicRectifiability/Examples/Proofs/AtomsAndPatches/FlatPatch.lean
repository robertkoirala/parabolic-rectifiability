import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements

/-! # Flat patch

Proof of `E2FlatPatchStatement` (`e2_flatPatch_proof`) from `E2ModelCarriedSquareZeroStatement`:
a measure carried by a single model has zero square energy. -/

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

theorem e2_flatPatch_proof : E2FlatPatchStatement := by
  intro hF1 n _ k _ _ L D hD _ hDpos c hc
  have hc' : ENNReal.ofReal c ≠ 0 := by simpa using hc
  refine ⟨?_, ?_⟩
  · intro R z
    apply hF1 n k .mixed _ L _ R z
    rw [Measure.smul_apply, Measure.restrict_apply (modelSet_isClosed L).isOpen_compl.measurableSet]
    have : (modelSet L)ᶜ ∩ D = ∅ := by
      ext x; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
      exact fun h => h.1 (hD h.2)
    simp [this]
  · intro X hX
    by_contra hpos
    have h0 : hausdorffP n k X = 0 := by simpa using hpos
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hX
    have hXc : ((hausdorffP n k).restrict D) Xᶜ = 0 := hX.resolve_left hc'
    have h1 : ((hausdorffP n k).restrict D) X = 0 :=
      nonpos_iff_eq_zero.mp ((Measure.restrict_le_self X).trans h0.le)
    have h2 : hausdorffP n k D = 0 := by
      have := measure_univ_le_add_compl (μ := (hausdorffP n k).restrict D) X
      rw [h1, hXc, add_zero] at this
      rw [Measure.restrict_apply_univ] at this
      exact nonpos_iff_eq_zero.mp this
    exact absurd hDpos (by simp [h2])

end ParabolicRectifiability.Examples
