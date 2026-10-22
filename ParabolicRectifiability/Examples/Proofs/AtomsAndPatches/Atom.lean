import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Characterization.Assembly.CoveringLemmas
import ParabolicRectifiability.Geometry.AdmissibleModels
import ParabolicRectifiability.Foundations.Graphs

/-! # The atom density test

An atom `A δ_z` has zero square energy, a Hausdorff-null carrier and infinite densities, but it
is not absolutely continuous with respect to `H_P^k`; so its carrier is regularly rectifiable as
a set while the measure is not. `e2_atom_proof` derives this from
`E2ModelCarriedSquareZeroStatement` and `E2AtomDensityStatement`.

Proof outline:
* a mixed model through `z` (`AdmissibleModel.nonempty_of_range`, `exists_model_mem`) carries the
  atom, so `E2ModelCarriedSquareZeroStatement` gives zero square;
* `H_P^k {z} = 0` by `Measure.nullSingletonClass_hausdorff` (`k > 0`);
* the set clause is `Characterization.hasTypedGraphCover_of_null .mixed ε` on the null singleton,
  at every `ε`;
* the measure clause fails because absolute continuity fails (`μ {z} = ofReal A ≠ 0`). -/

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The singleton is `H_P^k`-null for `k ≥ 1` (`Measure.nullSingletonClass_hausdorff`). -/
theorem e2f4_hausdorff_singleton {n k : ℕ} (hk : 1 ≤ k) (z : Space n) :
    hausdorffP n k {z} = 0 := by
  let := Measure.nullSingletonClass_hausdorff (Space n) (Nat.cast_pos.mpr hk : (0 : ℝ) < k)
  change (Measure.hausdorffMeasure (k : ℝ) : Measure (Space n)) {z} = 0
  exact measure_singleton z

/-- **Atom.** The atom `A δ_z` passes the set test but fails the measure test, given that
model-carried measures have zero square energy and the atom densities are infinite. -/
theorem e2_atom_proof : E2AtomStatement := by
  intro hF1 _hF3 n hn k hk hkn z A hA
  have hAne : ENNReal.ofReal A ≠ 0 := by simpa using hA
  have hnull : hausdorffP n k {z} = 0 := e2f4_hausdorff_singleton hk z
  have hmass : (ENNReal.ofReal A • Measure.dirac z) {z} = ENNReal.ofReal A := by
    simp
  have hnotAC : ¬ (ENNReal.ofReal A • Measure.dirac z) ≪ hausdorffP n k := by
    intro hac
    exact hAne (hmass ▸ hac hnull)
  refine ⟨?_, ?_, hnull, ?_, (_hF3 n k hk z A hA).1, (_hF3 n k hk z A hA).2, hnotAC, ?_, ?_⟩
  · intro R w
    obtain ⟨L, hzL⟩ := exists_model_mem (T := .mixed)
      (AdmissibleModel.nonempty_of_range hn hk hkn) z
    apply hF1 n k .mixed _ L _ R w
    rw [Measure.smul_apply, Measure.dirac_apply' _ (modelSet_isClosed L).isOpen_compl.measurableSet]
    simp [hzL]
  · simp
  · rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton z).compl]
    simp
  · intro ε _
    exact Characterization.hasTypedGraphCover_of_null .mixed ε hnull
  · intro h
    exact hnotAC h.1
end ParabolicRectifiability.Examples
