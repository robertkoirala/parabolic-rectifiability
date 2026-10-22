import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements

/-! Proof of the mass and regularity properties of the dense atomic measure. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private theorem e2_dm_geometric_sum :
    ∑' j : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹) = 1 := by
  have hterm (j : ℕ) :
      ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹) = ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)]
    rw [← ENNReal.inv_pow]
    norm_num
  calc
    _ = ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) := by
      apply tsum_congr
      exact hterm
    _ = (2 : ℝ≥0∞)⁻¹ * (1 - (2 : ℝ≥0∞)⁻¹)⁻¹ :=
      ENNReal.tsum_geometric_add_one _
    _ = 1 := by
      rw [ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)

/-- The dense atomic measure is finite, inner regular and nonzero, with finite mass and pair sum. -/
theorem e2_dense_measure_proof : E2DenseWeightStatement → E2DenseMeasureStatement := by
  intro hweights n k z
  rcases hweights n k z with ⟨hpositive, hweightBound, hpairBound⟩
  let μ : Measure (Space n) := denseAtomMeasure k z
  have hmass : μ univ = ∑' j, ENNReal.ofReal (denseAtomWeight k z j) := by
    simp [μ, denseAtomMeasure]
  have hweightsFinite :
      (∑' j, ENNReal.ofReal (denseAtomWeight k z j)) ≤ 1 := by
    calc
      _ ≤ ∑' j, ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹) :=
        ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hweightBound j)
      _ = 1 := e2_dm_geometric_sum
  have hfinite : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    exact (hmass ▸ hweightsFinite).trans_lt ENNReal.one_lt_top
  let : IsFiniteMeasure μ := hfinite
  have hregular : μ.InnerRegular := by infer_instance
  have hzeroAtom : 0 < ENNReal.ofReal (denseAtomWeight k z 0) :=
    ENNReal.ofReal_pos.mpr (hpositive 0)
  have hfirstMass : ENNReal.ofReal (denseAtomWeight k z 0) ≤ μ {z 0} := by
    have hle := Measure.le_sum
      (fun j => ENNReal.ofReal (denseAtomWeight k z j) • Measure.dirac (z j)) 0
    have hcomponent : ENNReal.ofReal (denseAtomWeight k z 0) ≤
        (Measure.sum fun j => ENNReal.ofReal (denseAtomWeight k z j) • Measure.dirac (z j)) {z 0} := by
      simpa [Measure.smul_apply] using hle {z 0}
    simpa [μ, denseAtomMeasure] using hcomponent
  have hnonzero : μ ≠ 0 := by
    intro hμ
    have hle : ENNReal.ofReal (denseAtomWeight k z 0) ≤ 0 := by
      simpa [hμ] using hfirstMass
    exact (not_le_of_gt hzeroAtom) hle
  have hpairFinite :
      (∑' j, ∑ i ∈ Finset.range j,
        ENNReal.ofReal (denseAtomWeight k z i * denseAtomWeight k z j *
          (dist (z i) (z j) ^ k)⁻¹)) < ⊤ := by
    have hsumBound (j : ℕ) :
        (∑ i ∈ Finset.range j,
          ENNReal.ofReal (denseAtomWeight k z i * denseAtomWeight k z j *
            (dist (z i) (z j) ^ k)⁻¹)) ≤ ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact ENNReal.ofReal_le_ofReal (hpairBound j)
      · intro i hi
        exact mul_nonneg (mul_nonneg (le_of_lt (hpositive i)) (le_of_lt (hpositive j)))
          (inv_nonneg.mpr (pow_nonneg dist_nonneg _))
    have htsumBound :
        (∑' j, ∑ i ∈ Finset.range j,
          ENNReal.ofReal (denseAtomWeight k z i * denseAtomWeight k z j *
            (dist (z i) (z j) ^ k)⁻¹)) ≤ 1 := by
      calc
        _ ≤ ∑' j, ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹) :=
          ENNReal.tsum_le_tsum hsumBound
        _ = 1 := e2_dm_geometric_sum
    exact htsumBound.trans_lt ENNReal.one_lt_top
  simpa [μ] using ⟨hfinite, hregular, hnonzero, hweightsFinite, hpairFinite⟩

end ParabolicRectifiability.Examples
