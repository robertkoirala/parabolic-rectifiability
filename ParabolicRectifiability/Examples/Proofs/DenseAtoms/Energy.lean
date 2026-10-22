import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements

/-! # Finite integrated energy of the dense atomic source

The atomic square bound is integrated against the dense atomic measure. The double sum over
pairs of atoms is symmetrized to a sum over `i < j`, and the recursive pair bound of the weights
makes it finite.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Examples

private theorem triangular_tsum (f : ℕ → ℕ → ℝ≥0∞)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑' i, ∑' j, f i j) =
      (∑' j, ∑ i ∈ Finset.range j, f i j) +
        (∑' j, ∑ i ∈ Finset.range j, f i j) := by
  classical
  have hfinite (i : ℕ) :
      (∑' j, if j < i then f j i else 0) = ∑ j ∈ Finset.range i, f j i := by
    rw [tsum_eq_sum (s := Finset.range i)]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]
    · intro j hj
      simp [Finset.mem_range] at hj
      simp [not_lt.mpr hj]
  have hsplit (i j : ℕ) : f i j =
      (if j < i then f j i else 0) + (if i < j then f i j else 0) := by
    rcases lt_trichotomy j i with h | h | h
    · simp [h, not_lt.mpr h.le, hsym i j]
    · subst j; simp [hdiag]
    · simp [h, not_lt.mpr h.le]
  calc
    _ = ∑' i, ∑' j,
        ((if j < i then f j i else 0) + (if i < j then f i j else 0)) := by
      apply tsum_congr; intro i; apply tsum_congr; exact hsplit i
    _ = (∑' i, ∑' j, if j < i then f j i else 0) +
        (∑' i, ∑' j, if i < j then f i j else 0) := by
      simp_rw [ENNReal.tsum_add]
    _ = (∑' i, ∑' j, if j < i then f j i else 0) +
        (∑' j, ∑' i, if i < j then f i j else 0) := by
      rw [ENNReal.tsum_comm (f := fun i j => if i < j then f i j else 0)]
    _ = _ := by simp_rw [hfinite]

/-- Integrating the atomic square bound gives finite energy, using the recursive pair bound. -/
theorem e2_dense_energy_proof :
    E2AtomicSquareBoundStatement → E2DenseWeightStatement → E2DenseEnergyStatement := by
  intro hatomic hweights n hn k hk hkn z
  rcases hweights n k z with ⟨hpos, _hweight, hpair⟩
  let w := denseAtomWeight k z
  let f : ℕ → ℕ → ℝ≥0∞ := fun i j =>
    ENNReal.ofReal (w i * w j * (dist (z i) (z j) ^ k)⁻¹)
  have hw (i : ℕ) : 0 ≤ w i := (hpos i).le
  have hgeom : (∑' j : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹)) = 1 := by
    have hterm (j : ℕ) :
        ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹) = ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)]
      rw [← ENNReal.inv_pow]
      norm_num
    simp_rw [hterm]
    rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  have htri : (∑' j, ∑ i ∈ Finset.range j, f i j) ≤ 1 := by
    calc
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (j + 1))⁻¹) := by
        apply ENNReal.tsum_le_tsum
        intro j
        dsimp [f]
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · exact ENNReal.ofReal_le_ofReal (hpair j)
        · intro i hi
          exact mul_nonneg (mul_nonneg (hw i) (hw j))
            (inv_nonneg.mpr (pow_nonneg dist_nonneg _))
      _ = 1 := hgeom
  have hdouble : (∑' i, ∑' j, f i j) < ⊤ := by
    rw [triangular_tsum f]
    · exact (add_le_add htri htri).trans_lt (by norm_num)
    · intro i j
      dsimp [f]
      rw [dist_comm (z i) (z j)]
      congr 1
      ring
    · intro i
      simp [f, Nat.ne_of_gt hk]
  have hbound : (∫⁻ x, squareEnergy (denseAtomMeasure k z) k .mixed 2 x
      ∂(denseAtomMeasure k z)) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 2)) * (∑' i, ∑' j, f i j) := by
    simp only [denseAtomMeasure, lintegral_sum_measure, lintegral_smul_measure,
      lintegral_dirac, smul_eq_mul]
    calc
      _ ≤ ∑' i, ENNReal.ofReal (w i) *
          (ENNReal.ofReal (1 / ((k : ℝ) + 2)) *
            ∑' j, ENNReal.ofReal (w j * (dist (z i) (z j) ^ k)⁻¹)) := by
        apply ENNReal.tsum_le_tsum
        intro i
        exact mul_le_mul' le_rfl (hatomic n k hn hk hkn z w hw (z i))
      _ = _ := by
        simp_rw [mul_left_comm (ENNReal.ofReal (w _)), ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        congr 1
        rw [← ENNReal.ofReal_mul (hw i)]
        dsimp [f]
        congr 1
        ring
  exact (setLIntegral_le_lintegral _ _).trans_lt
    (hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdouble))

end ParabolicRectifiability.Examples
