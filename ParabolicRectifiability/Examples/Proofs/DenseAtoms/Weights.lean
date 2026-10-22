import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements

/-! # The dense-atom weights

The recursively defined weights are positive, bounded by `2^{-(j+1)}`, and satisfy the
recursion bound `w_j Σ_{i<j} w_i d_{ij}^{-k} ≤ 2^{-(j+1)}`.
-/

noncomputable section

namespace ParabolicRectifiability.Examples

private theorem e2_dense_weight_sum_nonneg {n k : ℕ} {z : ℕ → Space n}
    (hpos : ∀ j, 0 < denseAtomWeight k z j) (j : ℕ) :
    0 ≤ ∑ i : Fin j, denseAtomWeight k z i * (dist (z i) (z j) ^ k)⁻¹ := by
  refine Finset.sum_nonneg fun i _ => ?_
  exact mul_nonneg (le_of_lt (hpos i))
    (inv_nonneg.mpr (pow_nonneg (dist_nonneg) k))

/-- The recursive weights satisfy all three weight bounds. -/
theorem e2_dense_weights_proof : E2DenseWeightStatement := by
  intro n k z
  have hpos : ∀ j, 0 < denseAtomWeight k z j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        rw [denseAtomWeight]
        apply div_pos
        · exact inv_pos.mpr (by positivity)
        · have hsum :
              0 ≤ ∑ i : Fin j, denseAtomWeight k z i * (dist (z i) (z j) ^ k)⁻¹ := by
            refine Finset.sum_nonneg fun i _ => ?_
            exact mul_nonneg (le_of_lt (ih i i.isLt))
              (inv_nonneg.mpr (pow_nonneg (dist_nonneg) k))
          linarith
  refine ⟨hpos, ?_, ?_⟩
  · intro j
    have hsum :
        0 ≤ ∑ i : Fin j, denseAtomWeight k z i * (dist (z i) (z j) ^ k)⁻¹ :=
      e2_dense_weight_sum_nonneg hpos j
    rw [denseAtomWeight]
    exact div_le_self (le_of_lt (inv_pos.mpr (by positivity))) (by linarith)
  · intro j
    let S : ℝ := ∑ i : Fin j, denseAtomWeight k z i * (dist (z i) (z j) ^ k)⁻¹
    have hsum : 0 ≤ S := by
      dsimp [S]
      exact e2_dense_weight_sum_nonneg hpos j
    have hden : 0 < 1 + S := by linarith
    have hrec : denseAtomWeight k z j * (1 + S) = ((2 : ℝ) ^ (j + 1))⁻¹ := by
      rw [denseAtomWeight]
      simpa [S] using
        (div_mul_cancel₀ (((2 : ℝ) ^ (j + 1))⁻¹) hden.ne')
    have hpair :
        (∑ i ∈ Finset.range j,
          denseAtomWeight k z i * denseAtomWeight k z j * (dist (z i) (z j) ^ k)⁻¹) =
          denseAtomWeight k z j *
            (∑ i : Fin j, denseAtomWeight k z i * (dist (z i) (z j) ^ k)⁻¹) := by
      rw [← Fin.sum_univ_eq_sum_range]
      calc
        (∑ i : Fin j,
          denseAtomWeight k z i * denseAtomWeight k z j *
            (dist (z i) (z j) ^ k)⁻¹) =
            ∑ i : Fin j,
              denseAtomWeight k z j *
                (denseAtomWeight k z i * (dist (z i) (z j) ^ k)⁻¹) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = denseAtomWeight k z j *
              (∑ i : Fin j, denseAtomWeight k z i *
                (dist (z i) (z j) ^ k)⁻¹) := by
          rw [Finset.mul_sum]
    have hpair' :
        (∑ i ∈ Finset.range j,
          denseAtomWeight k z i * denseAtomWeight k z j * (dist (z i) (z j) ^ k)⁻¹) =
          denseAtomWeight k z j * S := by
      simpa [S] using hpair
    calc
      (∑ i ∈ Finset.range j,
        denseAtomWeight k z i * denseAtomWeight k z j * (dist (z i) (z j) ^ k)⁻¹) =
          denseAtomWeight k z j * S := hpair'
      _ ≤ denseAtomWeight k z j * (1 + S) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (hpos j))
          linarith
      _ = ((2 : ℝ) ^ (j + 1))⁻¹ := hrec

end ParabolicRectifiability.Examples
