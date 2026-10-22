import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Bounds for the above-two segment labels

The supplied weight premise gives positive child lengths and δ < 1/4.
For every valid label we preserve b + (4/255)L ≤ 4/255: since N ≥ 64,
the height increment is at most L/64 and the new length is at most L/256.
The extreme coefficients satisfy 1/64 + (4/255)/256 = 4/255.
-/

noncomputable section

namespace ParabolicRectifiability.Examples

private theorem sap_child_inv (hW : E2sapWeights) (j m : ℕ) (hj : 1 ≤ j) (hm : m < e2_sapN j) (a L b : ℝ)
    (hL : 0 < L) (ha : 0 ≤ a) (hr : a + L ≤ 1) (hb : 0 ≤ b)
    (hinv : b + 4 / 255 * L ≤ 4 / 255) :
    0 < (e2_sapChild (a, L, b) j m).2.1 ∧ 0 ≤ (e2_sapChild (a, L, b) j m).1 ∧
      (e2_sapChild (a, L, b) j m).1 + (e2_sapChild (a, L, b) j m).2.1 ≤ 1 ∧
      0 ≤ (e2_sapChild (a, L, b) j m).2.2 ∧
      (e2_sapChild (a, L, b) j m).2.2 + 4 / 255 * (e2_sapChild (a, L, b) j m).2.1 ≤ 4 / 255 := by
  obtain ⟨hd0, hd1⟩ := hW.1 j
  have hN64 : (64 : ℝ) ≤ (e2_sapN j : ℝ) := by
    have : 64 ≤ e2_sapN j := by
      unfold e2_sapN
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ 8 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have hmN : (m : ℝ) + 1 ≤ (e2_sapN j : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (e2_sapN j : ℝ) := ⟨_, rfl⟩
  rw [← hNdef] at hN64 hmN
  have hNpos : 0 < N := by linarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = L / N := ⟨_, rfl⟩
  have hhpos : 0 < h := by rw [hh]; exact div_pos hL hNpos
  have hNh : N * h = L := by rw [hh]; field_simp
  have h64 : 64 * h ≤ L := by nlinarith
  have hdh : e2_sapDelta j * h ≤ 1 / 4 * h := mul_le_mul_of_nonneg_right hd1.le hhpos.le
  have hmh : (m : ℝ) * h ≥ 0 := mul_nonneg hm0 hhpos.le
  have hmh2 : ((m : ℝ) + 1) * h ≤ N * h := mul_le_mul_of_nonneg_right hmN hhpos.le
  unfold e2_sapChild
  simp only []
  rw [← hNdef, ← hh]
  refine ⟨mul_pos hd0 hhpos, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · linarith
  · nlinarith

private theorem sap_seg_inv (hW : E2sapWeights) : ∀ l : List (ℕ × ℕ), e2_sapValid l →
    0 < (e2_sapSeg l).2.1 ∧ 0 ≤ (e2_sapSeg l).1 ∧ (e2_sapSeg l).1 + (e2_sapSeg l).2.1 ≤ 1 ∧
      0 ≤ (e2_sapSeg l).2.2 ∧ (e2_sapSeg l).2.2 + 4 / 255 * (e2_sapSeg l).2.1 ≤ 4 / 255
  | [], _ => by simp [e2_sapSeg]
  | q :: l, hv => by
      have hl : e2_sapValid l := fun r hr => hv r (by simp [hr])
      have hq := hv q (by simp)
      obtain ⟨h1, h2, h3, h4, h5⟩ := sap_seg_inv hW l hl
      simp only [e2_sapSeg]
      exact sap_child_inv hW q.1 q.2 hq.1 hq.2 (e2_sapSeg l).1 (e2_sapSeg l).2.1 (e2_sapSeg l).2.2
        h1 h2 h3 h4 h5

/-- Every valid coded segment is nondegenerate and lies in the unit square. -/
theorem e2_sap_labelBounds_proof (hW : E2sapWeights) : E2sapLabelBounds := by
  intro n hn
  obtain ⟨h1, h2, h3, h4, h5⟩ := sap_seg_inv hW (e2_sapLabel n) hn
  simp only [e2_sapLeft, e2_sapRight, e2_sapLength, e2_sapHeight]
  refine ⟨by linarith, h2, h3, h4, by linarith⟩


end ParabolicRectifiability.Examples
