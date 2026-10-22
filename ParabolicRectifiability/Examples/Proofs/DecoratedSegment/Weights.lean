import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements
import Mathlib.Analysis.SumIntegralComparisons

/-! # The decorated-segment weights

The finite integral test bounds the sum of the weights from index one by
`1/100`. Its primitive is `-1 / (100 * (1 + log x))` on `[1, ∞)`.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

private theorem sapDelta_bounds (j : ℕ) :
    0 < e2_sapDelta j ∧ e2_sapDelta j < 1 / 4 := by
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  have hlog : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg hj
  have hsq : 1 ≤ (1 + Real.log ((j : ℝ) + 1)) ^ 2 := by nlinarith
  have hden : 100 ≤ 100 * ((j : ℝ) + 1) * (1 + Real.log ((j : ℝ) + 1)) ^ 2 := by nlinarith
  unfold e2_sapDelta
  refine ⟨one_div_pos.2 (by linarith), ?_⟩
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

private def sapWeightFunction (x : ℝ) : ℝ :=
  1 / (100 * x * (1 + Real.log x) ^ 2)

private theorem sapWeightFunction_antitone : AntitoneOn sapWeightFunction (Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hlogx := Real.log_nonneg hx
  have hlogy := Real.log_nonneg hy
  have hlog := Real.log_le_log hx0 hxy
  apply one_div_le_one_div_of_le (by positivity)
  have hsq : (1 + Real.log x) ^ 2 ≤ (1 + Real.log y) ^ 2 := by nlinarith
  exact mul_le_mul (mul_le_mul_of_nonneg_left hxy (by norm_num)) hsq
    (sq_nonneg _) (by positivity)

private theorem sapWeightFunction_primitive (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt (fun t : ℝ => -1 / (100 * (1 + Real.log t))) (sapWeightFunction x) x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hne : 100 * (1 + Real.log x) ≠ 0 := by positivity
  convert (((Real.hasDerivAt_log hx0.ne').const_add 1).const_mul 100).inv hne |>.const_mul (-1) using 1
  · ext t
    simp [div_eq_mul_inv]
  · dsimp [sapWeightFunction]
    field_simp [hx0.ne', show 1 + Real.log x ≠ 0 by positivity]

private theorem sapDelta_sum_range_le (n : ℕ) :
    ∑ j ∈ Finset.range n, e2_sapDelta (j + 1) ≤ 1 / 100 := by
  have hn : (1 : ℝ) ≤ 1 + n := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have ha : AntitoneOn sapWeightFunction (Icc 1 (1 + n)) :=
    sapWeightFunction_antitone.mono Icc_subset_Ici_self
  have hi : IntervalIntegrable sapWeightFunction volume 1 (1 + n) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hn).2
      (ha.integrableOn_isCompact isCompact_Icc)
  have hprim := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => sapWeightFunction_primitive x ((uIcc_of_le hn ▸ hx).1)) hi
  have hsum := ha.sum_le_integral
  have heq : (∑ j ∈ Finset.range n, e2_sapDelta (j + 1)) =
      ∑ j ∈ Finset.range n, sapWeightFunction (1 + ↑(j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [e2_sapDelta, sapWeightFunction, Nat.cast_add, add_comm]
  rw [heq]
  refine hsum.trans ?_
  rw [hprim]
  have hlog : 0 ≤ Real.log (1 + (n : ℝ)) := Real.log_nonneg hn
  have hp : 0 ≤ 1 / (100 * (1 + Real.log (1 + (n : ℝ)))) := by positivity
  simp only [Real.log_one, add_zero, mul_one, neg_div] 
  linarith

/-- The weight bounds `E2sapWeights`: positive small weights and summable tail
with total mass at most `1/100`. -/
theorem e2_sap_weights_proof : E2sapWeights := by
  refine ⟨sapDelta_bounds, ?_, ?_⟩
  · exact summable_of_sum_range_le (fun j => (sapDelta_bounds (j + 1)).1.le)
      sapDelta_sum_range_le
  · exact Real.tsum_le_of_sum_range_le (fun j => (sapDelta_bounds (j + 1)).1.le)
      sapDelta_sum_range_le

end ParabolicRectifiability.Examples
