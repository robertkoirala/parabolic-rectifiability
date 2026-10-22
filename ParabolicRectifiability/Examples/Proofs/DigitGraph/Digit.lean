import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # Digit coding and height separation

Coding on the nested grids and separation of the digit heights (`e2_sb_digit_proof`): the
bits `b_1, …, b_j` are constant on each generation-`j` interval, the height remainder
`y(x) - Y_j(x)` lies in `[0, η_j]`, and heights closer than `h_j/2` share their first `j` bits. -/
noncomputable section
open MeasureTheory Set Filter Topology
namespace ParabolicRectifiability.Examples

private lemma e2_sb_digit_bit_values (j : ℕ) (x : ℝ) :
    e2_sbBit j x = 0 ∨ e2_sbBit j x = 1 := by
  by_cases hx : x ∈ e2_sbMarked j
  · exact Or.inr (by simp [e2_sbBit, hx])
  · exact Or.inl (by simp [e2_sbBit, hx])

private lemma e2_sb_digit_bit_bounds (j : ℕ) (x : ℝ) :
    0 ≤ e2_sbBit j x ∧ e2_sbBit j x ≤ 1 := by
  rcases e2_sb_digit_bit_values j x with h | h <;> simp [h]

private lemma e2_sb_digit_grid (hG : E2sbGrid) :
    ∀ j i : ℕ, 1 ≤ i → i ≤ j → ∀ (k : ℤ) (x y : ℝ),
      x ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j) →
      y ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j) →
      e2_sbBit i x = e2_sbBit i y := by
  intro j i _ hij k x y hx hy
  obtain ⟨c, hc⟩ := hG.2.2.2.1 i j hij
  have hfloor (z : ℝ) (hz : z ∈ Ico ((k : ℝ) * e2_sbEll j)
      (((k : ℝ) + 1) * e2_sbEll j)) : ⌊z / e2_sbEll j⌋ = k :=
    Int.floor_eq_iff.mpr ⟨(le_div_iff₀ (hG.1 j)).mpr hz.1,
      (div_lt_iff₀ (hG.1 j)).mpr hz.2⟩
  have hcoarse (z : ℝ) : ⌊z / e2_sbEll i⌋ = ⌊z / e2_sbEll j⌋ / (c : ℤ) := by
    rw [hc, div_mul_eq_div_div_swap, Int.floor_div_natCast]
  have heq : ⌊x / e2_sbEll i⌋ = ⌊y / e2_sbEll i⌋ := by
    rw [hcoarse, hcoarse, hfloor x hx, hfloor y hy]
  have hm : x ∈ e2_sbMarked i ↔ y ∈ e2_sbMarked i := by
    change ((i + 1 : ℕ) : ℤ) ∣ ⌊x / e2_sbEll i⌋ ↔
      ((i + 1 : ℕ) : ℤ) ∣ ⌊y / e2_sbEll i⌋
    rw [heq]
  by_cases hxM : x ∈ e2_sbMarked i
  · simp [e2_sbBit, hxM, hm.mp hxM]
  · have hyM : y ∉ e2_sbMarked i := fun hyM => hxM (hm.mpr hyM)
    simp [e2_sbBit, hxM, hyM]

private lemma e2_sb_digit_summable (hG : E2sbGrid) (hT : E2sbTails) (x : ℝ) :
    Summable (fun i : ℕ => e2_sbH (i + 1) * e2_sbBit (i + 1) x) := by
  apply Summable.of_norm_bounded ((summable_nat_add_iff 1).2 hT.1)
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG.2.1 _).le
    (e2_sb_digit_bit_bounds _ _).1)]
  exact mul_le_of_le_one_right (hG.2.1 _).le (e2_sb_digit_bit_bounds _ _).2

private lemma e2_sb_digit_tail (hG : E2sbGrid) (hT : E2sbTails) (j : ℕ) (x : ℝ) :
    0 ≤ e2_sbHeight x - e2_sbOldHeight j x ∧
      e2_sbHeight x - e2_sbOldHeight j x ≤ e2_sbTail j := by
  have hs := e2_sb_digit_summable hG hT x
  have he : e2_sbHeight x - e2_sbOldHeight j x =
      ∑' i : ℕ, e2_sbH (j + 1 + i) * e2_sbBit (j + 1 + i) x := by
    have ht := hs.sum_add_tsum_nat_add j
    simpa only [e2_sbHeight, e2_sbOldHeight, add_sub_cancel_left,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (show (∑' i : ℕ, e2_sbH (i + 1) * e2_sbBit (i + 1) x) -
        (∑ i ∈ Finset.range j, e2_sbH (i + 1) * e2_sbBit (i + 1) x) =
        ∑' i : ℕ, e2_sbH (i + j + 1) * e2_sbBit (i + j + 1) x by linarith [ht])
  rw [he]
  constructor
  · exact tsum_nonneg (fun i => mul_nonneg (hG.2.1 _).le (e2_sb_digit_bit_bounds _ _).1)
  · have hsTail : Summable (fun i : ℕ =>
        e2_sbH (j + 1 + i) * e2_sbBit (j + 1 + i) x) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (summable_nat_add_iff j).2 hs
    have hH : Summable (fun i : ℕ => e2_sbH (j + 1 + i)) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff (j + 1)).2 hT.1
    exact hsTail.tsum_le_tsum (fun i =>
      mul_le_of_le_one_right (hG.2.1 _).le (e2_sb_digit_bit_bounds _ _).2) hH

private lemma e2_sb_digit_tail_lt_half (hG : E2sbGrid) (hT : E2sbTails)
    (j : ℕ) (hj : 1 ≤ j) : e2_sbTail j < e2_sbH j / 2 := by
  have hb := hT.2.2.2.2.2.1 j hj
  have hd := (hG.2.2.2.2.2.2.2.2 j hj).2
  have hp : (2 : ℝ) ≤ 2 ^ (j + 30) := by
    calc
      (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 30) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := hG.2.1 j
  have hb' := (le_div_iff₀ (show (0 : ℝ) < 2 ^ (j + 30) by positivity)).mp hb
  have ht := hT.2.2.1 j
  have hdH := mul_le_mul_of_nonneg_right hd hh.le
  have hpT := mul_nonneg (sub_nonneg.mpr hp) ht
  nlinarith

private lemma e2_sb_digit_separation (hG : E2sbGrid) (hT : E2sbTails) :
    ∀ (j : ℕ) (x y : ℝ), |e2_sbHeight x - e2_sbHeight y| < e2_sbH j / 2 →
      ∀ i : ℕ, 1 ≤ i → i ≤ j → e2_sbBit i x = e2_sbBit i y := by
  intro j
  induction j with
  | zero => intros; omega
  | succ j ih =>
    intro x y hxy
    have hanti := hT.2.2.2.2.2.2.2.1
    have hprev : ∀ i : ℕ, 1 ≤ i → i ≤ j → e2_sbBit i x = e2_sbBit i y := by
      apply ih x y
      exact hxy.trans_le (div_le_div_of_nonneg_right ((hanti (Nat.lt_succ_self j)).le) (by norm_num))
    have hold : e2_sbOldHeight j x = e2_sbOldHeight j y := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hprev (k + 1) (by omega) (by have := Finset.mem_range.mp hk; omega)]
    have hnext : e2_sbBit (j + 1) x = e2_sbBit (j + 1) y := by
      have hx := e2_sb_digit_tail hG hT (j + 1) x
      have hy := e2_sb_digit_tail hG hT (j + 1) y
      have ht := e2_sb_digit_tail_lt_half hG hT (j + 1) (by omega)
      have hex (z : ℝ) : e2_sbOldHeight (j + 1) z =
          e2_sbOldHeight j z + e2_sbH (j + 1) * e2_sbBit (j + 1) z := by
        exact Finset.sum_range_succ _ _
      rw [hex x] at hx
      rw [hex y, ← hold] at hy
      have hab := abs_lt.mp hxy
      rcases e2_sb_digit_bit_values (j + 1) x with hxbit | hxbit <;>
        rcases e2_sb_digit_bit_values (j + 1) y with hybit | hybit
      · exact hxbit.trans hybit.symm
      · simp only [hxbit, mul_zero] at hx
        simp only [hybit, mul_one] at hy
        linarith
      · simp only [hxbit, mul_one] at hx
        simp only [hybit, mul_zero] at hy
        linarith
      · exact hxbit.trans hybit.symm
    intro i hi hij
    by_cases heq : i = j + 1
    · simpa [heq] using hnext
    · exact hprev i hi (by omega)

/-- The globally defined bits are constant on each nested grid interval, their height
remainders are bounded by the positive tail, and distinct prefixes have separated heights. -/
theorem e2_sb_digit_proof (hG : E2sbGrid) (hT : E2sbTails) : E2sbDigit := by
  exact ⟨e2_sb_digit_grid hG, e2_sb_digit_tail hG hT, e2_sb_digit_separation hG hT⟩

end ParabolicRectifiability.Examples
