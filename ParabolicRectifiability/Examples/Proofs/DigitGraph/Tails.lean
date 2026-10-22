import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Summability and tail bounds for the below-two digit heights

The grid identities give the exact successive-height ratio. A geometric bound with
ratio `1/2` controls every shifted sum; the stronger exact ratio then gives the
scale-dependent tail bounds and the squared-tail estimate.
-/

noncomputable section
open Filter Topology
namespace ParabolicRectifiability.Examples

private theorem e2_sb_tails_ratio (hG : E2sbGrid) (j : ℕ) (hj : 1 ≤ j) :
    e2_sbH (j + 1) = e2_sbDelta j * e2_sbH j / 2 ^ (j + 31) := by
  have hp := hG.2.2.2.2.2.2.1 j hj
  rw [e2_sbH, hp, e2_sbPeriod, e2_sbDelta]
  have hn : (j : ℝ) + 1 ≠ 0 := by positivity
  have he : j + 31 = (j + 21) + 10 := by omega
  rw [he, pow_add]
  field_simp; ring

private theorem e2_sb_tails_half (hG : E2sbGrid) (j : ℕ) :
    e2_sbH (j + 1) ≤ e2_sbH j / 2 := by
  rcases j with _ | j
  · norm_num [e2_sbH, e2_sbEll]
  · have hd := hG.2.2.2.2.2.2.2.2 (j + 1) (by omega)
    rw [e2_sb_tails_ratio hG (j + 1) (by omega)]
    have hpow : (1 : ℝ) ≤ 2 ^ (j + 1 + 31) := one_le_pow₀ (by norm_num)
    have hpos := (hG.2.1 (j + 1)).le
    calc
      e2_sbDelta (j + 1) * e2_sbH (j + 1) / 2 ^ (j + 1 + 31)
          ≤ e2_sbDelta (j + 1) * e2_sbH (j + 1) :=
        div_le_self (mul_nonneg hd.1.le hpos) hpow
      _ ≤ e2_sbH (j + 1) / 2 := by nlinarith [mul_le_mul_of_nonneg_right hd.2 hpos]

private theorem e2_sb_tails_geometric (hG : E2sbGrid) (k i : ℕ) :
    e2_sbH (k + i) ≤ e2_sbH k * (1 / 2 : ℝ) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hs := e2_sb_tails_half hG (k + i)
    rw [show k + (i + 1) = (k + i) + 1 by omega]
    rw [pow_succ]
    nlinarith

/-- Summability and tail bounds of the digit heights, with the grid supplied as a hypothesis. -/
theorem e2_sb_tails_proof (hG : E2sbGrid) : E2sbTails := by
  have hnonneg : ∀ j, 0 ≤ e2_sbH j := fun j => (hG.2.1 j).le
  have hsum : Summable e2_sbH := by
    apply (summable_geometric_two.mul_left (e2_sbH 0)).of_nonneg_of_le hnonneg
    intro i
    simpa using e2_sb_tails_geometric hG 0 i
  have htail0 : ∀ j, 0 ≤ e2_sbTail j := fun j => tsum_nonneg (fun _ => hnonneg _)
  have htail : ∀ j, e2_sbTail j ≤ 2 * e2_sbH (j + 1) := by
    intro j
    have hs : Summable (fun i => e2_sbH (j + 1 + i)) := by
      simpa [Nat.add_comm] using (summable_nat_add_iff (j + 1)).2 hsum
    calc
      e2_sbTail j ≤ ∑' i : ℕ, e2_sbH (j + 1) * (1 / 2 : ℝ) ^ i :=
        hs.tsum_le_tsum (e2_sb_tails_geometric hG (j + 1))
          (summable_geometric_two.mul_left _)
      _ = 2 * e2_sbH (j + 1) := by rw [tsum_mul_left, tsum_geometric_two]; ring
  have hscale : ∀ j, 1 ≤ j →
      e2_sbTail j ≤ e2_sbDelta j * e2_sbH j / 2 ^ (j + 30) := by
    intro j hj
    have hr := e2_sb_tails_ratio hG j hj
    have he : j + 31 = (j + 30) + 1 := by omega
    have ht := htail j
    rw [hr, he, pow_succ] at ht
    convert ht using 1; field_simp
  refine ⟨hsum, fun j hj => (e2_sb_tails_ratio hG j hj).le, htail0,
    fun j _ => htail j, ?_, hscale, ?_, ?_, hsum.tendsto_atTop_zero⟩
  · intro j _
    have ht := htail j
    rw [e2_sbH] at ht
    have he : j + 21 = (j + 20) + 1 := by omega
    rw [he, pow_succ] at ht
    convert ht using 1; field_simp
  · intro j hj
    have hd := hG.2.2.2.2.2.2.2.2 j hj
    have hh := hnonneg j
    have hp : (8 : ℝ) ≤ 2 ^ (j + 30) := by
      calc
        (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
        _ ≤ 2 ^ (j + 30) := pow_le_pow_right₀ (by norm_num) (by omega)
    have ht : e2_sbTail j ≤ e2_sbDelta j * e2_sbH j / 8 :=
      (hscale j hj).trans (div_le_div_of_nonneg_left (mul_nonneg hd.1.le hh) (by norm_num) hp)
    have hsmall : e2_sbTail j ≤ e2_sbH j / 8 := by
      nlinarith [mul_le_mul_of_nonneg_right hd.2 hh]
    have hm := mul_le_mul ht hsmall (htail0 j) (div_nonneg (mul_nonneg hd.1.le hh) (by norm_num))
    nlinarith [mul_nonneg hd.1.le (sq_nonneg (e2_sbH j))]
  · apply strictAnti_nat_of_succ_lt
    intro j
    exact (e2_sb_tails_half hG j).trans_lt (by nlinarith [hG.2.1 j])

end ParabolicRectifiability.Examples
