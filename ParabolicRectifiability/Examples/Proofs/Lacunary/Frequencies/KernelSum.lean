import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Summing kernels on a lacunary sequence of scales

A first scale below the testing radius separates two geometric series. Reading
scales before that index backwards gives the same ratio as the forward tail.
-/

noncomputable section

namespace ParabolicRectifiability.Examples

/-- Iterating quarter decay from any starting scale. -/
private lemma e2_quarterDecay_add (b : ℕ → ℝ)
    (h : ∀ j, b (j + 1) ≤ b j / 4) (m k : ℕ) :
    b (m + k) ≤ b m * (1 / 4 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      b (m + (k + 1)) ≤ b (m + k) / 4 := by simpa [Nat.add_assoc] using h (m + k)
      _ ≤ (b m * (1 / 4 : ℝ) ^ k) / 4 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = b m * (1 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-- The lacunary scale kernels have uniformly bounded total mass. -/
theorem e2_kernelSum_le_proof : E2KernelSumStatement := by
  classical
  intro b hb hd r hr
  have hgeom : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgeom_sum : ∑' j : ℕ, (1 / 4 : ℝ) ^ j = 4 / 3 := by
    rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)]
    norm_num
  have hbound (j : ℕ) : b j ≤ b 0 * (1 / 4 : ℝ) ^ j := by
    simpa using e2_quarterDecay_add b hd 0 j
  have hbsum : Summable b :=
    (hgeom.mul_left (b 0)).of_nonneg_of_le (fun j => (hb j).le) hbound
  have hnonneg (j : ℕ) : 0 ≤ e2_kernelAt (b j) r :=
    le_min (div_nonneg hr.le (hb j).le) (div_nonneg (hb j).le hr.le)
  have hsum : Summable (fun j => e2_kernelAt (b j) r) := by
    apply (hbsum.div_const r).of_nonneg_of_le hnonneg
    intro j
    exact min_le_right _ _
  refine ⟨hsum, ?_⟩
  have hex : ∃ j, b j < r :=
    (hbsum.tendsto_atTop_zero.eventually (gt_mem_nhds hr)).exists
  let N := Nat.find hex
  have hN : b N < r := Nat.find_spec hex
  have hpre (j : ℕ) (hj : j < N) : r ≤ b j :=
    le_of_not_gt (Nat.find_min hex hj)
  have htail (j : ℕ) : e2_kernelAt (b (j + N)) r ≤ (1 / 4 : ℝ) ^ j := by
    apply le_trans (min_le_right _ _)
    apply (div_le_iff₀ hr).2
    calc
      b (j + N) ≤ b N * (1 / 4 : ℝ) ^ j := by
        simpa [Nat.add_comm] using e2_quarterDecay_add b hd N j
      _ ≤ r * (1 / 4 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right hN.le (by positivity)
      _ = (1 / 4 : ℝ) ^ j * r := mul_comm _ _
  have htail_sum : ∑' j, e2_kernelAt (b (j + N)) r ≤ 4 / 3 := by
    rw [← hgeom_sum]
    exact Summable.tsum_le_tsum htail (hsum.comp_injective (add_left_injective N)) hgeom
  have hhead : ∑ j ∈ Finset.range N, e2_kernelAt (b j) r ≤ 4 / 3 := by
    by_cases hz : N = 0
    · simpa [hz] using (by norm_num : (0 : ℝ) ≤ 4 / 3)
    have hlast : r ≤ b (N - 1) := hpre _ (by omega)
    have hreverse (j : ℕ) (hj : j ∈ Finset.range N) :
        e2_kernelAt (b (N - 1 - j)) r ≤ (1 / 4 : ℝ) ^ j := by
      have hjN := Finset.mem_range.mp hj
      apply le_trans (min_le_left _ _)
      apply (div_le_iff₀ (hb _)).2
      calc
        r ≤ b (N - 1) := hlast
        _ ≤ b (N - 1 - j) * (1 / 4 : ℝ) ^ j := by
          have hh := e2_quarterDecay_add b hd (N - 1 - j) j
          simpa [show N - 1 - j + j = N - 1 by omega] using hh
        _ = (1 / 4 : ℝ) ^ j * b (N - 1 - j) := mul_comm _ _
    calc
      ∑ j ∈ Finset.range N, e2_kernelAt (b j) r =
          ∑ j ∈ Finset.range N, e2_kernelAt (b (N - 1 - j)) r := by
            symm
            exact Finset.sum_range_reflect (fun j : ℕ => e2_kernelAt (b j) r) N
      _ ≤ ∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j := Finset.sum_le_sum hreverse
      _ ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j :=
        hgeom.sum_le_tsum _ (fun j _ => by positivity)
      _ = 4 / 3 := hgeom_sum
  have hsplit := hsum.sum_add_tsum_nat_add N
  linarith

end ParabolicRectifiability.Examples
