import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # Plateau decomposition for the lacunary cosine series

The finite low-frequency part changes by at most `w_j / 100` on the closed
period window. The remaining tail has absolute value at most `w_j / 999`.
The weighted summability and tail estimate are precisely the hypothesis
`E2LacunaryWeightStatement`.
-/

noncomputable section

namespace ParabolicRectifiability.Examples

/-- The plateau error estimate, from the weighted summability and tail estimate
`E2LacunaryWeightStatement`. -/
theorem e2_plateau_error_proof : E2LacunaryWeightStatement → E2PlateauErrorStatement := by
  intro hweight ε a N hε hd j t s hst
  obtain ⟨hwpos, _, _, hwsum, hwtail⟩ := hweight a N hd
  let w : ℕ → ℝ := fun i => a i / Real.sqrt (N i)
  let u : ℝ → ℕ → ℝ := fun x i => w i * Real.cos (N i * x)
  have hw : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  have huabs (x : ℝ) (i : ℕ) : |u x i| ≤ w i := by
    dsimp [u]
    rw [abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_of_le_one_right (hw i) (Real.abs_cos_le_one _)
  have husum (x : ℝ) : Summable (u x) :=
    hwsum.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using huabs x i)
  have htailw : Summable (fun i => w (j + 1 + i)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff (j + 1)).2 hwsum
  have htailabs : Summable (fun i => |u s (j + 1 + i)|) := by
    refine htailw.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => huabs _ _)
  have htail : |∑' i, u s (j + 1 + i)| ≤ w j / 999 := by
    calc
      |∑' i, u s (j + 1 + i)| ≤ ∑' i, |u s (j + 1 + i)| := by
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun i : ℕ => u s (j + 1 + i))
            (by simpa only [Real.norm_eq_abs] using htailabs)
      _ ≤ ∑' i, w (j + 1 + i) := htailabs.tsum_le_tsum (fun i => huabs _ _) htailw
      _ ≤ w j / 999 := hwtail j
  have hterm (i : ℕ) :
      |u s i - u t i| ≤ (a i * Real.sqrt (N i)) * (Real.pi / N j) := by
    have hi : 0 ≤ (N i : ℝ) := Nat.cast_nonneg _
    have hwi : w i * (N i : ℝ) = a i * Real.sqrt (N i) := by
      dsimp [w]
      calc
        a i / Real.sqrt (N i) * (N i : ℝ) = a i * ((N i : ℝ) / Real.sqrt (N i)) := by ring
        _ = a i * Real.sqrt (N i) := by rw [Real.div_sqrt]
    calc
      |u s i - u t i| = w i * |Real.cos (N i * s) - Real.cos (N i * t)| := by
        dsimp [u]
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw i)]
      _ ≤ w i * |(N i : ℝ) * s - N i * t| :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (hw i)
      _ = (w i * N i) * |s - t| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hi, mul_assoc]
      _ ≤ (w i * N i) * (Real.pi / N j) :=
        mul_le_mul_of_nonneg_left hst (mul_nonneg (hw i) hi)
      _ = (a i * Real.sqrt (N i)) * (Real.pi / N j) := by rw [hwi]
  have hNj : 0 < (N j : ℝ) := Nat.cast_pos.mpr (hd.frequency_pos j)
  have hsqrt : 0 < Real.sqrt (N j) := Real.sqrt_pos.mpr hNj
  have hhead : |∑ i ∈ Finset.range j, (u s i - u t i)| ≤ w j / 100 := by
    calc
      |∑ i ∈ Finset.range j, (u s i - u t i)| ≤
          ∑ i ∈ Finset.range j, |u s i - u t i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range j, (a i * Real.sqrt (N i)) * (Real.pi / N j) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Real.pi / Real.sqrt (N j) *
          ∑ i ∈ Finset.range j, a i * Real.sqrt (N i)) / Real.sqrt (N j) := by
        rw [← Finset.sum_mul]
        calc
          _ = (Real.pi * ∑ i ∈ Finset.range j, a i * Real.sqrt (N i)) /
              (Real.sqrt (N j) * Real.sqrt (N j)) := by
            rw [Real.mul_self_sqrt hNj.le]
            ring
          _ = _ := by ring
      _ ≤ (a j / 100) / Real.sqrt (N j) :=
        div_le_div_of_nonneg_right (hd.low_frequency j) hsqrt.le
      _ = w j / 100 := by dsimp [w]; ring
  have hsplit : (∑' i, u s i) =
      (∑ i ∈ Finset.range j, u s i) + u s j + ∑' i, u s (j + 1 + i) := by
    have hh := (husum s).sum_add_tsum_nat_add (j + 1)
    rw [Finset.sum_range_succ] at hh
    simpa only [Nat.add_comm] using hh.symm
  have hid : lacunaryFunction ε a N s - e2_plateauCenter ε a N j t -
      ε * (a j / Real.sqrt (N j)) * Real.cos (N j * s) =
      ε * ((∑ i ∈ Finset.range j, (u s i - u t i)) + ∑' i, u s (j + 1 + i)) := by
    change ε * (∑' i, u s i) - ε * (∑ i ∈ Finset.range j, u t i) - ε * w j * Real.cos (N j * s) = _
    rw [hsplit, Finset.sum_sub_distrib]
    dsimp [u]
    ring
  rw [hid, abs_mul, abs_of_nonneg hε]
  calc
    ε * |(∑ i ∈ Finset.range j, (u s i - u t i)) + ∑' i, u s (j + 1 + i)| ≤
        ε * (|∑ i ∈ Finset.range j, (u s i - u t i)| + |∑' i, u s (j + 1 + i)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hε
    _ ≤ ε * (w j / 100 + w j / 999) :=
      mul_le_mul_of_nonneg_left (add_le_add hhead htail) hε
    _ ≤ ε * (a j / Real.sqrt (N j)) / 50 := by
      change ε * (w j / 100 + w j / 999) ≤ ε * w j / 50
      nlinarith [mul_nonneg hε (hw j)]

end ParabolicRectifiability.Examples
