import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Square summability of the logarithmic amplitudes

The amplitudes squared are a constant multiple of
`1 / ((j + 1) * log (j + 2)^2)`. Cauchy condensation turns this into a series
bounded by a constant multiple of `1 / (k + 1)^2`.
-/

noncomputable section

open Real

namespace ParabolicRectifiability.Examples

private def e2_logWeight (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * (Real.log ((n : ℝ) + 2)) ^ 2)

private theorem e2_logWeight_den_pos (n : ℕ) :
    0 < ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 2)) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have harg : (1 : ℝ) < (n : ℝ) + 2 := by linarith
  exact mul_pos (by positivity) (sq_pos_of_pos (Real.log_pos harg))

private theorem e2_logWeight_antitone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    e2_logWeight n ≤ e2_logWeight m := by
  unfold e2_logWeight
  apply one_div_le_one_div_of_le (e2_logWeight_den_pos m)
  have hmn1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hmn2 : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
    exact_mod_cast Nat.add_le_add_right hmn 2
  have hmarg : 0 < (m : ℝ) + 2 := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnarg : (1 : ℝ) < (n : ℝ) + 2 := by linarith
  have hlogm : 0 < Real.log ((m : ℝ) + 2) :=
    Real.log_pos (by linarith)
  have hlogn : 0 < Real.log ((n : ℝ) + 2) :=
    Real.log_pos hnarg
  have hlog : Real.log ((m : ℝ) + 2) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hmarg hmn2
  have hsq : (Real.log ((m : ℝ) + 2)) ^ 2 ≤ (Real.log ((n : ℝ) + 2)) ^ 2 := by
    nlinarith
  exact mul_le_mul hmn1 hsq (sq_nonneg _) (by positivity)

private theorem e2_condensed_logWeight_bound (k : ℕ) :
    (2 : ℝ) ^ k * e2_logWeight (2 ^ k) ≤
      (4 / (Real.log 2) ^ 2) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
  let q : ℝ := (2 : ℝ) ^ k
  let L : ℝ := Real.log (q + 2)
  let b : ℝ := (((k : ℝ) + 1) / 2) * Real.log 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : b ≤ L := by
    by_cases hk : k = 0
    · subst k
      have h23 : Real.log 2 ≤ Real.log 3 :=
        Real.log_le_log (by norm_num) (by norm_num)
      dsimp [b, L, q]
      norm_num
      linarith
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
      have hqeq : q = (2 : ℝ) ^ k := rfl
      have hlogq : Real.log q = (k : ℝ) * Real.log 2 := by
        rw [hqeq, Real.log_pow]
      have hqle : q ≤ q + 2 := by linarith
      have hlogle : Real.log q ≤ L := Real.log_le_log hq hqle
      have hkbound : ((k : ℝ) + 1) / 2 ≤ (k : ℝ) := by linarith
      calc
        b = (((k : ℝ) + 1) / 2) * Real.log 2 := rfl
        _ ≤ (k : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hkbound (le_of_lt hlog2)
        _ = Real.log q := hlogq.symm
        _ ≤ L := hlogle
  have hb : 0 < b := by dsimp [b]; positivity
  have hL : 0 < L := lt_of_lt_of_le hb hlog
  have hsq : b ^ 2 ≤ L ^ 2 := by nlinarith
  have hinv : (L ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) hsq
  have hratio : q / (q + 1) ≤ 1 := by
    apply (div_le_iff₀ (by linarith)).2
    nlinarith
  have heq : (2 : ℝ) ^ k * e2_logWeight (2 ^ k) =
      (q / (q + 1)) * (L ^ 2)⁻¹ := by
    dsimp [e2_logWeight, q, L]
    norm_cast
    field_simp
  have hb_sq : (b ^ 2)⁻¹ =
      (4 / (Real.log 2) ^ 2) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
    dsimp [b]
    field_simp [ne_of_gt hlog2]
    norm_num
  calc
    (2 : ℝ) ^ k * e2_logWeight (2 ^ k) = (q / (q + 1)) * (L ^ 2)⁻¹ := heq
    _ ≤ 1 * (L ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    _ ≤ 1 * (b ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = (4 / (Real.log 2) ^ 2) * (((k : ℝ) + 1) ^ 2)⁻¹ := by
      rw [one_mul, hb_sq]

private theorem e2_summable_logWeight : Summable e2_logWeight := by
  have hpow : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    exact (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have hshift : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
    simpa [Nat.cast_add] using
      (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).2 hpow
  have hmajor : Summable (fun k : ℕ =>
      (4 / (Real.log 2) ^ 2) * (((k : ℝ) + 1) ^ 2)⁻¹) :=
    hshift.mul_left (4 / (Real.log 2) ^ 2)
  have hcond_nonneg : ∀ k : ℕ, 0 ≤ (2 : ℝ) ^ k * e2_logWeight (2 ^ k) := by
    intro k
    exact mul_nonneg (by positivity)
      (le_of_lt (one_div_pos.mpr (e2_logWeight_den_pos (2 ^ k))))
  have hcondensed : Summable (fun k : ℕ => (2 : ℝ) ^ k * e2_logWeight (2 ^ k)) :=
    Summable.of_nonneg_of_le hcond_nonneg
      e2_condensed_logWeight_bound hmajor
  exact (summable_condensed_iff_of_nonneg
    (f := e2_logWeight)
    (fun n => le_of_lt (one_div_pos.mpr (e2_logWeight_den_pos n)))
    (by
      intro m n hm hmn
      exact e2_logWeight_antitone hm hmn)).mp hcondensed

private theorem e2_exponentAmplitude_sq_eq (c₀ : ℝ) (n : ℕ) :
    exponentAmplitude c₀ n ^ 2 = c₀ ^ 2 * e2_logWeight n := by
  unfold exponentAmplitude e2_logWeight
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  rw [div_pow, mul_pow, hsqrt]
  field_simp

/-- The squared exponent amplitudes form a summable sequence. -/
theorem e2_exponentAmplitude_sq_summable_proof : E2ExponentSquareSummableStatement := by
  intro c₀
  simpa only [e2_exponentAmplitude_sq_eq] using e2_summable_logWeight.mul_left (c₀ ^ 2)

end ParabolicRectifiability.Examples

end
