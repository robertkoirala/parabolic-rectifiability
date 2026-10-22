import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements

/-! # Oscillation of the low-frequency cosine sum

Each summand changes by at most `|c_j| N_j ℓ`. Cauchy--Schwarz reduces the estimate
to the sum of the squared scaled frequencies. The sixteen-fold growth makes these
frequencies decrease geometrically when read backwards from `K - 1`; their squared
sum is at most `1 + 1/256 + 1/256^2 + ⋯ = 256/255`. The empty sum handles `K = 0`.
-/

namespace ParabolicRectifiability.Examples

private theorem e2_bmo3_scaledFrequencySquares
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hfreq : ∀ j, 16 * N j ≤ N (j + 1)) (K : ℕ)
    (hlow : ∀ j < K, (N j : ℝ) * ℓ ≤ 1) :
    (∑ j ∈ Finset.range K, ((N j : ℝ) * ℓ) ^ 2) ≤ (256 : ℝ) / 255 := by
  let q : ℕ → ℝ := fun j => (N j : ℝ) * ℓ
  have hq_pos : ∀ j, 0 < q j := by
    intro j
    dsimp [q]
    exact mul_pos (Nat.cast_pos.mpr (hN j)) hℓ
  have hq_nonneg : ∀ j, 0 ≤ q j := fun j => (hq_pos j).le
  have hlast_sum : ∀ m : ℕ, 0 < m →
      (∑ j ∈ Finset.range m, q j ^ 2) ≤ (256 : ℝ) / 255 * q (m - 1) ^ 2 := by
    intro m
    induction m with
    | zero =>
        intro hm
        omega
    | succ m ih =>
        intro hm
        by_cases hm0 : m = 0
        · subst m
          norm_num [Finset.sum_range_succ, q]
          nlinarith [sq_nonneg (q 0)]
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have ihm := ih hmpos
          have hfreq_nat : 16 * N (m - 1) ≤ N m := by
            simpa [Nat.sub_add_cancel hmpos] using hfreq (m - 1)
          have hfreq_real : (16 : ℝ) * (N (m - 1) : ℝ) ≤ (N m : ℝ) := by
            exact_mod_cast hfreq_nat
          have hstep : 16 * q (m - 1) ≤ q m := by
            dsimp [q]
            calc
              16 * ((N (m - 1) : ℝ) * ℓ) =
                  ((16 : ℝ) * (N (m - 1) : ℝ)) * ℓ := by ring
              _ ≤ (N m : ℝ) * ℓ := mul_le_mul_of_nonneg_right hfreq_real hℓ.le
          have hstep_sq : (256 : ℝ) * q (m - 1) ^ 2 ≤ q m ^ 2 := by
            calc
              (256 : ℝ) * q (m - 1) ^ 2 =
                  (16 * q (m - 1)) * (16 * q (m - 1)) := by ring
              _ ≤ q m * (16 * q (m - 1)) :=
                mul_le_mul_of_nonneg_right hstep (by positivity)
              _ ≤ q m * q m := mul_le_mul_of_nonneg_left hstep (hq_nonneg m)
              _ = q m ^ 2 := by ring
          rw [Finset.sum_range_succ]
          calc
            (∑ j ∈ Finset.range m, q j ^ 2) + q m ^ 2 ≤
                ((256 : ℝ) / 255 * q (m - 1) ^ 2) + q m ^ 2 :=
              add_le_add ihm le_rfl
            _ ≤ (256 : ℝ) / 255 * q m ^ 2 := by
              nlinarith [hstep_sq]
  by_cases hK : K = 0
  · subst K
    norm_num
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    have hlast := hlast_sum K hKpos
    have hq_last : q (K - 1) ≤ 1 := by
      simpa [q] using hlow (K - 1) (by omega)
    have hq_last_sq : q (K - 1) ^ 2 ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hq_last (hq_nonneg (K - 1))
      nlinarith [hq_nonneg (K - 1)]
    calc
      (∑ j ∈ Finset.range K, ((N j : ℝ) * ℓ) ^ 2) =
          ∑ j ∈ Finset.range K, q j ^ 2 := by simp [q]
      _ ≤ (256 : ℝ) / 255 * q (K - 1) ^ 2 := hlast
      _ ≤ (256 : ℝ) / 255 := by
        nlinarith [hq_last_sq]

/-- The low-frequency finite cosine sum has a uniform oscillation bound. -/
theorem e2_lowFrequency_oscillation_proof : E2LowFrequencyOscillationStatement := by
  intro c N hN hfreq ℓ hℓ K hlow t s hts
  let q : ℕ → ℝ := fun j => (N j : ℝ) * ℓ
  let C : ℝ := ∑ j ∈ Finset.range K, c j ^ 2
  let S : ℝ := ∑ j ∈ Finset.range K, |c j| * q j
  have hq_nonneg : ∀ j, 0 ≤ q j := by
    intro j
    dsimp [q]
    exact mul_nonneg (Nat.cast_nonneg _) hℓ.le
  have hgeom : (∑ j ∈ Finset.range K, q j ^ 2) ≤ (256 : ℝ) / 255 := by
    simpa [q] using e2_bmo3_scaledFrequencySquares N hN ℓ hℓ hfreq K hlow
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun j _ => sq_nonneg (c j)
  have hsum_diff :
      (∑ j ∈ Finset.range K, c j * Real.cos ((N j : ℝ) * t)) -
          ∑ j ∈ Finset.range K, c j * Real.cos ((N j : ℝ) * s) =
        ∑ j ∈ Finset.range K,
          c j * (Real.cos ((N j : ℝ) * t) - Real.cos ((N j : ℝ) * s)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hterm : ∀ j ∈ Finset.range K,
      |c j * (Real.cos ((N j : ℝ) * t) - Real.cos ((N j : ℝ) * s))| ≤
        |c j| * q j := by
    intro j _
    have hN_nonneg : 0 ≤ (N j : ℝ) := Nat.cast_nonneg _
    have hangle :
        |(N j : ℝ) * t - (N j : ℝ) * s| ≤ q j := by
      calc
        |(N j : ℝ) * t - (N j : ℝ) * s| =
            (N j : ℝ) * |t - s| := by
              rw [show (N j : ℝ) * t - (N j : ℝ) * s =
                (N j : ℝ) * (t - s) by ring, abs_mul, abs_of_nonneg hN_nonneg]
        _ ≤ (N j : ℝ) * ℓ := mul_le_mul_of_nonneg_left hts hN_nonneg
        _ = q j := rfl
    calc
      |c j * (Real.cos ((N j : ℝ) * t) - Real.cos ((N j : ℝ) * s))| =
          |c j| * |Real.cos ((N j : ℝ) * t) - Real.cos ((N j : ℝ) * s)| := abs_mul _ _
      _ ≤ |c j| * |(N j : ℝ) * t - (N j : ℝ) * s| :=
        mul_le_mul_of_nonneg_left
          (Real.abs_cos_sub_cos_le _ _) (abs_nonneg _)
      _ ≤ |c j| * q j := mul_le_mul_of_nonneg_left hangle (abs_nonneg _)
  have hsum_abs :
      |∑ j ∈ Finset.range K,
          c j * (Real.cos ((N j : ℝ) * t) - Real.cos ((N j : ℝ) * s))| ≤ S := by
    calc
      _ ≤ ∑ j ∈ Finset.range K,
          |c j * (Real.cos ((N j : ℝ) * t) - Real.cos ((N j : ℝ) * s))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ S := by
        dsimp [S]
        exact Finset.sum_le_sum hterm
  have hcs : S ^ 2 ≤ C * (∑ j ∈ Finset.range K, q j ^ 2) := by
    dsimp [S, C]
    simpa [sq_abs] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K) (fun j => |c j|) q)
  have hS_sq : S ^ 2 ≤ 4 * C := by
    calc
      S ^ 2 ≤ C * (∑ j ∈ Finset.range K, q j ^ 2) := hcs
      _ ≤ C * 4 := mul_le_mul_of_nonneg_left
        (le_trans hgeom (by norm_num)) hC_nonneg
      _ = 4 * C := by ring
  have hS_bound : S ≤ 2 * Real.sqrt C := by
    apply le_of_sq_le_sq ?_ (by positivity)
    calc
      S ^ 2 ≤ 4 * C := hS_sq
      _ = (2 * Real.sqrt C) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC_nonneg]
        ring
  calc
    |(∑ j ∈ Finset.range K, c j * Real.cos ((N j : ℝ) * t)) -
        ∑ j ∈ Finset.range K, c j * Real.cos ((N j : ℝ) * s)| =
        |∑ j ∈ Finset.range K,
          c j * (Real.cos ((N j : ℝ) * t) - Real.cos ((N j : ℝ) * s))| := by rw [hsum_diff]
    _ ≤ S := hsum_abs
    _ ≤ 2 * Real.sqrt C := hS_bound

end ParabolicRectifiability.Examples
