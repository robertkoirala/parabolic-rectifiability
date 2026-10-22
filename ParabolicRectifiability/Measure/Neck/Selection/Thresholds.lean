import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Elementary thresholds of the neck construction

Proofs of two arithmetic statements:

* `exists_neck_thresholds_proof` (`exists_neck_thresholds`): given the final constant
  `C` and the positive geometric thresholds, a tube threshold `θ₀ ≤ θ₁` and a noncollapse
  factor `A ≥ A₁` put `C √(B/a)`, `C B/a`, `C (θ + √(B/a))` and `C (θ² + B/a)` below
  `δ₀, E₀, κ₀, γ₀` whenever `0 < θ ≤ θ₀`, `0 < B` and `A B ≤ a`.
  With `m = min (min δ₀ E₀) (min κ₀ γ₀)` and `η = min 1 (m / (2C))` one takes
  `θ₀ = min θ₁ η` and `A = max A₁ η⁻²`; then `B/a ≤ η²`, so `√(B/a) ≤ η`, and every
  quantity is at most `2 C η ≤ m`.
* `exists_child_scales_proof` (`exists_child_scales`): with
  `M = C_g (3^{n+2} C_col + 2^{n+2} C_ter) + 1` the common choice `ρ = ε = 1/(24 M)`
  works for every `k ≤ n + 2`.

Both proofs are elementary real arithmetic and use no project declaration.
-/

namespace ParabolicRectifiability

/-- **`exists_neck_thresholds`**: elementary choice of the thresholds. -/
theorem exists_neck_thresholds_proof (C δ₀ E₀ κ₀ θ₁ γ₀ A₁ : ℝ) (hC : 0 < C) (hδ₀ : 0 < δ₀)
    (hE₀ : 0 < E₀) (hκ₀ : 0 < κ₀) (hθ₁ : 0 < θ₁) (hγ₀ : 0 < γ₀) (hA₁ : 0 < A₁) :
    ∃ θ₀ A : ℝ, 0 < θ₀ ∧ θ₀ ≤ θ₁ ∧ A₁ ≤ A ∧
      ∀ θ B a : ℝ, 0 < θ → θ ≤ θ₀ → 0 < B → A * B ≤ a →
        C * Real.sqrt (B / a) ≤ δ₀ ∧ C * (B / a) ≤ E₀ ∧ C * (θ + Real.sqrt (B / a)) ≤ κ₀ ∧
          C * (θ ^ 2 + B / a) ≤ γ₀ := by
  set m : ℝ := min (min δ₀ E₀) (min κ₀ γ₀) with hm
  have hm0 : 0 < m := lt_min (lt_min hδ₀ hE₀) (lt_min hκ₀ hγ₀)
  have hmδ : m ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hmE : m ≤ E₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hmκ : m ≤ κ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hmγ : m ≤ γ₀ := (min_le_right _ _).trans (min_le_right _ _)
  have h2C : 0 < 2 * C := by linarith
  have hCne : C ≠ 0 := hC.ne'
  set η : ℝ := min 1 (m / (2 * C)) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos hm0 h2C)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηC : 2 * C * η ≤ m := by
    have h : η ≤ m / (2 * C) := min_le_right _ _
    calc 2 * C * η ≤ 2 * C * (m / (2 * C)) := mul_le_mul_of_nonneg_left h h2C.le
      _ = m := by field_simp
  have hη2 : 0 < η ^ 2 := pow_pos hη0 2
  have hη2η : η ^ 2 ≤ η :=
    calc η ^ 2 = η * η := sq η
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left hη1 hη0.le
      _ = η := mul_one η
  refine ⟨min θ₁ η, max A₁ (1 / η ^ 2), lt_min hθ₁ hη0, min_le_left _ _, le_max_left _ _, ?_⟩
  intro θ B a hθ hθ₀ hB ha
  have hA : 0 < max A₁ (1 / η ^ 2) := lt_of_lt_of_le hA₁ (le_max_left _ _)
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hA hB) ha
  have hs0 : 0 ≤ B / a := div_nonneg hB.le ha0.le
  have hs : B / a ≤ η ^ 2 := by
    rw [div_le_iff₀ ha0]
    have h1 : 1 / η ^ 2 * B ≤ a :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB.le) ha
    have h2 : B = η ^ 2 * (1 / η ^ 2 * B) := by
      rw [← mul_assoc, mul_one_div_cancel hη2.ne', one_mul]
    calc B = η ^ 2 * (1 / η ^ 2 * B) := h2
      _ ≤ η ^ 2 * a := mul_le_mul_of_nonneg_left h1 hη2.le
  have hsq : Real.sqrt (B / a) ≤ η :=
    calc Real.sqrt (B / a) ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt hs
      _ = η := Real.sqrt_sq hη0.le
  have hsq0 : 0 ≤ Real.sqrt (B / a) := Real.sqrt_nonneg _
  have hθη : θ ≤ η := hθ₀.trans (min_le_right _ _)
  have hsη : B / a ≤ η := hs.trans hη2η
  have hθ1 : θ ≤ 1 := hθη.trans hη1
  have hθ2 : θ ^ 2 ≤ η :=
    calc θ ^ 2 = θ * θ := sq θ
      _ ≤ θ * 1 := mul_le_mul_of_nonneg_left hθ1 hθ.le
      _ = θ := mul_one θ
      _ ≤ η := hθη
  have hCη : C * η ≤ m := by linarith [mul_pos hC hη0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc C * Real.sqrt (B / a) ≤ C * η := mul_le_mul_of_nonneg_left hsq hC.le
      _ ≤ m := hCη
      _ ≤ δ₀ := hmδ
  · calc C * (B / a) ≤ C * η := mul_le_mul_of_nonneg_left hsη hC.le
      _ ≤ m := hCη
      _ ≤ E₀ := hmE
  · calc C * (θ + Real.sqrt (B / a)) ≤ C * (η + η) :=
          mul_le_mul_of_nonneg_left (add_le_add hθη hsq) hC.le
      _ = 2 * C * η := by ring
      _ ≤ m := hηC
      _ ≤ κ₀ := hmκ
  · calc C * (θ ^ 2 + B / a) ≤ C * (η + η) :=
          mul_le_mul_of_nonneg_left (add_le_add hθ2 hsη) hC.le
      _ = 2 * C * η := by ring
      _ ≤ m := hηC
      _ ≤ γ₀ := hmγ

/-- **`exists_child_scales`**: a common choice of the child scales. -/
theorem exists_child_scales_proof (n : ℕ) (Cg Ccol Cter : ℝ) (hCg : 0 ≤ Cg)
    (hCcol : 0 ≤ Ccol) (hCter : 0 ≤ Cter) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 12 * ρ ≤ 1 / 2 ∧ 0 < ε ∧ ε ≤ 1 ∧ 2 * ε ≤ 1 / 2 ∧
      ∀ k : ℕ, k ≤ n + 2 → Cg * (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ε ^ 2) ≤ 1 / 2 := by
  set K : ℝ := Cg * (3 ^ (n + 2) * Ccol + 2 ^ (n + 2) * Cter) with hK
  have hK0 : 0 ≤ K := by positivity
  set M : ℝ := K + 1 with hM
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hMne : M ≠ 0 := hM0.ne'
  set ρ : ℝ := 1 / (24 * M) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ24 : ρ ≤ 1 / 24 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hMρ : M * ρ = 1 / 24 := by
    rw [hρ]
    field_simp
  refine ⟨ρ, ρ, hρ0, by linarith, by linarith, hρ0, by linarith, by linarith, ?_⟩
  intro k hk
  have h3 : (3 : ℝ) ^ k ≤ 3 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hk
  have h2 : (2 : ℝ) ^ k ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) hk
  have hρ1 : ρ ≤ 1 := by linarith
  have hρ2 : ρ ^ 2 ≤ ρ :=
    calc ρ ^ 2 = ρ * ρ := sq ρ
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hρ1 hρ0.le
      _ = ρ := mul_one ρ
  have e1 : 3 ^ k * Ccol * ρ ≤ 3 ^ (n + 2) * Ccol * ρ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hCcol) hρ0.le
  have e2 : 2 ^ k * Cter * ρ ^ 2 ≤ 2 ^ (n + 2) * Cter * ρ :=
    mul_le_mul (mul_le_mul_of_nonneg_right h2 hCter) hρ2 (by positivity) (by positivity)
  have key : Cg * (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ρ ^ 2) ≤ K * ρ :=
    calc Cg * (3 ^ k * Ccol * ρ + 2 ^ k * Cter * ρ ^ 2)
        ≤ Cg * (3 ^ (n + 2) * Ccol * ρ + 2 ^ (n + 2) * Cter * ρ) :=
          mul_le_mul_of_nonneg_left (add_le_add e1 e2) hCg
      _ = K * ρ := by rw [hK]; ring
  have hKρ : K * ρ ≤ M * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ0.le
  linarith

end ParabolicRectifiability
