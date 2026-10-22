import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # One step of the lacunary frequency recursion

Proof of the one-step inequalities for the recursion defining the lacunary frequencies
(`e2_lacunaryStep_spec_proof`). -/

noncomputable section

open Real

namespace ParabolicRectifiability.Examples

/-- Proof of the one-step inequalities of the lacunary frequency recursion. -/
theorem e2_lacunaryStep_spec_proof : E2LacunaryStepStatement := by
  intro a ha j q hq hs
  set n : ℕ := q.1 with hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hq
  have hsqn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  set s0 : ℝ := q.2 + a j * Real.sqrt (n : ℝ) with hs0
  have hs0pos : 0 < s0 := by
    have := mul_pos (ha j) hsqn
    linarith
  have haj := ha j
  have haj1 := ha (j + 1)
  set A : ℝ := 100 * Real.pi * s0 / a (j + 1) with hA
  set B : ℝ := 1000 * a (j + 1) * Real.sqrt (n : ℝ) / a j with hB
  set M : ℝ := max (16 * (n : ℝ)) (max (A ^ 2) (B ^ 2)) with hM
  have hstep : e2_lacunaryStep a j q = (Nat.ceil M + 1, s0) := rfl
  rw [hstep]
  show 0 < Nat.ceil M + 1 ∧ 16 * n ≤ Nat.ceil M + 1 ∧
    Real.pi / Real.sqrt ((Nat.ceil M + 1 : ℕ) : ℝ) * s0 ≤ a (j + 1) / 100 ∧
    a (j + 1) / Real.sqrt ((Nat.ceil M + 1 : ℕ) : ℝ) ≤ a j / (1000 * Real.sqrt (n : ℝ))
  have hMN : M ≤ ((Nat.ceil M + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil M]
  have hNpos : (0 : ℝ) < ((Nat.ceil M + 1 : ℕ) : ℝ) := by positivity
  have hsqN : 0 < Real.sqrt ((Nat.ceil M + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hNpos
  refine ⟨Nat.succ_pos _, ?_, ?_, ?_⟩
  · have : (16 * n : ℝ) ≤ ((Nat.ceil M + 1 : ℕ) : ℝ) :=
      le_trans (le_max_left _ _) hMN
    exact_mod_cast this
  · have h1 : A ^ 2 ≤ ((Nat.ceil M + 1 : ℕ) : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMN
    have h2 : A ≤ Real.sqrt ((Nat.ceil M + 1 : ℕ) : ℝ) :=
      le_trans (le_abs_self A) (Real.abs_le_sqrt h1)
    have h3 : 100 * Real.pi * s0 ≤ Real.sqrt ((Nat.ceil M + 1 : ℕ) : ℝ) * a (j + 1) := by
      have := (div_le_iff₀ haj1).mp h2
      exact this
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hsqN (by norm_num)]
    linarith
  · have h1 : B ^ 2 ≤ ((Nat.ceil M + 1 : ℕ) : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMN
    have h2 : B ≤ Real.sqrt ((Nat.ceil M + 1 : ℕ) : ℝ) :=
      le_trans (le_abs_self B) (Real.abs_le_sqrt h1)
    have h3 : 1000 * a (j + 1) * Real.sqrt (n : ℝ) ≤
        Real.sqrt ((Nat.ceil M + 1 : ℕ) : ℝ) * a j :=
      (div_le_iff₀ haj).mp h2
    rw [div_le_div_iff₀ hsqN (by positivity)]
    nlinarith

end ParabolicRectifiability.Examples
