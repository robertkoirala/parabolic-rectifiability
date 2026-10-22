import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # Scales and nested grids of the dispersed digit construction

Arithmetic of the scales `ℓ_j, h_j, P_j, δ_j`: positivity, the nested grids (`ℓ_i` is an
integer multiple of `ℓ_j` for `i ≤ j`, and `1/ℓ_j` is an integer), and the exact relations
`h_j = ℓ_{j-1}/2^{j+20}`, `h_j = 2^{10} P_j`, `ℓ_{j-1} = 2^{j+30} P_j` (`e2_sb_grid_proof`). -/

namespace ParabolicRectifiability.Examples

private theorem e2_sb_grid_N_pos (j : ℕ) : 0 < e2_sbN j := by
  unfold e2_sbN
  positivity

private theorem e2_sb_grid_ell_pos (j : ℕ) : 0 < e2_sbEll j := by
  induction j with
  | zero => norm_num [e2_sbEll]
  | succ j ih =>
    exact div_pos ih (by exact_mod_cast e2_sb_grid_N_pos (j + 1))

private theorem e2_sb_grid_step (j : ℕ) :
    e2_sbEll j = (e2_sbN (j + 1) : ℝ) * e2_sbEll (j + 1) := by
  rw [e2_sbEll]
  exact (mul_div_cancel₀ _ (ne_of_gt (by exact_mod_cast e2_sb_grid_N_pos (j + 1) : (0 : ℝ) < e2_sbN (j + 1)))).symm

private theorem e2_sb_grid_nested (i j : ℕ) (hij : i ≤ j) :
    ∃ c : ℕ, e2_sbEll i = (c : ℝ) * e2_sbEll j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact ⟨1, by simp⟩
  | succ j ih =>
    by_cases h : i = j + 1
    · subst i
      exact ⟨1, by simp⟩
    · obtain ⟨c, hc⟩ := ih (by omega)
      refine ⟨c * e2_sbN (j + 1), ?_⟩
      rw [hc, e2_sb_grid_step j, Nat.cast_mul]
      ring

private theorem e2_sb_grid_period (j : ℕ) :
    e2_sbEll j = 2 ^ (j + 1 + 30) * e2_sbPeriod (j + 1) := by
  rw [e2_sbPeriod, e2_sbEll, e2_sbN]
  push_cast
  have hq : (j : ℝ) + 1 + 1 ≠ 0 := by positivity
  field_simp [hq]

/-- The grid properties of the scales, proved directly from their recursive definition. -/
theorem e2_sb_grid_proof : E2sbGrid := by
  refine ⟨e2_sb_grid_ell_pos, ?_, ?_, e2_sb_grid_nested, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | zero => norm_num [e2_sbH]
    | succ j => exact div_pos (e2_sb_grid_ell_pos j) (by positivity)
  · intro j
    induction j with
    | zero => norm_num [e2_sbEll]
    | succ j ih =>
      exact (div_le_self (le_of_lt (e2_sb_grid_ell_pos j))
        (by
          have hn : 1 ≤ e2_sbN (j + 1) := e2_sb_grid_N_pos (j + 1)
          exact_mod_cast hn)).trans ih
  · intro j
    obtain ⟨c, hc⟩ := e2_sb_grid_nested 0 j (Nat.zero_le j)
    exact ⟨c, by simpa [e2_sbEll] using hc.symm⟩
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    simp [e2_sbH, Nat.add_assoc]
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hp := e2_sb_grid_period k
    rw [e2_sbH, hp]
    have he : k + 1 + 30 = (k + 21) + 10 := by omega
    rw [he, pow_add]
    field_simp
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    simpa using e2_sb_grid_period k
  · intro j hj
    constructor
    · unfold e2_sbDelta
      positivity
    · unfold e2_sbDelta
      have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)
        (by norm_num : (0 : ℝ) < 2)).2
      linarith

end ParabolicRectifiability.Examples
