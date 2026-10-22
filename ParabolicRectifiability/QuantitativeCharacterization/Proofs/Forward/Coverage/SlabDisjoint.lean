import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # Disjointness of the slabs

Proves `SlabDisjointStatement` without any hypothesis: distinct cell addresses `Q ≠ Q'` have disjoint slabs. Same level: the cells are
disjoint (`cell_disjoint`); different levels: `ℓ_{Q'} ≤ ℓ_Q / 10` makes the half-open scale
intervals `[ℓ/10, ℓ)` disjoint.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- One step down the levels divides the scale by at least `10`: `ℓ_j ≤ ℓ_i / 10` for `i < j`. -/
theorem d1fsdisj_scale_le {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    {i j : ℕ} (h : i < j) : P.scale j ≤ P.scale i / 10 := by
  have hpos : 0 < ℓ₀ := P.scale_pos
  have hpow : (10 : ℝ) ^ (i + 1) ≤ 10 ^ j := pow_le_pow_right₀ (by norm_num) h
  unfold DirectPartition.scale coherentScale
  rw [div_div, ← pow_succ]
  exact div_le_div_of_nonneg_left hpos.le (by positivity) hpow

/-- The half-open scale intervals `[s/10, s)` and `[s'/10, s')` are disjoint when `s' ≤ s/10`. -/
theorem d1fsdisj_Ico_disjoint {s s' : ℝ} (h : s' ≤ s / 10) :
    Disjoint (Ico (s / 10) s) (Ico (s' / 10) s') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  linarith [hx.1, hx'.2]

/-- Slabs of cells at strictly increasing levels are disjoint. -/
theorem d1fsdisj_lt {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (a : Space n) (R : ℝ) {Q Q' : ℕ × Space n} (h : Q.1 < Q'.1) :
    Disjoint (slab P a R Q) (slab P a R Q') :=
  Disjoint.set_prod_right (d1fsdisj_Ico_disjoint (d1fsdisj_scale_le P h)) _ _

/-- **Slab disjointness**: distinct cell addresses have disjoint slabs. -/
theorem d1f_slabDisjoint_proof : SlabDisjointStatement := by
  intro n E ℓ₀ P a R Q Q' hQ hQ' hne
  rcases lt_trichotomy Q.1 Q'.1 with h | h | h
  · exact d1fsdisj_lt P a R h
  · have hQ'' : Q'.2 ∈ P.center Q.1 := by
      rw [h]
      exact hQ'
    have h2 : Q.2 ≠ Q'.2 := fun h2 => hne (Prod.ext h h2)
    have hd : Disjoint (P.cell Q.1 Q.2) (P.cell Q.1 Q'.2) := P.cell_disjoint Q.1 Q.2 hQ Q'.2 hQ'' h2
    have hd' : Disjoint (P.cellOf Q ∩ Metric.ball a R) (P.cellOf Q' ∩ Metric.ball a R) := by
      refine (hd.mono inter_subset_left ?_)
      have : P.cellOf Q' = P.cell Q.1 Q'.2 := by
        unfold DirectPartition.cellOf
        rw [h]
      rw [← this]
      exact inter_subset_left
    exact Disjoint.set_prod_left hd' _ _
  · exact (d1fsdisj_lt P a R h).symm

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
