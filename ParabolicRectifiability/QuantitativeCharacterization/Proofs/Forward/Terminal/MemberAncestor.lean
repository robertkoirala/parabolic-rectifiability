import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Member ancestors of a good region

Proof of `d1c_ancestor_proof : AncestorStatement`.

(a) A member at the root level is the root: its centre lies in its own cell, which lies in the root
cell, and same-level cells of distinct centres are disjoint. (b) Iterating `P.parent` gives, at each
level `i` between the root's and `Q.1`, a cell containing `cell Q`; its own level-`root.1` ancestor
contains `Q.2 ∈ rootCell`, hence is the root cell, so the level-`i` cell lies below the root, and
`hereditary` makes it a member.
-/

set_option autoImplicit false

noncomputable section

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section Ancestor

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

/-- A centre lies in its own cell (`center_subset`, `inner_subset`). -/
theorem d1canc_center_mem_cell (P : DirectPartition E ℓ₀) {j : ℕ} {z : Space n}
    (hz : z ∈ P.center j) : z ∈ P.cell j z := by
  apply P.inner_subset j z hz
  refine ⟨P.center_subset j hz, ?_⟩
  rw [Metric.mem_ball, dist_self]
  have h : 0 < coherentScale ℓ₀ j := div_pos P.scale_pos (pow_pos (by norm_num) _)
  linarith

/-- Every cell has, at each coarser level, an ancestor cell containing it (`parent_mem`,
`cell_subset_parent`). -/
theorem d1canc_exists_ancestor (P : DirectPartition E ℓ₀) :
    ∀ (l : ℕ) (w : Space n), w ∈ P.center l → ∀ m : ℕ, m ≤ l →
      ∃ w' ∈ P.center m, P.cell l w ⊆ P.cell m w' := by
  intro l
  induction l with
  | zero =>
    intro w hw m hm
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    exact ⟨w, hw, subset_rfl⟩
  | succ l ih =>
    intro w hw m hm
    rcases Nat.lt_or_ge m (l + 1) with h | h
    · obtain ⟨w', hw', hsub⟩ :=
        ih (P.parent l w) (P.parent_mem l w hw) m (Nat.lt_succ_iff.mp h)
      exact ⟨w', hw', (P.cell_subset_parent l w hw).trans hsub⟩
    · obtain rfl : m = l + 1 := le_antisymm hm h
      exact ⟨w, hw, subset_rfl⟩

/-- Two same-level cells sharing a point have the same centre (`cell_disjoint`). -/
theorem d1canc_eq_of_mem_cells (P : DirectPartition E ℓ₀) {m : ℕ} {w w' x : Space n}
    (hw : w ∈ P.center m) (hw' : w' ∈ P.center m) (hx : x ∈ P.cell m w)
    (hx' : x ∈ P.cell m w') : w = w' := by
  by_contra hne
  exact Set.disjoint_left.mp (P.cell_disjoint m w hw w' hw' hne) hx hx'

end Ancestor

/-- **Member ancestors** (`AncestorStatement`). -/
theorem d1c_ancestor_proof : AncestorStatement := by
  intro n E ℓ₀ P μ k Λ b 𝒢
  have hroot : 𝒢.root.2 ∈ P.center 𝒢.root.1 := 𝒢.root_isCell
  refine ⟨?_, ?_⟩
  · intro Q hQ hlev
    obtain ⟨hQc, -, hQsub⟩ := 𝒢.below_root Q hQ
    have hmem : Q.2 ∈ P.cell Q.1 Q.2 := d1canc_center_mem_cell P hQc
    have hQc' : Q.2 ∈ P.center 𝒢.root.1 := by rw [← hlev]; exact hQc
    have hmem' : Q.2 ∈ P.cell 𝒢.root.1 Q.2 := by rw [← hlev]; exact hmem
    have hroot_mem : Q.2 ∈ P.cell 𝒢.root.1 𝒢.root.2 := hQsub hmem
    exact Prod.ext hlev (d1canc_eq_of_mem_cells P hQc' hroot hmem' hroot_mem)
  · intro Q hQ i hi hiQ
    obtain ⟨hQc, -, hQsub⟩ := 𝒢.below_root Q hQ
    obtain ⟨w, hw, hQw⟩ := d1canc_exists_ancestor P Q.1 Q.2 hQc i hiQ
    obtain ⟨w', hw', hww'⟩ := d1canc_exists_ancestor P i w hw 𝒢.root.1 hi
    have hmem : Q.2 ∈ P.cell Q.1 Q.2 := d1canc_center_mem_cell P hQc
    have h1 : Q.2 ∈ P.cell 𝒢.root.1 w' := hww' (hQw hmem)
    have h2 : Q.2 ∈ P.cell 𝒢.root.1 𝒢.root.2 := hQsub hmem
    have hw'eq : w' = 𝒢.root.2 := d1canc_eq_of_mem_cells P hw' hroot h1 h2
    have hsub : P.cell i w ⊆ P.cell 𝒢.root.1 𝒢.root.2 := by rw [← hw'eq]; exact hww'
    have hbelowQ : P.IsBelow Q (i, w) := ⟨hQc, hiQ, hQw⟩
    have hbelowR : P.IsBelow (i, w) 𝒢.root := ⟨hw, hi, hsub⟩
    exact ⟨(i, w), 𝒢.hereditary Q hQ (i, w) hbelowQ hbelowR, rfl, hQw⟩

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
