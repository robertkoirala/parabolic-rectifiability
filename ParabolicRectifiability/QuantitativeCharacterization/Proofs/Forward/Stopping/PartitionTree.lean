import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping

/-! # Tree facts of a direct partition

Proof of `d1b_partitionTree_proof : PartitionTreeStatement`: every field of `PartitionTree P` for an arbitrary direct
partition `P` of an arbitrary set `E`.

Route: the scales are `coherentScale ℓ₀ j = ℓ₀ / 10^j`; a centre lies in its cell by
`center_subset` and `inner_subset`; ancestors by iterating `parent` / `cell_subset_parent`
(induction on `Q.1 - j`); two cells of one level with a common point have the same centre by
`cell_disjoint`; this gives `eq_of_isBelow`, `isBelow_of_common` and `isBelow_or_disjoint`;
`inForest_subset` from `cell_subset_ball` at level `0` and the triangle inequality. No
closedness of `E` and no measure is used. Helpers carry the prefix `d1btree_`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

section Tree

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

/-- The scale `ℓ_j = ℓ₀ / 10^j` is positive. -/
theorem d1btree_coherentScale_pos (P : DirectPartition E ℓ₀) (j : ℕ) :
    0 < coherentScale ℓ₀ j := by
  show 0 < ℓ₀ / 10 ^ j
  exact div_pos P.scale_pos (pow_pos (by norm_num) j)

/-- A centre lies in its own cell (`center_subset`, `inner_subset`). -/
theorem d1btree_center_mem (P : DirectPartition E ℓ₀) {j : ℕ} {z : Space n}
    (hz : z ∈ P.center j) : z ∈ P.cell j z := by
  apply P.inner_subset j z hz
  refine ⟨P.center_subset j hz, ?_⟩
  rw [Metric.mem_ball, dist_self]
  have := d1btree_coherentScale_pos P j
  linarith

/-- Two cells of one level with a common point have the same centre (`cell_disjoint`). -/
theorem d1btree_eq_of_mem (P : DirectPartition E ℓ₀) {j : ℕ} {z z' : Space n}
    (hz : z ∈ P.center j) (hz' : z' ∈ P.center j) {x : Space n}
    (hx : x ∈ P.cell j z) (hx' : x ∈ P.cell j z') : z = z' := by
  by_contra hne
  exact Set.disjoint_left.mp (P.cell_disjoint j z hz z' hz' hne) hx hx'

/-- Iterated parents: a cell of level `j + m` lies in a cell of level `j`. -/
theorem d1btree_ancestor_aux (P : DirectPartition E ℓ₀) (j : ℕ) :
    ∀ m : ℕ, ∀ w ∈ P.center (j + m), ∃ z ∈ P.center j, P.cell (j + m) w ⊆ P.cell j z := by
  intro m
  induction m with
  | zero =>
    intro w hw
    exact ⟨w, hw, subset_rfl⟩
  | succ m ih =>
    intro w hw
    rw [← Nat.add_assoc] at hw ⊢
    obtain ⟨z, hz, hsub⟩ := ih (P.parent (j + m) w) (P.parent_mem (j + m) w hw)
    exact ⟨z, hz, (P.cell_subset_parent (j + m) w hw).trans hsub⟩

/-- `IsBelow` is transitive. -/
theorem d1btree_isBelow_trans (P : DirectPartition E ℓ₀) {Q T U : ℕ × Space n}
    (hQT : P.IsBelow Q T) (hTU : P.IsBelow T U) : P.IsBelow Q U := by
  obtain ⟨hQ, hQT1, hQTs⟩ := hQT
  obtain ⟨-, hTU1, hTUs⟩ := hTU
  exact ⟨hQ, hTU1.trans hQT1, hQTs.trans hTUs⟩

/-- Every cell has an ancestor cell at each coarser level. -/
theorem d1btree_exists_ancestor (P : DirectPartition E ℓ₀) (Q : ℕ × Space n) (hQ : P.IsCell Q)
    (j : ℕ) (hj : j ≤ Q.1) : ∃ T : ℕ × Space n, P.IsCell T ∧ T.1 = j ∧ P.IsBelow Q T := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hj
  have hQ' : Q.2 ∈ P.center (j + m) := by
    rw [← hm]
    exact hQ
  obtain ⟨z, hz, hsub⟩ := d1btree_ancestor_aux P j m Q.2 hQ'
  refine ⟨(j, z), hz, rfl, hQ, hj, ?_⟩
  show P.cell Q.1 Q.2 ⊆ P.cell j z
  rw [hm]
  exact hsub

/-- Below a cell, a cell of the same level is that cell. -/
theorem d1btree_eq_of_isBelow (P : DirectPartition E ℓ₀) (Q T : ℕ × Space n)
    (hT : P.IsCell T) (hQT : P.IsBelow Q T) (hlev : Q.1 = T.1) : Q = T := by
  obtain ⟨i, w⟩ := Q
  obtain ⟨j, z⟩ := T
  obtain ⟨hQ, -, hsub⟩ := hQT
  change i = j at hlev
  subst hlev
  change w ∈ P.center i at hQ
  change z ∈ P.center i at hT
  change P.cell i w ⊆ P.cell i z at hsub
  have hwz : w = z :=
    d1btree_eq_of_mem P hQ hT (d1btree_center_mem P hQ) (hsub (d1btree_center_mem P hQ))
  rw [hwz]

/-- Two ancestors of one cell are nested. -/
theorem d1btree_isBelow_of_common (P : DirectPartition E ℓ₀) (Q T U : ℕ × Space n)
    (hT : P.IsCell T) (hU : P.IsCell U) (hQT : P.IsBelow Q T) (hQU : P.IsBelow Q U)
    (hle : T.1 ≤ U.1) : P.IsBelow U T := by
  obtain ⟨T', hT', hT'1, hUT'⟩ := d1btree_exists_ancestor P U hU T.1 hle
  have hQT' : P.IsBelow Q T' := d1btree_isBelow_trans P hQU hUT'
  obtain ⟨hQ, -, hQTs⟩ := hQT
  obtain ⟨-, -, hQT's⟩ := hQT'
  obtain ⟨-, -, hUT's⟩ := hUT'
  have hx : Q.2 ∈ P.cell Q.1 Q.2 := d1btree_center_mem P hQ
  have hxT : Q.2 ∈ P.cell T.1 T.2 := hQTs hx
  have hxT' : Q.2 ∈ P.cell T.1 T'.2 := by
    rw [← hT'1]
    exact hQT's hx
  have hT'' : T'.2 ∈ P.center T.1 := by
    rw [← hT'1]
    exact hT'
  have heq : T.2 = T'.2 := d1btree_eq_of_mem P hT hT'' hxT hxT'
  refine ⟨hU, hle, ?_⟩
  show P.cellOf U ⊆ P.cell T.1 T.2
  rw [heq, ← hT'1]
  exact hUT's

/-- Two cells are nested or disjoint. -/
theorem d1btree_isBelow_or_disjoint (P : DirectPartition E ℓ₀) (Q T : ℕ × Space n)
    (hQ : P.IsCell Q) (hT : P.IsCell T) (hle : T.1 ≤ Q.1) :
    P.IsBelow Q T ∨ Disjoint (P.cellOf Q) (P.cellOf T) := by
  obtain ⟨T', hT', hT'1, hQT'⟩ := d1btree_exists_ancestor P Q hQ T.1 hle
  obtain ⟨-, -, hQT's⟩ := hQT'
  have hT'' : T'.2 ∈ P.center T.1 := by
    rw [← hT'1]
    exact hT'
  have hsub : P.cellOf Q ⊆ P.cell T.1 T'.2 := by
    rw [← hT'1]
    exact hQT's
  by_cases heq : T'.2 = T.2
  · left
    refine ⟨hQ, hle, ?_⟩
    show P.cellOf Q ⊆ P.cell T.1 T.2
    rw [← heq]
    exact hsub
  · right
    exact (P.cell_disjoint T.1 T'.2 hT'' T.2 hT heq).mono_left hsub

/-- The root forest is closed downward. -/
theorem d1btree_inForest_of_isBelow (P : DirectPartition E ℓ₀) (a : Space n) (R : ℝ)
    (Q T : ℕ × Space n) (hT : P.InForest a R T) (hQT : P.IsBelow Q T) : P.InForest a R Q := by
  obtain ⟨z₀, hz₀, hne, hT0⟩ := hT
  exact ⟨z₀, hz₀, hne, d1btree_isBelow_trans P hQT hT0⟩

/-- Forest cells lie in `P(a, R + 4 ℓ₀)`. -/
theorem d1btree_inForest_subset (P : DirectPartition E ℓ₀) (a : Space n) (R : ℝ)
    (Q : ℕ × Space n) (hQ : P.InForest a R Q) : P.cellOf Q ⊆ Metric.ball a (R + 4 * ℓ₀) := by
  obtain ⟨z₀, hz₀, ⟨y, hy0, hya⟩, -, -, hsub⟩ := hQ
  intro x hx
  have hx0 : x ∈ P.cell 0 z₀ := hsub hx
  have h1 := P.cell_subset_ball 0 z₀ hz₀ hx0
  have h2 := P.cell_subset_ball 0 z₀ hz₀ hy0
  have hs : coherentScale ℓ₀ 0 = ℓ₀ := by
    show ℓ₀ / 10 ^ 0 = ℓ₀
    simp
  rw [hs, Metric.mem_ball] at h1 h2
  rw [Metric.mem_ball] at hya ⊢
  have t1 := dist_triangle x z₀ a
  have t2 := dist_triangle z₀ y a
  have t3 := dist_comm y z₀
  linarith

end Tree

/-- **Tree facts of direct partitions**: the tree
facts of every direct partition of every set. -/
theorem d1b_partitionTree_proof : PartitionTreeStatement := by
  intro n E ℓ₀ P
  exact
    { scale_pos := fun j => d1btree_coherentScale_pos P j
      scale_zero := by
        show ℓ₀ / 10 ^ 0 = ℓ₀
        simp
      scale_succ := fun j => by
        show ℓ₀ / 10 ^ (j + 1) = ℓ₀ / 10 ^ j / 10
        rw [pow_succ, div_div]
      center_mem_cell := fun Q hQ => d1btree_center_mem P hQ
      isBelow_refl := fun Q hQ => ⟨hQ, le_rfl, subset_rfl⟩
      isBelow_trans := fun Q T U hQT hTU => d1btree_isBelow_trans P hQT hTU
      exists_ancestor := fun Q hQ j hj => d1btree_exists_ancestor P Q hQ j hj
      eq_of_isBelow := fun Q T hT hQT hlev => d1btree_eq_of_isBelow P Q T hT hQT hlev
      isBelow_of_common := fun Q T U hT hU hQT hQU hle =>
        d1btree_isBelow_of_common P Q T U hT hU hQT hQU hle
      isBelow_or_disjoint := fun Q T hQ hT hle => d1btree_isBelow_or_disjoint P Q T hQ hT hle
      inForest_of_isBelow := fun a R Q T hT hQT => d1btree_inForest_of_isBelow P a R Q T hT hQT
      inForest_subset := fun a R Q hQ => d1btree_inForest_subset P a R Q hQ }

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
