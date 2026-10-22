import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Protected balls

Proof of `d1a_protectedBalls_proof : ProtectedBallsStatement`, for arbitrary assigned cells `C`,
from the hypotheses `N.ClosedCellBasics` and `N.UniqueInner`. Write `l = j + d` and let `z'` be the
level-`j` ancestor of `w`.

* Iterating `cell_subset_parent` gives `Q_{l,w} ⊆ Q_{j,z'}`, so `Q_{l,w} ⊄ Q_{j,z}` forces `z' ≠ z`.
* **Coarse ball.** Iterating the child-union identity gives `C_{l,w} ⊆ C_{j,z'}`; with
  `closure Q_{l,w} = C_{l,w}`, the unique-inner property at level `j` for `z ≠ z'` protects
  `E ∩ P(z, ℓ_j/4)`.
* **Fine ball.** Iterating the child-union identity the other way, `C_{j,z}` is contained in the
  union of the closed
  cells `C_{l,v}` of the level-`l` centres `v` with level-`j` ancestor `z`. None of them is `w`
  (its ancestor is `z' ≠ z`), so the unique-inner property at level `l` protects
  `E ∩ P(w, ℓ_l/4)` from
  `closure Q_{j,z} = C_{j,z}`.

The hypothesis `IsClosed E` is not used.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

/-- One more ancestor step. -/
theorem d1aprot_ancestor_succ (N : NestedNets E ℓ₀) (j d : ℕ) (w : Space n) :
    N.ancestor j (d + 1) w = N.ancestor j d (N.parent (j + d) w) :=
  rfl

/-- The level-`j` ancestor of a level-`(j + d)` centre is a level-`j` centre. -/
theorem d1aprot_ancestor_mem (N : NestedNets E ℓ₀) (j : ℕ) :
    ∀ d : ℕ, ∀ w ∈ N.center (j + d), N.ancestor j d w ∈ N.center j := by
  intro d
  induction d with
  | zero =>
    intro w hw
    exact hw
  | succ d ih =>
    intro w hw
    rw [d1aprot_ancestor_succ]
    exact ih _ (N.parent_mem (j + d) w hw)

/-- Iterated `cell_subset_parent`: `Q_{j+d,w} ⊆ Q_{j, ancestor w}`. -/
theorem d1aprot_cell_subset_ancestor (N : NestedNets E ℓ₀) (C : N.AssignedCells) (j : ℕ) :
    ∀ d : ℕ, ∀ w ∈ N.center (j + d), C.cell (j + d) w ⊆ C.cell j (N.ancestor j d w) := by
  intro d
  induction d with
  | zero =>
    intro w _hw
    exact subset_rfl
  | succ d ih =>
    intro w hw
    rw [d1aprot_ancestor_succ]
    exact (C.cell_subset_parent (j + d) w hw).trans (ih _ (N.parent_mem (j + d) w hw))

/-- A child's closed cell lies in its parent's closed cell (from the child-union identity). -/
theorem d1aprot_closedCell_subset_parent (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics)
    (i : ℕ) (w : Space n) (hw : w ∈ N.center (i + 1)) :
    N.closedCell (i + 1) w ⊆ N.closedCell i (N.parent i w) := by
  rw [hB.closedCell_children i (N.parent i w) (N.parent_mem i w hw)]
  have hch : w ∈ N.children i (N.parent i w) := ⟨hw, rfl⟩
  exact Set.subset_biUnion_of_mem (u := fun v => N.closedCell (i + 1) v) hch

/-- Iterated child-union identity: `C_{j+d,w} ⊆ C_{j, ancestor w}`. -/
theorem d1aprot_closedCell_subset_ancestor (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics)
    (j : ℕ) : ∀ d : ℕ, ∀ w ∈ N.center (j + d),
      N.closedCell (j + d) w ⊆ N.closedCell j (N.ancestor j d w) := by
  intro d
  induction d with
  | zero =>
    intro w _hw
    exact subset_rfl
  | succ d ih =>
    intro w hw
    rw [d1aprot_ancestor_succ]
    exact (d1aprot_closedCell_subset_parent N hB (j + d) w hw).trans
      (ih _ (N.parent_mem (j + d) w hw))

/-- Iterated child-union identity downward: `C_{j,z}` is covered by the closed cells of the level-`(j + d)`
centres whose level-`j` ancestor is `z`. -/
theorem d1aprot_closedCell_subset_union (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics)
    (j : ℕ) (z : Space n) (hz : z ∈ N.center j) : ∀ d : ℕ,
      N.closedCell j z ⊆
        ⋃ v ∈ {v | v ∈ N.center (j + d) ∧ N.ancestor j d v = z}, N.closedCell (j + d) v := by
  intro d
  induction d with
  | zero =>
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨z, ⟨hz, rfl⟩, hx⟩
  | succ d ih =>
    intro x hx
    obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.mp (ih hx)
    obtain ⟨huc, hua⟩ := hu
    rw [hB.closedCell_children (j + d) u huc] at hxu
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hxu
    obtain ⟨hvc, hvp⟩ := hv
    have hva : N.ancestor j (d + 1) v = z := by
      rw [d1aprot_ancestor_succ, hvp, hua]
    exact Set.mem_iUnion₂.mpr ⟨v, ⟨hvc, hva⟩, hxv⟩

/-- **Protected balls** (`ProtectedBallsStatement`). -/
theorem d1a_protectedBalls_proof : ProtectedBallsStatement := by
  intro n E ℓ₀ N _hE hB hU C j l hjl z hz w hw hnot
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjl
  have hcell := d1aprot_cell_subset_ancestor N C j d w hw
  have hamem := d1aprot_ancestor_mem N j d w hw
  have hne : z ≠ N.ancestor j d w := by
    intro h
    apply hnot
    rw [h]
    exact hcell
  constructor
  · -- the coarse inner ball: a different level-`j` ancestor
    rw [C.closure_cell (j + d) w hw]
    apply Set.eq_empty_of_subset_empty
    exact (Set.inter_subset_inter_right _
      (d1aprot_closedCell_subset_ancestor N hB j d w hw)).trans
      (hU j z hz _ hamem hne).subset
  · -- the fine inner ball: iterated child unions
    rw [C.closure_cell j z hz, Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hxE, hxw⟩, hxC⟩
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp (d1aprot_closedCell_subset_union N hB j z hz d hxC)
    obtain ⟨hvc, hva⟩ := hv
    by_cases hwv : w = v
    · apply hne
      rw [hwv, hva]
    · have hempty := hU (j + d) w hw v hvc hwv
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) x ⟨⟨hxE, hxw⟩, hxv⟩

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
