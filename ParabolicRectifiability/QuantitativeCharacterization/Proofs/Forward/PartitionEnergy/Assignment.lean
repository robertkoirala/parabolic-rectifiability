import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Exact Borel assignment of nested cells

Proof of `d1a_assignment_proof : AssignmentStatement`: the nested closed cells of a net are
refined to an exact Borel partition (the assigned cells), with the inclusions
`D_{j,z} ⊆ Q_{j,z} ⊆ C_{j,z}` and the closure identity.

The hypotheses `IsClosed E`, `N.ClosedCellBasics` and `N.UniqueInner` are hypotheses of the
statement; nothing here proves them.

Part (a), the recursive Borel partition inside the closed cells:
* `d1aassign_firstPiece`: for an index set `S` ordered by `ord : α → ℕ`, the piece
  `C s \ ⋃ {C s' : s' ∈ S, ord s' < ord s}`; these pieces are pairwise disjoint when `ord` is
  injective on `S` (`d1aassign_firstPiece_disjoint`), have the same union over `S` as the `C s`
  (`d1aassign_biUnion_firstPiece`, no injectivity needed) and are measurable when `S` is
  countable and every `C s` is measurable (`d1aassign_firstPiece_measurable`).
* `d1aassign_ord N j`: an injection of the countable centre set `𝒵_j` into `ℕ` (finite and empty
  sets allowed); the children of a level-`j` centre are ordered by `d1aassign_ord N (j + 1)`.
* `d1aassign_cell N`: `Q_{0,z}` = the first piece of `C_{0,z}` over `𝒵_0`, and
  `Q_{j+1,w} = Q_{j,parent w} ∩` the first piece of `C_{j+1,w}` over the children of `parent w`
  (the child rule); cells at non-centres are empty.
* Measurability, `Q ⊆ C`, `cell_subset_parent`, disjointness at each level, the exact child
  partition `Q_{j,z} = ⋃_{children} Q_{j+1,w}` and the level cover `⋃ Q_{j,z} = E`.

Part (b): the inner inclusion from the exact cover and the unique-inner property,
`D_{j,z} ⊆ Q_{j,z} ⊆ C_{j,z}`, the closure identity, and `d1a_assignment_proof`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-! ## Ordered first pieces of an indexed family -/

section FirstPiece

variable {α β : Type*}

/-- The part of `C s` not covered by the `C s'` with `s' ∈ S` of smaller order `ord s' < ord s`. -/
def d1aassign_firstPiece (S : Set α) (ord : α → ℕ) (C : α → Set β) (s : α) : Set β :=
  C s \ ⋃ s' ∈ {s' | s' ∈ S ∧ ord s' < ord s}, C s'

theorem d1aassign_firstPiece_subset (S : Set α) (ord : α → ℕ) (C : α → Set β) (s : α) :
    d1aassign_firstPiece S ord C s ⊆ C s :=
  fun _ hx => hx.1

theorem d1aassign_firstPiece_disjoint {S : Set α} {ord : α → ℕ} (hord : InjOn ord S)
    (C : α → Set β) {s s' : α} (hs : s ∈ S) (hs' : s' ∈ S) (hne : s ≠ s') :
    Disjoint (d1aassign_firstPiece S ord C s) (d1aassign_firstPiece S ord C s') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rcases lt_trichotomy (ord s) (ord s') with h | h | h
  · exact hx'.2 (mem_biUnion (x := s) ⟨hs, h⟩ hx.1)
  · exact hne (hord hs hs' h)
  · exact hx.2 (mem_biUnion (x := s') ⟨hs', h⟩ hx'.1)

theorem d1aassign_biUnion_firstPiece (S : Set α) (ord : α → ℕ) (C : α → Set β) :
    (⋃ s ∈ S, d1aassign_firstPiece S ord C s) = ⋃ s ∈ S, C s := by
  classical
  apply Subset.antisymm
  · exact biUnion_mono subset_rfl fun s _ => d1aassign_firstPiece_subset S ord C s
  · intro x hx
    rw [mem_iUnion₂] at hx
    have hex : ∃ m, ∃ s ∈ S, ord s = m ∧ x ∈ C s := by
      obtain ⟨s, hs, hxs⟩ := hx
      exact ⟨ord s, s, hs, rfl, hxs⟩
    obtain ⟨s, hs, hsm, hxs⟩ := Nat.find_spec hex
    refine mem_biUnion hs ⟨hxs, ?_⟩
    intro hmem
    rw [mem_iUnion₂] at hmem
    obtain ⟨s', ⟨hs', hlt⟩, hxs'⟩ := hmem
    have hlt' : ord s' < Nat.find hex := by rw [← hsm]; exact hlt
    exact Nat.find_min hex hlt' ⟨s', hs', rfl, hxs'⟩

theorem d1aassign_firstPiece_measurable [MeasurableSpace β] {S : Set α} (hS : S.Countable)
    (ord : α → ℕ) {C : α → Set β} (hC : ∀ s, MeasurableSet (C s)) (s : α) :
    MeasurableSet (d1aassign_firstPiece S ord C s) :=
  (hC s).diff (MeasurableSet.biUnion (hS.mono fun _ h => h.1) fun s' _ => hC s')

end FirstPiece

/-! ## The recursive assignment -/

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

theorem d1aassign_scale_pos (N : NestedNets E ℓ₀) (j : ℕ) : 0 < coherentScale ℓ₀ j :=
  div_pos N.scale_pos (pow_pos (by norm_num) j)

/-- An injection of the countable centre set `𝒵_j` into `ℕ` (on `𝒵_j`). -/
def d1aassign_ord (N : NestedNets E ℓ₀) (j : ℕ) : Space n → ℕ :=
  Classical.choose (Set.countable_iff_exists_injOn.1 (N.center_countable j))

theorem d1aassign_ord_injOn (N : NestedNets E ℓ₀) (j : ℕ) :
    InjOn (d1aassign_ord N j) (N.center j) :=
  Classical.choose_spec (Set.countable_iff_exists_injOn.1 (N.center_countable j))

open Classical in
/-- The assigned cells: `Q_{0,z} = C_{0,z} \ ⋃_{z' < z} C_{0,z'}` and
`Q_{j+1,w} = Q_{j,z} ∩ (C_{j+1,w} \ ⋃_{w' < w, parent w' = z} C_{j+1,w'})` with `z = parent w`;
empty at non-centres. -/
def d1aassign_cell (N : NestedNets E ℓ₀) : ℕ → Space n → Set (Space n)
  | 0, z =>
    if z ∈ N.center 0 then
      d1aassign_firstPiece (N.center 0) (d1aassign_ord N 0) (N.closedCell 0) z
    else ∅
  | j + 1, w =>
    if w ∈ N.center (j + 1) then
      d1aassign_cell N j (N.parent j w) ∩
        d1aassign_firstPiece (N.children j (N.parent j w)) (d1aassign_ord N (j + 1))
          (N.closedCell (j + 1)) w
    else ∅

theorem d1aassign_cell_zero (N : NestedNets E ℓ₀) {z : Space n} (hz : z ∈ N.center 0) :
    d1aassign_cell N 0 z =
      d1aassign_firstPiece (N.center 0) (d1aassign_ord N 0) (N.closedCell 0) z := by
  rw [d1aassign_cell, ite_eq_left hz]

theorem d1aassign_cell_succ (N : NestedNets E ℓ₀) (j : ℕ) {w : Space n}
    (hw : w ∈ N.center (j + 1)) :
    d1aassign_cell N (j + 1) w =
      d1aassign_cell N j (N.parent j w) ∩
        d1aassign_firstPiece (N.children j (N.parent j w)) (d1aassign_ord N (j + 1))
          (N.closedCell (j + 1)) w := by
  rw [d1aassign_cell, ite_eq_left hw]

theorem d1aassign_cell_of_not_mem (N : NestedNets E ℓ₀) (j : ℕ) {z : Space n}
    (hz : z ∉ N.center j) : d1aassign_cell N j z = ∅ := by
  cases j with
  | zero => rw [d1aassign_cell, ite_eq_right hz]
  | succ j => rw [d1aassign_cell, ite_eq_right hz]

theorem d1aassign_children_subset (N : NestedNets E ℓ₀) (j : ℕ) (z : Space n) :
    N.children j z ⊆ N.center (j + 1) :=
  fun _ h => h.1

/-- Every assigned cell lies in its closed cell. -/
theorem d1aassign_cell_subset_closedCell (N : NestedNets E ℓ₀) :
    ∀ j z, d1aassign_cell N j z ⊆ N.closedCell j z := by
  intro j z
  by_cases hz : z ∈ N.center j
  · cases j with
    | zero =>
      rw [d1aassign_cell_zero N hz]
      exact d1aassign_firstPiece_subset _ _ _ z
    | succ j =>
      rw [d1aassign_cell_succ N j hz]
      exact fun x hx => d1aassign_firstPiece_subset _ _ _ z hx.2
  · rw [d1aassign_cell_of_not_mem N j hz]
    exact empty_subset _

/-- `cell_subset_parent`. -/
theorem d1aassign_cell_subset_parent (N : NestedNets E ℓ₀) :
    ∀ j, ∀ w ∈ N.center (j + 1),
      d1aassign_cell N (j + 1) w ⊆ d1aassign_cell N j (N.parent j w) := by
  intro j w hw
  rw [d1aassign_cell_succ N j hw]
  exact fun x hx => hx.1

/-- `measurable_cell`. -/
theorem d1aassign_measurable_cell (N : NestedNets E ℓ₀) :
    ∀ j z, MeasurableSet (d1aassign_cell N j z) := by
  intro j
  induction j with
  | zero =>
    intro z
    by_cases hz : z ∈ N.center 0
    · rw [d1aassign_cell_zero N hz]
      exact d1aassign_firstPiece_measurable (N.center_countable 0) _
        (fun _ => isClosed_closure.measurableSet) z
    · rw [d1aassign_cell_of_not_mem N 0 hz]
      exact MeasurableSet.empty
  | succ j ih =>
    intro w
    by_cases hw : w ∈ N.center (j + 1)
    · rw [d1aassign_cell_succ N j hw]
      exact (ih _).inter (d1aassign_firstPiece_measurable
        ((N.center_countable (j + 1)).mono (d1aassign_children_subset N j _)) _
        (fun _ => isClosed_closure.measurableSet) w)
    · rw [d1aassign_cell_of_not_mem N (j + 1) hw]
      exact MeasurableSet.empty

/-- `cell_disjoint`. -/
theorem d1aassign_cell_disjoint (N : NestedNets E ℓ₀) :
    ∀ j, ∀ z ∈ N.center j, ∀ z' ∈ N.center j, z ≠ z' →
      Disjoint (d1aassign_cell N j z) (d1aassign_cell N j z') := by
  intro j
  induction j with
  | zero =>
    intro z hz z' hz' hne
    rw [d1aassign_cell_zero N hz, d1aassign_cell_zero N hz']
    exact d1aassign_firstPiece_disjoint (d1aassign_ord_injOn N 0) _ hz hz' hne
  | succ j ih =>
    intro w hw w' hw' hne
    rw [d1aassign_cell_succ N j hw, d1aassign_cell_succ N j hw', Set.disjoint_left]
    intro x hx hx'
    by_cases hp : N.parent j w = N.parent j w'
    · have key := d1aassign_firstPiece_disjoint
        ((d1aassign_ord_injOn N (j + 1)).mono (d1aassign_children_subset N j (N.parent j w')))
        (N.closedCell (j + 1)) (s := w) (s' := w')
        (show w ∈ N.children j (N.parent j w') from ⟨hw, hp⟩)
        (show w' ∈ N.children j (N.parent j w') from ⟨hw', rfl⟩) hne
      rw [hp] at hx
      exact Set.disjoint_left.1 key hx.2 hx'.2
    · exact Set.disjoint_left.1
        (ih _ (N.parent_mem j w hw) _ (N.parent_mem j w' hw') hp) hx.1 hx'.1

/-- The exact child partition: `Q_{j,z} = ⋃_{w child of z} Q_{j+1,w}` (from the child-union identity). -/
theorem d1aassign_cell_eq_biUnion_children (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics)
    (j : ℕ) {z : Space n} (hz : z ∈ N.center j) :
    d1aassign_cell N j z = ⋃ w ∈ N.children j z, d1aassign_cell N (j + 1) w := by
  apply Subset.antisymm
  · intro x hx
    have hxC : x ∈ N.closedCell j z := d1aassign_cell_subset_closedCell N j z hx
    rw [hB.closedCell_children j z hz,
      ← d1aassign_biUnion_firstPiece (N.children j z) (d1aassign_ord N (j + 1))
        (N.closedCell (j + 1)), mem_iUnion₂] at hxC
    rw [mem_iUnion₂]
    obtain ⟨w, hw, hxw⟩ := hxC
    refine ⟨w, hw, ?_⟩
    have hpw : N.parent j w = z := hw.2
    rw [d1aassign_cell_succ N j hw.1, hpw]
    exact ⟨hx, hxw⟩
  · refine iUnion₂_subset fun w hw => ?_
    have hpw : N.parent j w = z := hw.2
    have h := d1aassign_cell_subset_parent N j w hw.1
    rw [hpw] at h
    exact h

/-- `cell_cover`: each level of assigned cells has union exactly `E`. -/
theorem d1aassign_cell_cover (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics) :
    ∀ j, (⋃ z ∈ N.center j, d1aassign_cell N j z) = E := by
  intro j
  apply Subset.antisymm
  · exact iUnion₂_subset fun z _ =>
      (d1aassign_cell_subset_closedCell N j z).trans (hB.closedCell_subset j z)
  · induction j with
    | zero =>
      intro x hx
      have h := hB.closedCell_cover 0 hx
      rw [← d1aassign_biUnion_firstPiece (N.center 0) (d1aassign_ord N 0) (N.closedCell 0),
        mem_iUnion₂] at h
      obtain ⟨z, hz, hxz⟩ := h
      rw [mem_iUnion₂]
      refine ⟨z, hz, ?_⟩
      rw [d1aassign_cell_zero N hz]
      exact hxz
    | succ j ih =>
      intro x hx
      have h := ih hx
      rw [mem_iUnion₂] at h ⊢
      obtain ⟨z, hz, hxz⟩ := h
      rw [d1aassign_cell_eq_biUnion_children N hB j hz, mem_iUnion₂] at hxz
      obtain ⟨w, hw, hxw⟩ := hxz
      exact ⟨w, hw.1, hxw⟩

/-! ## Part (b): inner inclusion, descendants and the closure identity -/

/-- `inner_subset` (lower inclusion): from the exact cover and the unique-inner property. -/
theorem d1aassign_inner_subset (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics)
    (hU : N.UniqueInner) : ∀ j, ∀ z ∈ N.center j,
      E ∩ Metric.ball z (coherentScale ℓ₀ j / 4) ⊆ d1aassign_cell N j z := by
  intro j z hz x hx
  have hxE : x ∈ ⋃ z ∈ N.center j, d1aassign_cell N j z := by
    rw [d1aassign_cell_cover N hB j]
    exact hx.1
  rw [mem_iUnion₂] at hxE
  obtain ⟨z', hz', hxz'⟩ := hxE
  by_cases h : z = z'
  · rw [h]
    exact hxz'
  · exfalso
    have h0 := hU j z hz z' hz' h
    have hmem : x ∈ E ∩ Metric.ball z (coherentScale ℓ₀ j / 4) ∩ N.closedCell j z' :=
      ⟨hx, d1aassign_cell_subset_closedCell N j z' hxz'⟩
    rw [h0] at hmem
    exact hmem

/-- Iterated `cell_subset_parent`: a level-`(j + d)` cell lies in the cell of its level-`j`
ancestor. -/
theorem d1aassign_cell_subset_ancestor (N : NestedNets E ℓ₀) :
    ∀ (j d : ℕ) (w : Space n), w ∈ N.center (j + d) →
      d1aassign_cell N (j + d) w ⊆ d1aassign_cell N j (N.ancestor j d w) := by
  intro j d
  induction d with
  | zero => exact fun _ _ _ hx => hx
  | succ d ih =>
    intro w hw
    exact (d1aassign_cell_subset_parent N (j + d) w hw).trans
      (ih _ (N.parent_mem (j + d) w hw))

/-- `D_{j,z} ⊆ Q_{j,z}`: every descendant centre lies in its own inner ball, hence in its
assigned cell and in the cell of its ancestor. -/
theorem d1aassign_descendants_subset (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics)
    (hU : N.UniqueInner) (j : ℕ) (z : Space n) :
    N.descendants j z ⊆ d1aassign_cell N j z := by
  rintro w ⟨d, hw, rfl⟩
  have hpos : 0 < coherentScale ℓ₀ (j + d) / 4 :=
    div_pos (d1aassign_scale_pos N (j + d)) (by norm_num)
  have hinner := d1aassign_inner_subset N hB hU (j + d) w hw
    ⟨N.center_subset (j + d) hw, Metric.mem_ball_self hpos⟩
  exact d1aassign_cell_subset_ancestor N j d w hw hinner

/-- `closure_cell`: `closure Q_{j,z} = C_{j,z}`. -/
theorem d1aassign_closure_cell (N : NestedNets E ℓ₀) (hB : N.ClosedCellBasics)
    (hU : N.UniqueInner) :
    ∀ j, ∀ z ∈ N.center j, closure (d1aassign_cell N j z) = N.closedCell j z := by
  intro j z _
  apply Subset.antisymm
  · exact closure_minimal (d1aassign_cell_subset_closedCell N j z) isClosed_closure
  · exact closure_mono (d1aassign_descendants_subset N hB hU j z)

/-- **Exact Borel assignment of nested cells** (`AssignmentStatement`). -/
theorem d1a_assignment_proof : AssignmentStatement := by
  intro n E ℓ₀ N _hE hB hU
  exact ⟨{ cell := d1aassign_cell N
           measurable_cell := d1aassign_measurable_cell N
           cell_disjoint := d1aassign_cell_disjoint N
           cell_cover := d1aassign_cell_cover N hB
           closure_cell := d1aassign_closure_cell N hB hU
           inner_subset := d1aassign_inner_subset N hB hU
           cell_subset_parent := d1aassign_cell_subset_parent N }⟩

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
