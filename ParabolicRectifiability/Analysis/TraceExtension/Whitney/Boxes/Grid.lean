import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Data

/-! # The parabolic dyadic grid

Integer floor-division arithmetic for `ParabolicDyadicBox` (see
`parabolicDyadicBox_geometry_proof`): membership in a box is described by integer floors, the boxes of one
level partition space, a box lies in its parent (floor division by `2` in space
and `4` in time), iterated parents are the ancestors, and boxes of different
levels are nested or disjoint.
-/

noncomputable section

open Set

namespace ParabolicRectifiability

namespace ParabolicDyadicBox

variable {m : ℕ}

theorem eq_iff {Q Q' : ParabolicDyadicBox m} :
    Q = Q' ↔ Q.level = Q'.level ∧ Q.space = Q'.space ∧ Q.time = Q'.time := by
  cases Q
  cases Q'
  simp

/-! ## Radii -/

theorem radius_pos (Q : ParabolicDyadicBox m) : 0 < Q.radius :=
  zpow_pos (by norm_num) _

theorem radius_nonneg (Q : ParabolicDyadicBox m) : 0 ≤ Q.radius :=
  Q.radius_pos.le

theorem radius_eq_of_level_eq {Q Q' : ParabolicDyadicBox m} (h : Q.level = Q'.level) :
    Q.radius = Q'.radius := by
  simp only [radius, h]

theorem parent_level (Q : ParabolicDyadicBox m) : Q.parent.level = Q.level - 1 :=
  rfl

/-- The parent has twice the radius. -/
theorem parent_radius (Q : ParabolicDyadicBox m) : Q.parent.radius = 2 * Q.radius := by
  simp only [radius, parent_level]
  rw [neg_sub, sub_eq_add_neg, zpow_add₀ two_ne_zero, zpow_one]

/-- Smaller levels have larger radii. -/
theorem radius_le_radius_of_level_le {Q Q' : ParabolicDyadicBox m} (h : Q.level ≤ Q'.level) :
    Q'.radius ≤ Q.radius :=
  zpow_le_zpow_right₀ (by norm_num) (neg_le_neg h)

/-! ## Membership through integer floors -/

theorem floor_div_eq_iff {x r : ℝ} (hr : 0 < r) (k : ℤ) :
    ⌊x / r⌋ = k ↔ (k : ℝ) * r ≤ x ∧ x < ((k : ℝ) + 1) * r := by
  rw [Int.floor_eq_iff, le_div_iff₀ hr, div_lt_iff₀ hr]

/-- A point lies in a box iff the integer floors of its rescaled coordinates are the
box's corner indices. -/
theorem mem_toSet_iff {Q : ParabolicDyadicBox m} {z : Space m} :
    z ∈ Q.toSet ↔
      (∀ i, ⌊z.1 i / Q.radius⌋ = Q.space i) ∧ ⌊z.2.val / Q.radius ^ 2⌋ = Q.time := by
  simp only [floor_div_eq_iff Q.radius_pos, floor_div_eq_iff (pow_pos Q.radius_pos 2)]
  exact Iff.rfl

/-- The level-`j` box containing `z`. -/
def boxAt (j : ℤ) (z : Space m) : ParabolicDyadicBox m where
  level := j
  space := fun i => ⌊z.1 i / (2 : ℝ) ^ (-j)⌋
  time := ⌊z.2.val / ((2 : ℝ) ^ (-j)) ^ 2⌋

theorem boxAt_level (j : ℤ) (z : Space m) : (boxAt j z).level = j :=
  rfl

theorem mem_boxAt (j : ℤ) (z : Space m) : z ∈ (boxAt j z).toSet :=
  mem_toSet_iff.mpr ⟨fun _ => rfl, rfl⟩

/-- Two boxes of the same level with a common point are equal. -/
theorem eq_of_mem_of_level_eq {Q Q' : ParabolicDyadicBox m} {z : Space m}
    (hl : Q.level = Q'.level) (hz : z ∈ Q.toSet) (hz' : z ∈ Q'.toSet) : Q = Q' := by
  have hr : Q.radius = Q'.radius := radius_eq_of_level_eq hl
  rw [mem_toSet_iff] at hz hz'
  rw [eq_iff]
  refine ⟨hl, funext fun i => ?_, ?_⟩
  · rw [← hz.1 i, ← hz'.1 i, hr]
  · rw [← hz.2, ← hz'.2, hr]

/-- At each level the boxes partition space. -/
theorem existsUnique_level_mem (j : ℤ) (z : Space m) :
    ∃! Q : ParabolicDyadicBox m, Q.level = j ∧ z ∈ Q.toSet :=
  ⟨boxAt j z, ⟨rfl, mem_boxAt j z⟩, fun _ hQ =>
    eq_of_mem_of_level_eq hQ.1 hQ.2 (mem_boxAt j z)⟩

theorem eq_boxAt_of_mem {Q : ParabolicDyadicBox m} {z : Space m} (hz : z ∈ Q.toSet) :
    Q = boxAt Q.level z :=
  eq_of_mem_of_level_eq rfl hz (mem_boxAt _ z)

/-! ## The parent -/

/-- Floor division of the corner index by a positive integer `b`. -/
theorem floor_div_mul_eq_ediv {x r : ℝ} (hr : 0 < r) {k b : ℤ} (hb : 0 < b)
    (h : ⌊x / r⌋ = k) : ⌊x / ((b : ℝ) * r)⌋ = k / b := by
  rw [floor_div_eq_iff hr] at h
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [floor_div_eq_iff (mul_pos hb' hr)]
  have h1 : ((k / b : ℤ) : ℝ) * b ≤ k := by exact_mod_cast Int.ediv_mul_le k hb.ne'
  have h2 : (k : ℝ) + 1 ≤ (((k / b : ℤ) : ℝ) + 1) * b := by
    have h' : k + 1 ≤ (k / b + 1) * b := Int.lt_iff_add_one_le.mp (Int.lt_ediv_add_one_mul_self k hb)
    exact_mod_cast h'
  constructor
  · calc ((k / b : ℤ) : ℝ) * ((b : ℝ) * r) = (((k / b : ℤ) : ℝ) * b) * r := by ring
      _ ≤ (k : ℝ) * r := mul_le_mul_of_nonneg_right h1 hr.le
      _ ≤ x := h.1
  · calc x < ((k : ℝ) + 1) * r := h.2
      _ ≤ ((((k / b : ℤ) : ℝ) + 1) * b) * r := mul_le_mul_of_nonneg_right h2 hr.le
      _ = (((k / b : ℤ) : ℝ) + 1) * ((b : ℝ) * r) := by ring

/-- A box lies in its parent. -/
theorem toSet_subset_parent (Q : ParabolicDyadicBox m) : Q.toSet ⊆ Q.parent.toSet := by
  intro z hz
  rw [mem_toSet_iff] at hz ⊢
  have hr : Q.parent.radius = ((2 : ℤ) : ℝ) * Q.radius := by
    rw [parent_radius]
    norm_num
  have hr2 : Q.parent.radius ^ 2 = ((4 : ℤ) : ℝ) * Q.radius ^ 2 := by
    rw [parent_radius]
    push_cast
    ring
  refine ⟨fun i => ?_, ?_⟩
  · rw [hr]
    exact floor_div_mul_eq_ediv Q.radius_pos (by norm_num) (hz.1 i)
  · rw [hr2]
    exact floor_div_mul_eq_ediv (pow_pos Q.radius_pos 2) (by norm_num) hz.2

/-- The parent is the box of the previous level containing any point of `Q`. -/
theorem parent_eq_boxAt {Q : ParabolicDyadicBox m} {z : Space m} (hz : z ∈ Q.toSet) :
    Q.parent = boxAt (Q.level - 1) z :=
  eq_of_mem_of_level_eq rfl (Q.toSet_subset_parent hz) (mem_boxAt _ z)

/-! ## Ancestors and nesting -/

theorem iterate_parent_level (Q : ParabolicDyadicBox m) (d : ℕ) :
    (parent^[d] Q).level = Q.level - d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', parent_level, ih]
    push_cast
    ring

theorem toSet_subset_iterate_parent (Q : ParabolicDyadicBox m) (d : ℕ) :
    Q.toSet ⊆ (parent^[d] Q).toSet := by
  induction d with
  | zero => exact subset_rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (toSet_subset_parent _)

/-- A box of a coarser (or equal) level meeting `Q'` is an iterated parent of `Q'`. -/
theorem eq_iterate_parent_of_mem {Q Q' : ParabolicDyadicBox m} {z : Space m}
    (hl : Q.level ≤ Q'.level) (hz : z ∈ Q.toSet) (hz' : z ∈ Q'.toSet) :
    Q = parent^[(Q'.level - Q.level).toNat] Q' := by
  refine eq_of_mem_of_level_eq ?_ hz (toSet_subset_iterate_parent Q' _ hz')
  rw [iterate_parent_level, Int.toNat_of_nonneg (sub_nonneg.mpr hl)]
  ring

/-- Boxes of different levels are nested or disjoint. -/
theorem subset_or_disjoint {Q Q' : ParabolicDyadicBox m} (hl : Q.level ≤ Q'.level) :
    Q'.toSet ⊆ Q.toSet ∨ Disjoint Q.toSet Q'.toSet := by
  by_cases h : (Q.toSet ∩ Q'.toSet).Nonempty
  · obtain ⟨z, hz, hz'⟩ := h
    left
    have hsub := toSet_subset_iterate_parent Q' (Q'.level - Q.level).toNat
    rwa [← eq_iterate_parent_of_mem hl hz hz'] at hsub
  · right
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)

end ParabolicDyadicBox

end ParabolicRectifiability
