import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Geometry

/-! # Maximal eligible boxes form Whitney data

For a closed nonempty `F₀`, eligibility passes to children (see `isWhitneyEligible_of_parent`), so
distinct maximal eligible boxes are disjoint; every point off `F₀` lies in one
(small boxes are eligible, large ancestors are not); and the failure of
eligibility of the parent gives the upper distance bounds. This file assembles these facts as
`exists_whitneyBoxes_data_proof`.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability

theorem whitneyA_eq (m : ℕ) : whitneyA m = 10 ^ 4 * whitneyD m :=
  rfl

theorem whitneyA_sub_whitneyD_pos (m : ℕ) : 0 < whitneyA m - whitneyD m := by
  have := whitneyD_pos m
  rw [whitneyA_eq]
  linarith

namespace ParabolicDyadicBox

variable {m : ℕ} {F₀ : Set (Space m)}

/-- Eligibility passes to children: `A_W r_Q - 2 D_m r_Q/2 > A_W r_Q/2` for the child
radius `r_Q/2`. -/
theorem isWhitneyEligible_of_parent {Q : ParabolicDyadicBox m}
    (h : IsWhitneyEligible F₀ Q.parent) : IsWhitneyEligible F₀ Q := by
  unfold IsWhitneyEligible at h ⊢
  have htri : Metric.infDist Q.parent.center F₀ ≤
      Metric.infDist Q.center F₀ + dist Q.parent.center Q.center :=
    Metric.infDist_le_infDist_add_dist
  have hd := Q.dist_center_parent_center_le_two
  rw [dist_comm] at hd
  rw [parent_radius] at h
  have hDr : 0 < whitneyD m * Q.radius := mul_pos (whitneyD_pos m) Q.radius_pos
  rw [whitneyA_eq] at h ⊢
  linarith

/-- Eligibility passes to all descendants. -/
theorem isWhitneyEligible_of_iterate_parent {Q : ParabolicDyadicBox m} (d : ℕ)
    (h : IsWhitneyEligible F₀ (parent^[d] Q)) : IsWhitneyEligible F₀ Q := by
  induction d generalizing Q with
  | zero => exact h
  | succ d ih =>
    rw [Function.iterate_succ_apply] at h
    exact isWhitneyEligible_of_parent (ih h)

theorem whitneyBoxes_disjoint_of_level_le {Q Q' : ParabolicDyadicBox m}
    (hQ : Q ∈ whitneyBoxes F₀) (hQ' : Q' ∈ whitneyBoxes F₀) (hne : Q ≠ Q')
    (hl : Q.level ≤ Q'.level) : Disjoint Q.toSet Q'.toSet := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz, hz'⟩
  have heq := eq_iterate_parent_of_mem hl hz hz'
  generalize (Q'.level - Q.level).toNat = d at heq
  cases d with
  | zero => exact hne heq
  | succ d =>
    rw [Function.iterate_succ_apply] at heq
    have h1 : IsWhitneyEligible F₀ (parent^[d] Q'.parent) := by
      rw [← heq]
      exact hQ.1
    exact hQ'.2 (isWhitneyEligible_of_iterate_parent d h1)

/-- Distinct maximal eligible boxes are disjoint. -/
theorem whitneyBoxes_disjoint {Q Q' : ParabolicDyadicBox m} (hQ : Q ∈ whitneyBoxes F₀)
    (hQ' : Q' ∈ whitneyBoxes F₀) (hne : Q ≠ Q') : Disjoint Q.toSet Q'.toSet := by
  rcases le_total Q.level Q'.level with hl | hl
  · exact whitneyBoxes_disjoint_of_level_le hQ hQ' hne hl
  · exact (whitneyBoxes_disjoint_of_level_le hQ' hQ hne.symm hl).symm

/-- The lower distance bound `(A_W - D_m) r_Q ≤ dist(q, F₀)` on an eligible box. -/
theorem le_infDist_of_mem {Q : ParabolicDyadicBox m} (hQ : IsWhitneyEligible F₀ Q)
    {q : Space m} (hq : q ∈ Q.toSet) :
    (whitneyA m - whitneyD m) * Q.radius ≤ Metric.infDist q F₀ := by
  have h1 : Metric.infDist Q.center F₀ ≤ Metric.infDist q F₀ + dist Q.center q :=
    Metric.infDist_le_infDist_add_dist
  have h2 : dist Q.center q ≤ whitneyD m * Q.radius := by
    rw [dist_comm]
    exact dist_center_le_of_mem hq
  have h3 : whitneyA m * Q.radius < Metric.infDist Q.center F₀ := hQ
  linarith

/-- The upper center bound from the ineligible parent: `dist(p_Q, F₀) ≤ (2A_W + 3D_m) r_Q`. -/
theorem infDist_center_le {Q : ParabolicDyadicBox m} (hQ : Q ∈ whitneyBoxes F₀) :
    Metric.infDist Q.center F₀ ≤ (2 * whitneyA m + 3 * whitneyD m) * Q.radius := by
  have h1 : Metric.infDist Q.center F₀ ≤
      Metric.infDist Q.parent.center F₀ + dist Q.center Q.parent.center :=
    Metric.infDist_le_infDist_add_dist
  have h2 := Q.dist_center_parent_center_le
  have h3 : Metric.infDist Q.parent.center F₀ ≤ whitneyA m * Q.parent.radius := not_lt.mp hQ.2
  rw [parent_radius] at h3
  linarith

/-- The upper bound `dist(q, F₀) ≤ (2A_W + 4D_m) r_Q` on a Whitney box. -/
theorem infDist_le_of_mem {Q : ParabolicDyadicBox m} (hQ : Q ∈ whitneyBoxes F₀)
    {q : Space m} (hq : q ∈ Q.toSet) :
    Metric.infDist q F₀ ≤ (2 * whitneyA m + 4 * whitneyD m) * Q.radius := by
  have h1 : Metric.infDist q F₀ ≤ Metric.infDist Q.center F₀ + dist q Q.center :=
    Metric.infDist_le_infDist_add_dist
  have h2 := dist_center_le_of_mem hq
  have h3 := infDist_center_le hQ
  linarith

/-- Center separation `max(r_Q, r_Q')/2 ≤ dist(p_Q, p_Q')` of distinct Whitney boxes. -/
theorem max_radius_div_two_le_dist {Q Q' : ParabolicDyadicBox m} (hQ : Q ∈ whitneyBoxes F₀)
    (hQ' : Q' ∈ whitneyBoxes F₀) (hne : Q ≠ Q') :
    max Q.radius Q'.radius / 2 ≤ dist Q.center Q'.center := by
  have hdisj := whitneyBoxes_disjoint hQ hQ' hne
  rw [← not_lt]
  intro hlt
  rcases le_total Q'.radius Q.radius with h | h
  · rw [max_eq_left h] at hlt
    have h1 : Q'.center ∈ Q.toSet :=
      Q.ball_half_subset (by rw [Metric.mem_ball, dist_comm]; exact hlt)
    exact Set.disjoint_left.mp hdisj h1 Q'.center_mem
  · rw [max_eq_right h] at hlt
    have h1 : Q.center ∈ Q'.toSet := Q'.ball_half_subset (by rw [Metric.mem_ball]; exact hlt)
    exact Set.disjoint_left.mp hdisj Q.center_mem h1

/-- Every point off a closed nonempty `F₀` lies in a maximal eligible box. -/
theorem exists_whitneyBox_mem (hF : IsClosed F₀) (hne : F₀.Nonempty) {z : Space m}
    (hz : z ∉ F₀) : ∃ Q ∈ whitneyBoxes F₀, z ∈ Q.toSet := by
  have hδ : 0 < Metric.infDist z F₀ := (hF.notMem_iff_infDist_pos hne).mp hz
  have hAD : 0 < whitneyA m - whitneyD m := whitneyA_sub_whitneyD_pos m
  have hApD : 0 < whitneyA m + whitneyD m := by linarith [whitneyD_pos m]
  -- small boxes at `z` are eligible
  have hsmall : ∀ j : ℤ, (whitneyA m + whitneyD m) * (boxAt j z).radius < Metric.infDist z F₀ →
      IsWhitneyEligible F₀ (boxAt j z) := by
    intro j hj
    have h1 : Metric.infDist z F₀ ≤
        Metric.infDist (boxAt j z).center F₀ + dist z (boxAt j z).center :=
      Metric.infDist_le_infDist_add_dist
    have h2 := dist_center_le_of_mem (mem_boxAt j z)
    show whitneyA m * (boxAt j z).radius < Metric.infDist (boxAt j z).center F₀
    linarith
  -- large boxes at `z` are not eligible
  have hlarge : ∀ j : ℤ, Metric.infDist z F₀ ≤ (whitneyA m - whitneyD m) * (boxAt j z).radius →
      ¬ IsWhitneyEligible F₀ (boxAt j z) := by
    intro j hj hel
    have h1 : Metric.infDist (boxAt j z).center F₀ ≤
        Metric.infDist z F₀ + dist (boxAt j z).center z :=
      Metric.infDist_le_infDist_add_dist
    have h2 : dist (boxAt j z).center z ≤ whitneyD m * (boxAt j z).radius := by
      rw [dist_comm]
      exact dist_center_le_of_mem (mem_boxAt j z)
    have h3 : whitneyA m * (boxAt j z).radius < Metric.infDist (boxAt j z).center F₀ := hel
    linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < Metric.infDist z F₀ / (whitneyA m + whitneyD m) :=
    exists_pow_lt_of_lt_one (div_pos hδ hApD) (by norm_num)
  obtain ⟨n', hn'⟩ : ∃ n : ℕ, Metric.infDist z F₀ / (whitneyA m - whitneyD m) < 2 ^ n :=
    pow_unbounded_of_one_lt _ (by norm_num)
  have hinh : ∃ j : ℤ, IsWhitneyEligible F₀ (boxAt j z) := by
    refine ⟨n, hsmall n ?_⟩
    have hrad : (boxAt (n : ℤ) z).radius = (1 / 2 : ℝ) ^ n := by
      simp only [radius, boxAt_level, zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [hrad]
    rw [lt_div_iff₀ hApD] at hn
    linarith
  have hbdd : ∃ b : ℤ, ∀ j : ℤ, IsWhitneyEligible F₀ (boxAt j z) → b ≤ j := by
    refine ⟨-(n' : ℤ), fun j hj => ?_⟩
    rw [← not_lt]
    intro hlt
    refine hlarge j ?_ hj
    have h1 : (2 : ℝ) ^ (n' : ℤ) ≤ (2 : ℝ) ^ (-j) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_natCast] at h1
    have hrad : (boxAt j z).radius = (2 : ℝ) ^ (-j) := rfl
    rw [hrad]
    rw [div_lt_iff₀ hAD] at hn'
    calc Metric.infDist z F₀ ≤ 2 ^ n' * (whitneyA m - whitneyD m) := hn'.le
      _ = (whitneyA m - whitneyD m) * 2 ^ n' := mul_comm _ _
      _ ≤ (whitneyA m - whitneyD m) * (2 : ℝ) ^ (-j) :=
          mul_le_mul_of_nonneg_left h1 hAD.le
  obtain ⟨j₀, hj₀, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨boxAt j₀ z, ⟨hj₀, fun hpar => ?_⟩, mem_boxAt j₀ z⟩
  rw [parent_eq_boxAt (mem_boxAt j₀ z)] at hpar
  have := hmin _ hpar
  simp only [boxAt_level] at this
  omega

end ParabolicDyadicBox

open ParabolicDyadicBox in
/-- The maximal eligible boxes of a closed nonempty `F₀` as Whitney data, with the boxes'
own cells, centers and radii, `D = D_m` and `a = A_W - D_m`. -/
def whitneyBoxesData {m : ℕ} (F₀ : Set (Space m)) (hF : IsClosed F₀) (hne : F₀.Nonempty) :
    WhitneyData m (whitneyBoxes F₀) F₀ (whitneyD m) (whitneyA m - whitneyD m) where
  cell Q := Q.1.toSet
  center Q := Q.1.center
  radius Q := Q.1.radius
  one_le_D := one_le_whitneyD m
  a_pos := whitneyA_sub_whitneyD_pos m
  radius_pos Q := Q.1.radius_pos
  measurableSet_cell Q := Q.1.measurableSet_toSet
  center_mem Q := Q.1.center_mem
  pairwise_disjoint Q Q' hne := whitneyBoxes_disjoint Q.2 Q'.2 fun h => hne (Subtype.ext h)
  iUnion_cell := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_compl_iff]
    constructor
    · rintro ⟨Q, hz⟩ hzF
      have h1 := le_infDist_of_mem Q.2.1 hz
      rw [Metric.infDist_zero_of_mem hzF] at h1
      have h2 := mul_pos (whitneyA_sub_whitneyD_pos m) Q.1.radius_pos
      linarith
    · intro hz
      obtain ⟨Q, hQ, hzQ⟩ := exists_whitneyBox_mem hF hne hz
      exact ⟨⟨Q, hQ⟩, hzQ⟩
  volume_cell Q := Q.1.volume_toSet
  cell_subset Q := Q.1.toSet_subset_closedBall
  le_infDist Q _ hq := le_infDist_of_mem Q.2.1 hq

/-- **Maximal eligible boxes as Whitney data**: for a compact nonempty `F₀` the maximal
eligible boxes form Whitney data, with the upper distance bounds and center separation. -/
theorem exists_whitneyBoxes_data_proof (m : ℕ) (F₀ : Set (Space m)) (hF₀ : IsCompact F₀)
    (hne : F₀.Nonempty) :
    ∃ W : WhitneyData m (whitneyBoxes F₀) F₀ (whitneyD m) (whitneyA m - whitneyD m),
      (∀ Q, W.cell Q = Q.1.toSet ∧ W.center Q = Q.1.center ∧ W.radius Q = Q.1.radius) ∧
      (∀ Q : whitneyBoxes F₀,
        Metric.infDist Q.1.center F₀ ≤ (2 * whitneyA m + 3 * whitneyD m) * Q.1.radius) ∧
      (∀ Q : whitneyBoxes F₀, ∀ q ∈ Q.1.toSet,
        Metric.infDist q F₀ ≤ (2 * whitneyA m + 4 * whitneyD m) * Q.1.radius) ∧
      (∀ Q Q' : whitneyBoxes F₀, Q ≠ Q' →
        max Q.1.radius Q'.1.radius / 2 ≤ dist Q.1.center Q'.1.center) :=
  ⟨whitneyBoxesData F₀ hF₀.isClosed hne, fun _ => ⟨rfl, rfl, rfl⟩,
    fun Q => ParabolicDyadicBox.infDist_center_le Q.2,
    fun Q _ hq => ParabolicDyadicBox.infDist_le_of_mem Q.2 hq,
    fun Q Q' hne => ParabolicDyadicBox.max_radius_div_two_le_dist Q.2 Q'.2
      fun h => hne (Subtype.ext h)⟩

end ParabolicRectifiability
