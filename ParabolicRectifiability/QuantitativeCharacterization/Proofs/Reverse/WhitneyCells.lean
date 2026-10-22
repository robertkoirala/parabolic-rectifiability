import ParabolicRectifiability.QuantitativeCharacterization.Statements.ReverseBound
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Maximal

/-! # The Whitney cells

Proves the statement `d2_whitney_cells` with its type `WhitneyCellsStatement`.

Proof idea: the Whitney boxes (`whitneyBoxes Γ`, maximal eligible parabolic dyadic
boxes). A box `B` has `B ⊆ P̄(p_B, D r_B)`, `(A_W - D) r_B ≤ dist(q, Γ)` on `B`, and
`dist(p_B, Γ) ≤ (2A_W + 3D) r_B`. The anchor is a nearest point of `Γ` to `p_B` (closed `Γ` in
the proper space), the scale is `s = (A_W - D) r_B`, and
`C₀ = max 1 ((2A_W + 4D + 1)/(A_W - D))`. The countable box type is re-indexed by `ℕ` through an
injection; unused indices get the empty cell, a fixed anchor of `Γ` and scale `1`.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization.ReverseTree

/-- **`d2_whitney_cells`**, type `WhitneyCellsStatement`. -/
theorem d2_whitney_cells_proof : WhitneyCellsStatement := by
  classical
  intro n
  set a : ℝ := whitneyA n - whitneyD n with ha_def
  have ha : 0 < a := whitneyA_sub_whitneyD_pos n
  set K : ℝ := 2 * whitneyA n + 4 * whitneyD n + 1 with hK_def
  refine ⟨max 1 (K / a), le_max_left _ _, ?_⟩
  intro Γ hΓ hne
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat (ParabolicDyadicBox n)
  -- nearest anchors
  have hnear : ∀ x : Space n, ∃ y ∈ Γ, Metric.infDist x Γ = dist x y :=
    fun x => hΓ.exists_infDist_eq_dist hne x
  let near : Space n → Space n := fun x => Classical.choose (hnear x)
  have hnear_mem : ∀ x, near x ∈ Γ := fun x => (Classical.choose_spec (hnear x)).1
  have hnear_dist : ∀ x, Metric.infDist x Γ = dist x (near x) :=
    fun x => (Classical.choose_spec (hnear x)).2
  -- the index predicate and the chosen box
  let P : ℕ → Prop := fun j => ∃ B ∈ whitneyBoxes Γ, f B = j
  let box : ∀ j, P j → ParabolicDyadicBox n := fun j h => Classical.choose h
  have hbox_mem : ∀ j (h : P j), box j h ∈ whitneyBoxes Γ :=
    fun j h => (Classical.choose_spec h).1
  have hbox_f : ∀ j (h : P j), f (box j h) = j := fun j h => (Classical.choose_spec h).2
  let g₀ : Space n := hne.some
  refine ⟨fun j => if h : P j then (box j h).toSet else ∅,
    fun j => if h : P j then near (box j h).center else g₀,
    fun j => if h : P j then a * (box j h).radius else 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- measurability
    intro j
    by_cases h : P j
    · simp only [h, dite_true]
      exact (box j h).measurableSet_toSet
    · simp only [h, dite_false]
      exact MeasurableSet.empty
  · -- pairwise disjointness
    intro i j hij
    by_cases hi : P i
    · by_cases hj : P j
      · simp only [hi, hj, dite_true]
        refine ParabolicDyadicBox.whitneyBoxes_disjoint (hbox_mem i hi) (hbox_mem j hj) ?_
        intro heq
        apply hij
        rw [← hbox_f i hi, ← hbox_f j hj, heq]
      · simp only [hj, dite_false]
        exact Set.disjoint_empty _
    · simp only [hi, dite_false]
      exact Set.empty_disjoint _
  · -- the cells cover exactly `Γᶜ`
    ext z
    simp only [Set.mem_iUnion, Set.mem_compl_iff]
    constructor
    · rintro ⟨j, hz⟩ hzΓ
      by_cases h : P j
      · simp only [h, dite_true] at hz
        have h1 := ParabolicDyadicBox.le_infDist_of_mem (hbox_mem j h).1 hz
        rw [Metric.infDist_zero_of_mem hzΓ] at h1
        have h2 := mul_pos ha (box j h).radius_pos
        linarith
      · simp only [h, dite_false] at hz
        exact hz
    · intro hz
      obtain ⟨B, hB, hzB⟩ := ParabolicDyadicBox.exists_whitneyBox_mem hΓ hne hz
      have hP : P (f B) := ⟨B, hB, rfl⟩
      refine ⟨f B, ?_⟩
      simp only [hP, dite_true]
      have hBeq : box (f B) hP = B := hf (hbox_f (f B) hP)
      rw [hBeq]
      exact hzB
  · -- anchors lie on `Γ`
    intro j
    by_cases h : P j
    · simp only [h, dite_true]
      exact hnear_mem _
    · simp only [h, dite_false]
      exact hne.some_mem
  · -- positive scales
    intro j
    by_cases h : P j
    · simp only [h, dite_true]
      exact mul_pos ha (box j h).radius_pos
    · simp only [h, dite_false]
      exact one_pos
  · -- containment `Q_j ⊆ P(g_j, C₀ s_j)`
    intro j
    by_cases h : P j
    · simp only [h, dite_true]
      intro y hy
      set B := box j h
      have hr := B.radius_pos
      have h1 : dist y B.center ≤ whitneyD n * B.radius :=
        Metric.mem_closedBall.mp (B.toSet_subset_closedBall hy)
      have h2 : dist B.center (near B.center) ≤
          (2 * whitneyA n + 3 * whitneyD n) * B.radius := by
        rw [← hnear_dist]
        exact ParabolicDyadicBox.infDist_center_le (hbox_mem j h)
      have h3 : dist y (near B.center) ≤ dist y B.center + dist B.center (near B.center) :=
        dist_triangle _ _ _
      have h4 : K * B.radius = K / a * (a * B.radius) := by
        field_simp
      have h5 : K / a * (a * B.radius) ≤ max 1 (K / a) * (a * B.radius) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_pos ha hr).le
      rw [Metric.mem_ball]
      have h7 : K * B.radius = (2 * whitneyA n + 4 * whitneyD n) * B.radius + B.radius := by
        rw [hK_def]
        ring
      have h6 : dist y (near B.center) < K * B.radius := by
        rw [h7]
        linarith
      linarith
    · simp only [h, dite_false]
      exact Set.empty_subset _
  · -- the scale is below the distance to `Γ`
    intro j y hy
    by_cases h : P j
    · simp only [h, dite_true] at hy ⊢
      exact ParabolicDyadicBox.le_infDist_of_mem (hbox_mem j h).1 hy
    · simp only [h, dite_false] at hy
      exact hy.elim

/-- Consumer check: the proof has the statement type. -/
example : WhitneyCellsStatement := d2_whitney_cells_proof

end ParabolicRectifiability.QuantitativeCharacterization.ReverseTree
