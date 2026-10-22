import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.Measure.Neck.Selection.Greedy

/-! # The terminal selection exists

Proof of `d1c_selectionExists_proof : CutoffStatement → SelectionExistsStatement`: the terminal
selection and continuing centres, built from the base lemmas `exists_terminal_selection` and
`exists_maximal_net`.

Route. Every entering set lies in the root cell `S`, hence in the compact container
`closedBall q (2 ℓ_*)` (`cell_subset_ball` of the direct partition at the root). At a stage `j`
the cutoff `f = stageCutoff 𝒢` takes only finitely many values `≥ r_j` (by `CutoffStatement` its
values are `0` or scales `r_i`, and `r_i ≥ r_j > 0` forces `i ≤ j`). On an entering set `E' ⊆ S`:

* the base greedy selection `NeckSelection.exists_terminal_selection` gives the terminal centres in
  decreasing remaining cutoff (`IsGreedyPrefix`), after which `f < r_j` on the remainder;
* the base `NeckSelection.exists_maximal_net` gives a finite maximal `κ_net r_j`-separated net of the
  remainder whose open balls cover it.

These choices are made once for every pair `(j, E')` (`d1csel_stage_choice`); the entering sets
are defined by recursion (`d1csel_entering`), the `Choice` reads its stage-`j` data at the entering
set of stage `j - 1` (`d1csel_choice`), and its surviving sets `kept` equal the entering sets
(`d1csel_kept_eq`, by induction). The selection rules then hold stage by stage.

Only the third clause of `CutoffStatement` (every value is `0` or a scale) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section Selection

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The net separation constants `κ_net` are positive. -/
theorem d1csel_sourceSeparation_pos (T : NeckType) : 0 < T.sourceSeparation := by
  cases T <;> norm_num [NeckType.sourceSeparation]

/-- The construction scales are positive. -/
theorem d1csel_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  unfold stageScale coherentScale
  exact div_pos (mul_pos (by norm_num) (d1c_rootScale_pos 𝒢)) (pow_pos (by norm_num) _)

/-- The construction scales are strictly decreasing: `r_j ≤ r_i` forces `i ≤ j`. -/
theorem d1csel_le_of_stageScale_le (𝒢 : GoodRegion P μ k Λ b) {i j : ℕ}
    (h : stageScale 𝒢 j ≤ stageScale 𝒢 i) : i ≤ j := by
  by_contra hij
  have hji : j < i := not_le.mp hij
  have h10 : (10 : ℝ) ^ j < 10 ^ i := pow_lt_pow_right₀ (by norm_num) hji
  have hpos : 0 < 48 * 𝒢.rootScale := mul_pos (by norm_num) (d1c_rootScale_pos 𝒢)
  have hlt : stageScale 𝒢 i < stageScale 𝒢 j := by
    unfold stageScale coherentScale
    exact div_lt_div_of_pos_left hpos (pow_pos (by norm_num) _) h10
  exact absurd h (not_le.mpr hlt)

/-- The root cell lies in the compact container `closedBall q (2 ℓ_*)`. -/
theorem d1csel_rootCell_subset (𝒢 : GoodRegion P μ k Λ b) :
    𝒢.rootCell ⊆ Metric.closedBall 𝒢.root.2 (2 * 𝒢.rootScale) := by
  intro z hz
  have h := P.cell_subset_ball 𝒢.root.1 𝒢.root.2 𝒢.root_isCell hz
  exact Metric.ball_subset_closedBall h

/-- On any set, the cutoff takes only finitely many values `≥ r_j`. -/
theorem d1csel_finite_values (hcut : CutoffStatement) (𝒢 : GoodRegion P μ k Λ b) (j : ℕ)
    (E' : Set (Space n)) :
    (stageCutoff 𝒢 '' E' ∩ Ici (stageScale 𝒢 j)).Finite := by
  refine ((Set.finite_Iic j).image (stageScale 𝒢)).subset ?_
  rintro v ⟨⟨z, -, rfl⟩, hv⟩
  rw [Set.mem_Ici] at hv
  rcases (hcut n E ℓ₀ P μ k Λ b 𝒢).2.2.1 z with h0 | ⟨i, hi⟩
  · rw [h0] at hv
    exact absurd hv (not_le.mpr (d1csel_stageScale_pos 𝒢 j))
  · rw [hi] at hv ⊢
    exact ⟨i, d1csel_le_of_stageScale_le 𝒢 hv, rfl⟩

/-- **The selection rules of one stage** `j` on an entering set `E'`, for the stage data
`(m, t, c, g)`: `t 0, …, t (m-1)` is a greedy terminal prefix in decreasing cutoff with `f ≥ r_j`,
after which `f < r_j` on the remainder `E' \ ⋃_{i<m} P(t i, f(t i))`; `g 0, …, g (c-1)` is a
`κ_net r_j`-separated subset of the remainder whose open `κ_net r_j`-balls cover it. -/
structure d1csel_StageSpec (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) (E' : Set (Space n)) (m : ℕ)
    (t : ℕ → Space n) (c : ℕ) (g : ℕ → Space n) : Prop where
  greedy : NeckSelection.IsGreedyPrefix E' (stageCutoff 𝒢) (stageScale 𝒢 j) m t
  done : ∀ z ∈ E' \ ⋃ (l : ℕ) (_ : l < m), Metric.ball (t l) (stageCutoff 𝒢 (t l)),
    stageCutoff 𝒢 z < stageScale 𝒢 j
  net_mem : ∀ i < c, g i ∈ E' \ ⋃ (l : ℕ) (_ : l < m), Metric.ball (t l) (stageCutoff 𝒢 (t l))
  net_sep : ∀ i < c, ∀ l < c, i ≠ l →
    𝒢.type.sourceSeparation * stageScale 𝒢 j ≤ dist (g i) (g l)
  net_cover : E' \ ⋃ (l : ℕ) (_ : l < m), Metric.ball (t l) (stageCutoff 𝒢 (t l)) ⊆
    ⋃ (i : ℕ) (_ : i < c), Metric.ball (g i) (𝒢.type.sourceSeparation * stageScale 𝒢 j)

/-- One stage of the selection exists on every entering set inside the root cell. -/
theorem d1csel_stage_exists (hcut : CutoffStatement) (𝒢 : GoodRegion P μ k Λ b) (j : ℕ)
    (E' : Set (Space n)) (hE' : E' ⊆ 𝒢.rootCell) :
    ∃ (m : ℕ) (t : ℕ → Space n) (c : ℕ) (g : ℕ → Space n), d1csel_StageSpec 𝒢 j E' m t c g := by
  have : Nonempty (Space n) := ⟨𝒢.root.2⟩
  have hr := d1csel_stageScale_pos 𝒢 j
  have hB : IsCompact (Metric.closedBall 𝒢.root.2 (2 * 𝒢.rootScale)) := isCompact_closedBall _ _
  have hEB : E' ⊆ Metric.closedBall 𝒢.root.2 (2 * 𝒢.rootScale) :=
    hE'.trans (d1csel_rootCell_subset 𝒢)
  obtain ⟨m, t, ht, hdone⟩ := NeckSelection.exists_terminal_selection hB hEB (stageCutoff 𝒢) hr
    (d1csel_finite_values hcut 𝒢 j E')
  obtain ⟨c, g, hgA, hgsep, hcover⟩ := NeckSelection.exists_maximal_net hB
    (A := E' \ ⋃ (l : ℕ) (_ : l < m), Metric.ball (t l) (stageCutoff 𝒢 (t l)))
    (Set.sdiff_subset.trans hEB) (mul_pos (d1csel_sourceSeparation_pos 𝒢.type) hr)
  exact ⟨m, t, c, g, ht, hdone, hgA, hgsep, hcover⟩

/-- The stage data chosen once for every stage `j` and every entering set `E'` (meaningful for
`E' ⊆ S`). -/
theorem d1csel_stage_choice (hcut : CutoffStatement) (𝒢 : GoodRegion P μ k Λ b) :
    ∃ (m : ℕ → Set (Space n) → ℕ) (t : ℕ → Set (Space n) → ℕ → Space n)
      (c : ℕ → Set (Space n) → ℕ) (g : ℕ → Set (Space n) → ℕ → Space n),
      ∀ (j : ℕ) (E' : Set (Space n)), E' ⊆ 𝒢.rootCell →
        d1csel_StageSpec 𝒢 j E' (m j E') (t j E') (c j E') (g j E') := by
  have h : ∀ (j : ℕ) (E' : Set (Space n)), ∃ (m : ℕ) (t : ℕ → Space n) (c : ℕ)
      (g : ℕ → Space n), E' ⊆ 𝒢.rootCell → d1csel_StageSpec 𝒢 j E' m t c g := by
    intro j E'
    by_cases hE : E' ⊆ 𝒢.rootCell
    · obtain ⟨m, t, c, g, h⟩ := d1csel_stage_exists hcut 𝒢 j E' hE
      exact ⟨m, t, c, g, fun _ => h⟩
    · exact ⟨0, fun _ => 𝒢.root.2, 0, fun _ => 𝒢.root.2, fun h => absurd h hE⟩
  choose m t c g hspec using h
  exact ⟨m, t, c, g, hspec⟩

/-- The entering sets of the recursive selection: `F 0 = S` and `F (j+1)` is `F j` minus the
terminal holes of stage `j + 1` chosen on `F j`. -/
def d1csel_entering (𝒢 : GoodRegion P μ k Λ b) (m : ℕ → Set (Space n) → ℕ)
    (t : ℕ → Set (Space n) → ℕ → Space n) : ℕ → Set (Space n)
  | 0 => 𝒢.rootCell
  | j + 1 => d1csel_entering 𝒢 m t j \
      ⋃ (i : ℕ) (_ : i < m (j + 1) (d1csel_entering 𝒢 m t j)),
        Metric.ball (t (j + 1) (d1csel_entering 𝒢 m t j) i)
          (stageCutoff 𝒢 (t (j + 1) (d1csel_entering 𝒢 m t j) i))

/-- The entering sets lie in the root cell. -/
theorem d1csel_entering_subset (𝒢 : GoodRegion P μ k Λ b) (m : ℕ → Set (Space n) → ℕ)
    (t : ℕ → Set (Space n) → ℕ → Space n) (j : ℕ) :
    d1csel_entering 𝒢 m t j ⊆ 𝒢.rootCell := by
  induction j with
  | zero => exact subset_rfl
  | succ j ih => exact Set.sdiff_subset.trans ih

/-- The raw choices: the stage-`j` data are read at the entering set of stage `j - 1`. -/
def d1csel_choice (𝒢 : GoodRegion P μ k Λ b) (m : ℕ → Set (Space n) → ℕ)
    (t : ℕ → Set (Space n) → ℕ → Space n) (c : ℕ → Set (Space n) → ℕ)
    (g : ℕ → Set (Space n) → ℕ → Space n) : Choice n where
  termCount j := m j (d1csel_entering 𝒢 m t (j - 1))
  term j := t j (d1csel_entering 𝒢 m t (j - 1))
  candCount j := c j (d1csel_entering 𝒢 m t (j - 1))
  cand j := g j (d1csel_entering 𝒢 m t (j - 1))

/-- One step of the surviving sets of any choice. -/
theorem d1csel_kept_succ (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    C.kept 𝒢 (j + 1) = C.kept 𝒢 j \
      ⋃ (i : ℕ) (_ : i < C.termCount (j + 1)),
        Metric.ball (C.term (j + 1) i) (stageCutoff 𝒢 (C.term (j + 1) i)) :=
  rfl

/-- The surviving sets of the constructed choice are the entering sets. -/
theorem d1csel_kept_eq (𝒢 : GoodRegion P μ k Λ b) (m : ℕ → Set (Space n) → ℕ)
    (t : ℕ → Set (Space n) → ℕ → Space n) (c : ℕ → Set (Space n) → ℕ)
    (g : ℕ → Set (Space n) → ℕ → Space n) (j : ℕ) :
    (d1csel_choice 𝒢 m t c g).kept 𝒢 j = d1csel_entering 𝒢 m t j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [d1csel_kept_succ, ih]
    rfl

/-- The stage-`(j+1)` data of the constructed choice satisfy the stage rules on its surviving
set `S_j`. -/
theorem d1csel_stageSpec_succ (𝒢 : GoodRegion P μ k Λ b) (m : ℕ → Set (Space n) → ℕ)
    (t : ℕ → Set (Space n) → ℕ → Space n) (c : ℕ → Set (Space n) → ℕ)
    (g : ℕ → Set (Space n) → ℕ → Space n)
    (hspec : ∀ (j : ℕ) (E' : Set (Space n)), E' ⊆ 𝒢.rootCell →
      d1csel_StageSpec 𝒢 j E' (m j E') (t j E') (c j E') (g j E')) (j : ℕ) :
    d1csel_StageSpec 𝒢 (j + 1) ((d1csel_choice 𝒢 m t c g).kept 𝒢 j)
      ((d1csel_choice 𝒢 m t c g).termCount (j + 1)) ((d1csel_choice 𝒢 m t c g).term (j + 1))
      ((d1csel_choice 𝒢 m t c g).candCount (j + 1)) ((d1csel_choice 𝒢 m t c g).cand (j + 1)) := by
  rw [d1csel_kept_eq]
  exact hspec (j + 1) _ (d1csel_entering_subset 𝒢 m t j)

/-- The constructed choice satisfies the selection rules. -/
theorem d1csel_isSelection (𝒢 : GoodRegion P μ k Λ b) (m : ℕ → Set (Space n) → ℕ)
    (t : ℕ → Set (Space n) → ℕ → Space n) (c : ℕ → Set (Space n) → ℕ)
    (g : ℕ → Set (Space n) → ℕ → Space n)
    (hspec : ∀ (j : ℕ) (E' : Set (Space n)), E' ⊆ 𝒢.rootCell →
      d1csel_StageSpec 𝒢 j E' (m j E') (t j E') (c j E') (g j E')) :
    (d1csel_choice 𝒢 m t c g).IsSelection 𝒢 := by
  have hS := d1csel_stageSpec_succ 𝒢 m t c g hspec
  refine
    { term_mem := ?_, term_large := ?_, term_max := ?_, term_done := ?_, cand_mem := ?_,
      cand_separated := ?_, cand_cover := ?_ }
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact (hS j).greedy.mem
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact (hS j).greedy.large
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact (hS j).greedy.max
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [d1csel_kept_succ]
    exact (hS j).done
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [d1csel_kept_succ]
    exact (hS j).net_mem
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact (hS j).net_sep
  · intro j hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [d1csel_kept_succ]
    exact (hS j).net_cover

end Selection

/-- **The terminal selection exists** (`CutoffStatement → SelectionExistsStatement`): every good
region has a `Choice` satisfying `IsSelection`. -/
theorem d1c_selectionExists_proof : CutoffStatement → SelectionExistsStatement := by
  intro hcut
  unfold SelectionExistsStatement
  intro n E ℓ₀ P μ k Λ b 𝒢
  obtain ⟨m, t, c, g, hspec⟩ := d1csel_stage_choice hcut 𝒢
  exact ⟨d1csel_choice 𝒢 m t c g, d1csel_isSelection 𝒢 m t c g hspec⟩

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
