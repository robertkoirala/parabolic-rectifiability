import ParabolicRectifiability.Measure.Neck.Construction

/-!
# Kept sets, stopping centers and the core of the source construction

Helpers for the region and core statements of the neck construction, for the constructed
data of `Construction`:

* the kept sets `S_j` decrease, lie in `S`, avoid every terminal ball `P(c, f(c))` and every
  collapsed ball `P(g, 5 r_j)` of their own stage, and are covered by the `κ r_j`-balls of
  the continuing candidates of that stage;
* every stopping center has a *stage witness* `ms4_StopAt j c d`: it is a terminal center or a
  noncontinuing candidate of stage `j ≥ 1` with the exact radius `d = radius c`;
* two distinct stopping centers are `1/20 max(d, d')`-separated, and a stopping center is
  `d`-separated from the limit set `⋂_j closure(S_j)`;
* the core `{c ∈ 𝒞 : d_c = 0}` is exactly the limit set `⋂_j closure(S_j)`, and every core
  point lies within `κ r_j ≤ r_j` of a continuing candidate of every positive stage.

Only the selection rules `IsSourceConstruction` and `R > 0` are used; no energy bound and
no stage uniqueness. The names carry the prefix `ms4_`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Stage scales -/

namespace NeckType

theorem ms4_quarter_le_sourceSeparation (T : NeckType) : (1 / 4 : ℝ) ≤ T.sourceSeparation := by
  cases T
  · show (1 / 4 : ℝ) ≤ 1 / 4
    exact le_rfl
  · show (1 / 4 : ℝ) ≤ 1
    norm_num

theorem ms4_rootRadius_le (T : NeckType) {R : ℝ} (hR : 0 < R) : T.rootRadius R ≤ 8 * R := by
  cases T
  · show 8 * R ≤ 8 * R
    exact le_rfl
  · show 4 * R ≤ 8 * R
    linarith

end NeckType

namespace SourceSetup

variable {n : ℕ} (P : SourceSetup n) (T : NeckType)

theorem ms4_scale_zero : P.scale T 0 = T.rootRadius P.R := by
  simp only [scale, coherentScale, pow_zero, div_one]

theorem ms4_scale_succ (j : ℕ) : P.scale T (j + 1) = P.scale T j / 10 := by
  simp only [scale, coherentScale, pow_succ, div_div]

theorem ms4_scale_anti (hR : 0 < P.R) : Antitone (P.scale T) :=
  antitone_nat_of_succ_le fun j => by
    rw [ms4_scale_succ]
    have := P.scale_pos T hR j
    linarith

theorem ms4_scale_le_div_ten (hR : 0 < P.R) {j j' : ℕ} (h : j < j') :
    P.scale T j' ≤ P.scale T j / 10 := by
  rw [← ms4_scale_succ]
  exact P.ms4_scale_anti T hR (Nat.succ_le_of_lt h)

theorem ms4_five_scale_le (hR : 0 < P.R) {j : ℕ} (hj : 1 ≤ j) : 5 * P.scale T j ≤ 4 * P.R := by
  have h1 : P.scale T j ≤ P.scale T 1 := P.ms4_scale_anti T hR hj
  have h2 : P.scale T 1 = T.rootRadius P.R / 10 := by
    simp only [scale, coherentScale, pow_one]
  have h3 := T.ms4_rootRadius_le hR
  rw [h2] at h1
  linarith

theorem ms4_tendsto_scale : Tendsto (fun m : ℕ => P.scale T (m + 1)) atTop (𝓝 0) := by
  have h10 : Tendsto (fun m : ℕ => (10 : ℝ) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp (tendsto_add_atTop_nat 1)
  show Tendsto (fun m : ℕ => T.rootRadius P.R / 10 ^ (m + 1)) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop h10

end SourceSetup

namespace ConstructionData

variable {n k : ℕ} {T : NeckType} (D : ConstructionData n k T) (P : SourceSetup n)

/-! ## Kept sets -/

theorem ms4_kept_zero : D.kept P 0 = D.tubeSet P := rfl

theorem ms4_kept_succ (j : ℕ) : D.kept P (j + 1) = D.stageKept P (j + 1) (D.kept P j) := rfl

theorem ms4_entering_succ (j : ℕ) : D.entering P (j + 1) = D.kept P j := by
  simp only [entering, Nat.add_sub_cancel]

theorem ms4_afterTerm_subset (j : ℕ) (E : Set (Space n)) : D.afterTerm P j E ⊆ E :=
  sdiff_subset

theorem ms4_afterColl_subset (j : ℕ) (E : Set (Space n)) :
    D.afterColl P j E ⊆ D.afterTerm P j E :=
  sdiff_subset

theorem ms4_stageKept_subset (j : ℕ) (E : Set (Space n)) :
    D.stageKept P j E ⊆ D.afterColl P j E := by
  intro z hz
  rw [stageKept, mem_iUnion₂] at hz
  obtain ⟨i, -, hz⟩ := hz
  exact hz.1.1

theorem ms4_kept_succ_subset (j : ℕ) : D.kept P (j + 1) ⊆ D.kept P j := by
  rw [ms4_kept_succ]
  exact ((D.ms4_stageKept_subset P _ _).trans (D.ms4_afterColl_subset P _ _)).trans
    (D.ms4_afterTerm_subset P _ _)

theorem ms4_kept_anti : Antitone (D.kept P) :=
  antitone_nat_of_succ_le (D.ms4_kept_succ_subset P)

theorem ms4_kept_subset_S (j : ℕ) : D.kept P j ⊆ P.S := by
  refine Subset.trans (D.ms4_kept_anti P (Nat.zero_le j)) ?_
  rw [ms4_kept_zero]
  exact inter_subset_left

theorem ms4_entering_subset_S (j : ℕ) : D.entering P j ⊆ P.S :=
  D.ms4_kept_subset_S P (j - 1)

theorem ms4_kept_subset_afterColl {j : ℕ} (hj : 1 ≤ j) :
    D.kept P j ⊆ D.afterColl P j (D.entering P j) := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [ms4_entering_succ, ms4_kept_succ]
  exact D.ms4_stageKept_subset P _ _

theorem ms4_kept_subset_afterTerm {j : ℕ} (hj : 1 ≤ j) :
    D.kept P j ⊆ D.afterTerm P j (D.entering P j) :=
  (D.ms4_kept_subset_afterColl P hj).trans (D.ms4_afterColl_subset P _ _)

theorem ms4_kept_subset_contBalls {j : ℕ} (hj : 1 ≤ j) :
    D.kept P j ⊆ ⋃ (i : ℕ) (_ : i < D.candCount j ∧ D.IsContinuing P j i),
      Metric.ball (D.cand j i) (T.sourceSeparation * P.scale T j) := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  intro z hz
  rw [ms4_kept_succ, stageKept, mem_iUnion₂] at hz
  obtain ⟨i, hi, hz⟩ := hz
  exact mem_iUnion₂.2 ⟨i, hi, hz.1.2.1⟩

theorem ms4_term_ball_disjoint {j : ℕ} (hj : 1 ≤ j) {i : ℕ} (hi : i < D.termCount j) :
    Disjoint (Metric.ball (D.term j i) (P.f (D.term j i))) (D.kept P j) := by
  rw [Set.disjoint_left]
  intro y hy hk
  exact (D.ms4_kept_subset_afterTerm P hj hk).2 (mem_iUnion₂.2 ⟨i, hi, hy⟩)

theorem ms4_coll_ball_disjoint {j : ℕ} (hj : 1 ≤ j) {i : ℕ} (hi : i < D.candCount j)
    (hc : ¬ D.IsContinuing P j i) :
    Disjoint (Metric.ball (D.cand j i) (5 * P.scale T j)) (D.kept P j) := by
  rw [Set.disjoint_left]
  intro y hy hk
  exact (D.ms4_kept_subset_afterColl P hj hk).2 (mem_iUnion₂.2 ⟨i, ⟨hi, hc⟩, hy⟩)

theorem ms4_cutoff_lt_of_mem_kept (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j)
    {y : Space n} (hy : y ∈ D.kept P j) : P.f y < P.scale T j :=
  hD.term_done j hj y (D.ms4_kept_subset_afterTerm P hj hy)

/-! ## Stage witnesses of stopping centers -/

/-- `c` is a stopping center witnessed at stage `j ≥ 1` with radius `d`: a terminal center
`term j i` with `d = f(c)`, or a noncontinuing candidate `cand j i` with `d = 5 r_j`. -/
def ms4_StopAt (j : ℕ) (c : Space n) (d : ℝ) : Prop :=
  1 ≤ j ∧ ((∃ i, i < D.termCount j ∧ D.term j i = c ∧ d = P.f c) ∨
    ∃ i, i < D.candCount j ∧ ¬ D.IsContinuing P j i ∧ D.cand j i = c ∧ d = 5 * P.scale T j)

theorem ms4_exists_stopAt {c : Space n} (hc : D.IsTermCenter c ∨ D.IsCollCenter P c) :
    ∃ j, D.ms4_StopAt P j c (D.radius P c) := by
  by_cases ht : D.IsTermCenter c
  · have hr : D.radius P c = P.f c := by rw [radius, ite_eq_left ht]
    obtain ⟨j, hj, i, hi, hci⟩ := ht
    exact ⟨j, hj, Or.inl ⟨i, hi, hci, hr⟩⟩
  · have hcc : D.IsCollCenter P c := hc.resolve_left ht
    have hr : D.radius P c = 5 * P.scale T (D.collStage P c) := by
      rw [radius, ite_eq_right ht, ite_eq_left hcc]
    have hs : D.collStage P c = Classical.choose hcc := by rw [collStage, dite_eq_left hcc]
    obtain ⟨hj, i, hi, hni, hci, -⟩ := Classical.choose_spec hcc
    refine ⟨D.collStage P c, ?_, Or.inr ⟨i, ?_, ?_, ?_, hr⟩⟩
    · rw [hs]
      exact hj
    · rw [hs]
      exact hi
    · rw [hs]
      exact hni
    · rw [hs]
      exact hci

theorem ms4_stop_of_radius_pos {c : Space n} (hc : 0 < D.radius P c) :
    D.IsTermCenter c ∨ D.IsCollCenter P c := by
  by_contra h
  rw [radius, ite_eq_right (fun h' => h (Or.inl h')), ite_eq_right (fun h' => h (Or.inr h'))] at hc
  exact lt_irrefl _ hc

theorem ms4_radius_eq_zero_of_not {c : Space n}
    (h : ¬ (D.IsTermCenter c ∨ D.IsCollCenter P c)) : D.radius P c = 0 := by
  rw [radius, ite_eq_right (fun h' => h (Or.inl h')), ite_eq_right (fun h' => h (Or.inr h'))]

variable {D P}

theorem ms4_StopAt.mem_entering (hD : D.IsSourceConstruction P) {j : ℕ} {c : Space n} {d : ℝ}
    (h : D.ms4_StopAt P j c d) : c ∈ D.entering P j := by
  obtain ⟨hj, ⟨i, hi, rfl, -⟩ | ⟨i, hi, -, rfl, -⟩⟩ := h
  · exact (hD.term_mem j hj i hi).1
  · exact D.ms4_afterTerm_subset P _ _ (hD.cand_mem j hj i hi)

theorem ms4_StopAt.scale_le (hD : D.IsSourceConstruction P) (hR : 0 < P.R) {j : ℕ}
    {c : Space n} {d : ℝ} (h : D.ms4_StopAt P j c d) : P.scale T j ≤ d := by
  obtain ⟨hj, ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, -, -, rfl⟩⟩ := h
  · exact hD.term_large j hj i hi
  · have := P.scale_pos T hR j
    linarith

theorem ms4_StopAt.pos (hD : D.IsSourceConstruction P) (hR : 0 < P.R) {j : ℕ}
    {c : Space n} {d : ℝ} (h : D.ms4_StopAt P j c d) : 0 < d :=
  (P.scale_pos T hR j).trans_le (h.scale_le hD hR)

theorem ms4_StopAt.le_four (hD : D.IsSourceConstruction P) (hP : P.IsAdmissible) {j : ℕ}
    {c : Space n} {d : ℝ} (h : D.ms4_StopAt P j c d) : d ≤ 4 * P.R := by
  have hcS : c ∈ P.S := D.ms4_entering_subset_S P j (h.mem_entering hD)
  obtain ⟨hj, ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, -, -, rfl⟩⟩ := h
  · have := hP.cutoff.le_radius _ hcS
    have := hP.R_pos
    linarith
  · exact P.ms4_five_scale_le T hP.R_pos hj

theorem ms4_StopAt.disjoint {j : ℕ} {c : Space n} {d : ℝ}
    (h : D.ms4_StopAt P j c d) : Disjoint (Metric.ball c d) (D.kept P j) := by
  obtain ⟨hj, ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, hni, rfl, rfl⟩⟩ := h
  · exact D.ms4_term_ball_disjoint P hj hi
  · exact D.ms4_coll_ball_disjoint P hj hi hni

/-- A stopping center of stage `j` is `d`-separated from `closure(S_{j'})`, `j' ≥ j`. -/
theorem ms4_StopAt.le_dist_of_mem_closure {j : ℕ}
    {c : Space n} {d : ℝ} (h : D.ms4_StopAt P j c d) {j' : ℕ} (hjj : j ≤ j') {y : Space n}
    (hy : y ∈ closure (D.kept P j')) : d ≤ dist c y := by
  have hy' : y ∈ closure (D.kept P j) := closure_mono (D.ms4_kept_anti P hjj) hy
  have hdisj := h.disjoint.closure_right Metric.isOpen_ball
  have hy'' : y ∉ Metric.ball c d := fun hb => Set.disjoint_left.1 hdisj hb hy'
  rw [Metric.mem_ball, not_lt, dist_comm] at hy''
  exact hy''

/-- A stopping center of a later stage `j' > j ≥ 1` has radius `< r_j`. -/
theorem ms4_StopAt.lt_scale_of_lt (hD : D.IsSourceConstruction P) (hR : 0 < P.R) {j j' : ℕ}
    {c' : Space n} {d' : ℝ} (h' : D.ms4_StopAt P j' c' d') (hj : 1 ≤ j) (hjj : j < j') :
    d' < P.scale T j := by
  have hc' : c' ∈ D.kept P j :=
    D.ms4_kept_anti P (show j ≤ j' - 1 by omega) (h'.mem_entering hD)
  obtain ⟨-, ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, -, -, rfl⟩⟩ := h'
  · exact D.ms4_cutoff_lt_of_mem_kept P hD hj hc'
  · have h1 := P.ms4_scale_le_div_ten T hR hjj
    have h2 := P.scale_pos T hR j
    linarith

theorem ms4_max_bound {a b x : ℝ} (ha : a / 20 ≤ x) (hb : b / 20 ≤ x) :
    1 / 20 * max a b ≤ x := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab]
    linarith
  · rw [max_eq_left hab]
    linarith

/-- Stopping separation for stage witnesses with `j ≤ j'`. -/
theorem ms4_StopAt.separation_of_le (hD : D.IsSourceConstruction P) (hR : 0 < P.R)
    {j j' : ℕ} {c c' : Space n} {d d' : ℝ} (h : D.ms4_StopAt P j c d)
    (h' : D.ms4_StopAt P j' c' d') (hcc : c ≠ c') (hjj : j ≤ j') :
    1 / 20 * max d d' ≤ dist c c' := by
  have hd := h.scale_le hD hR
  have hrj := P.scale_pos T hR j
  have hκ := T.ms4_quarter_le_sourceSeparation
  rcases hjj.lt_or_eq with hlt | rfl
  · have hc' : c' ∈ D.kept P j :=
      D.ms4_kept_anti P (show j ≤ j' - 1 by omega) (h'.mem_entering hD)
    have h1 : d ≤ dist c c' := h.le_dist_of_mem_closure le_rfl (subset_closure hc')
    have h2 : d' < P.scale T j := h'.lt_scale_of_lt hD hR h.1 hlt
    exact ms4_max_bound (by linarith) (by linarith)
  · obtain ⟨hj, ⟨i, hi, rfl, rfl⟩ | ⟨i, hi, hni, rfl, rfl⟩⟩ := h <;>
      obtain ⟨-, ⟨i', hi', rfl, rfl⟩ | ⟨i', hi', hni', rfl, rfl⟩⟩ := h'
    · -- two terminal centers of one stage
      have hii : i ≠ i' := fun e => hcc (by rw [e])
      rcases lt_or_gt_of_ne hii with hii | hii
      · have hmem := hD.term_mem j hj i' hi'
        have h1 : P.f (D.term j i) ≤ dist (D.term j i) (D.term j i') := by
          have : D.term j i' ∉ Metric.ball (D.term j i) (P.f (D.term j i)) :=
            fun hb => hmem.2 (mem_iUnion₂.2 ⟨i, hii, hb⟩)
          rw [Metric.mem_ball, not_lt, dist_comm] at this
          exact this
        have h2 : P.f (D.term j i') ≤ P.f (D.term j i) := by
          refine hD.term_max j hj i hi _ ⟨hmem.1, fun hU => hmem.2 ?_⟩
          obtain ⟨l, hl, hb⟩ := mem_iUnion₂.1 hU
          exact mem_iUnion₂.2 ⟨l, hl.trans hii, hb⟩
        have h3 := hD.term_large j hj i hi
        exact ms4_max_bound (by linarith) (by linarith)
      · have hmem := hD.term_mem j hj i hi
        have h1 : P.f (D.term j i') ≤ dist (D.term j i) (D.term j i') := by
          have : D.term j i ∉ Metric.ball (D.term j i') (P.f (D.term j i')) :=
            fun hb => hmem.2 (mem_iUnion₂.2 ⟨i', hii, hb⟩)
          rw [Metric.mem_ball, not_lt] at this
          exact this
        have h2 : P.f (D.term j i) ≤ P.f (D.term j i') := by
          refine hD.term_max j hj i' hi' _ ⟨hmem.1, fun hU => hmem.2 ?_⟩
          obtain ⟨l, hl, hb⟩ := mem_iUnion₂.1 hU
          exact mem_iUnion₂.2 ⟨l, hl.trans hii, hb⟩
        have h3 := hD.term_large j hj i' hi'
        exact ms4_max_bound (by linarith) (by linarith)
    · -- terminal `c`, collapsed `c'`
      have hmem := hD.cand_mem j hj i' hi'
      have h1 : P.f (D.term j i) ≤ dist (D.term j i) (D.cand j i') := by
        have : D.cand j i' ∉ Metric.ball (D.term j i) (P.f (D.term j i)) :=
          fun hb => hmem.2 (mem_iUnion₂.2 ⟨i, hi, hb⟩)
        rw [Metric.mem_ball, not_lt, dist_comm] at this
        exact this
      have h3 := hD.term_large j hj i hi
      exact ms4_max_bound (by linarith) (by linarith)
    · -- collapsed `c`, terminal `c'`
      have hmem := hD.cand_mem j hj i hi
      have h1 : P.f (D.term j i') ≤ dist (D.cand j i) (D.term j i') := by
        have : D.cand j i ∉ Metric.ball (D.term j i') (P.f (D.term j i')) :=
          fun hb => hmem.2 (mem_iUnion₂.2 ⟨i', hi', hb⟩)
        rw [Metric.mem_ball, not_lt] at this
        exact this
      have h3 := hD.term_large j hj i' hi'
      exact ms4_max_bound (by linarith) (by linarith)
    · -- two collapsed centers of one stage
      have hii : i ≠ i' := fun e => hcc (by rw [e])
      have h1 := hD.cand_separated j hj i hi i' hi' hii
      have h2 : P.scale T j / 4 ≤ T.sourceSeparation * P.scale T j := by nlinarith
      exact ms4_max_bound (by linarith) (by linarith)

/-- Stopping separation `1/20 max(d, d')` for any two distinct stage witnesses. -/
theorem ms4_StopAt.separation (hD : D.IsSourceConstruction P) (hR : 0 < P.R)
    {j j' : ℕ} {c c' : Space n} {d d' : ℝ} (h : D.ms4_StopAt P j c d)
    (h' : D.ms4_StopAt P j' c' d') (hcc : c ≠ c') :
    1 / 20 * max d d' ≤ dist c c' := by
  rcases le_total j j' with hjj | hjj
  · exact h.separation_of_le hD hR h' hcc hjj
  · have := h'.separation_of_le hD hR h hcc.symm hjj
    rwa [max_comm, dist_comm] at this

/-! ## The core -/

theorem ms4_isClosed_coreLimit : IsClosed (D.coreLimit P) :=
  isClosed_iInter fun _ => isClosed_closure

theorem ms4_not_stop_of_mem_coreLimit (hD : D.IsSourceConstruction P) (hR : 0 < P.R)
    {z : Space n} (hz : z ∈ D.coreLimit P) : ¬ (D.IsTermCenter z ∨ D.IsCollCenter P z) := by
  intro hst
  obtain ⟨j, h⟩ := D.ms4_exists_stopAt P hst
  have hle := h.le_dist_of_mem_closure le_rfl (mem_iInter.1 hz j)
  rw [dist_self] at hle
  exact lt_irrefl _ ((h.pos hD hR).trans_le hle)

theorem ms4_mem_coreLimit_of_mem_centers (hD : D.IsSourceConstruction P) (hR : 0 < P.R)
    {z : Space n} (hz : z ∈ D.centers P) (h0 : D.radius P z = 0) : z ∈ D.coreLimit P := by
  rcases hz with hz | hz
  · exact hz
  · obtain ⟨j, h⟩ := D.ms4_exists_stopAt P hz
    have := h.pos hD hR
    rw [h0] at this
    exact absurd this (lt_irrefl 0)

/-- The core is the limit set `C₀ = ⋂_j closure(S_j)`. -/
theorem ms4_core_eq_coreLimit (hD : D.IsSourceConstruction P) (hR : 0 < P.R) :
    D.core P = D.coreLimit P := by
  ext z
  constructor
  · rintro ⟨hz, h0⟩
    exact ms4_mem_coreLimit_of_mem_centers hD hR hz h0
  · intro hz
    exact ⟨mem_union_left _ hz,
      D.ms4_radius_eq_zero_of_not P (ms4_not_stop_of_mem_coreLimit hD hR hz)⟩

/-- A point of `closure(S_j)`, `j ≥ 1`, lies within `κ r_j` of a continuing candidate of
stage `j`. -/
theorem ms4_exists_cont_near {j : ℕ} (hj : 1 ≤ j) {z : Space n}
    (hz : z ∈ closure (D.kept P j)) :
    ∃ i, i < D.candCount j ∧ D.IsContinuing P j i ∧
      dist z (D.cand j i) ≤ T.sourceSeparation * P.scale T j := by
  set s : Set ℕ := {i | i < D.candCount j ∧ D.IsContinuing P j i} with hs
  have hfin : s.Finite := (Set.finite_lt_nat (D.candCount j)).subset fun i hi => hi.1
  have hclosed : IsClosed
      (⋃ i ∈ s, Metric.closedBall (D.cand j i) (T.sourceSeparation * P.scale T j)) :=
    hfin.isClosed_biUnion fun i _ => Metric.isClosed_closedBall
  have hsub : D.kept P j ⊆
      ⋃ i ∈ s, Metric.closedBall (D.cand j i) (T.sourceSeparation * P.scale T j) := by
    intro y hy
    obtain ⟨i, hi, hb⟩ := mem_iUnion₂.1 (D.ms4_kept_subset_contBalls P hj hy)
    exact mem_iUnion₂.2 ⟨i, hi, Metric.ball_subset_closedBall hb⟩
  obtain ⟨i, hi, hb⟩ := mem_iUnion₂.1 (closure_minimal hsub hclosed hz)
  exact ⟨i, hi.1, hi.2, Metric.mem_closedBall.1 hb⟩

/-- Every core limit point is a level limit of the constructed coherent family. -/
theorem ms4_isLevelLimit (hR : 0 < P.R) {z : Space n} (hz : z ∈ D.coreLimit P) :
    (D.family P hR).IsLevelLimit z := by
  have hnear : ∀ m : ℕ, ∃ i, i < D.candCount (m + 1) ∧ D.IsContinuing P (m + 1) i ∧
      dist z (D.cand (m + 1) i) ≤ T.sourceSeparation * P.scale T (m + 1) :=
    fun m => ms4_exists_cont_near (Nat.le_add_left 1 m) (mem_iInter.1 hz (m + 1))
  choose idx hidx hcont hdist using hnear
  have hc : ∀ m, (D.family P hR).center (m + 1) (idx m) = D.cand (m + 1) (idx m) := by
    intro m
    show (if m + 1 = 0 then D.rootCenter else D.cand (m + 1) (idx m)) = _
    rw [ite_eq_right (Nat.succ_ne_zero m)]
  refine ⟨fun m => m + 1, idx, fun m => ?_, tendsto_add_atTop_nat 1, ?_⟩
  · classical
    show idx m ∈ (if m + 1 = 0 then {0} else D.contIndex P (m + 1))
    rw [ite_eq_right (Nat.succ_ne_zero m)]
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hidx m), hcont m⟩
  · show Tendsto (fun m => (D.family P hR).center (m + 1) (idx m)) atTop (𝓝 z)
    simp only [hc]
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) (P.ms4_tendsto_scale T)
    rw [dist_comm]
    exact (hdist m).trans (mul_le_of_le_one_left (P.scale_pos T hR _).le
      T.sourceSeparation_le_one)

/-- The center set `C₀ ∪ {stopping centers}` is closed: away from `closure(S_{j₀})` only the
finitely many centers of the stages `≤ j₀` remain. -/
theorem ms4_isClosed_centers (hD : D.IsSourceConstruction P) : IsClosed (D.centers P) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  by_cases hxc : x ∈ D.coreLimit P
  · exact mem_union_left _ hxc
  obtain ⟨j0, hj0⟩ : ∃ j0, x ∉ closure (D.kept P j0) := by
    simpa only [coreLimit, mem_iInter, not_forall] using hxc
  set V : Set (Space n) := (closure (D.kept P j0))ᶜ with hVdef
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  set F : Set (Space n) := ⋃ j ∈ Iic j0,
    ((D.term j '' Iio (D.termCount j)) ∪ (D.cand j '' Iio (D.candCount j))) with hFdef
  have hF : F.Finite :=
    (finite_Iic j0).biUnion fun j _ => ((finite_Iio _).image _).union ((finite_Iio _).image _)
  have hsub : V ∩ D.centers P ⊆ F := by
    rintro y ⟨hyV, hy⟩
    rcases hy with hy | hy
    · exact absurd (mem_iInter.1 hy j0) hyV
    · obtain ⟨j, h⟩ := D.ms4_exists_stopAt P hy
      by_cases hjj : j ≤ j0
      · obtain ⟨-, ⟨i, hi, rfl, -⟩ | ⟨i, hi, -, rfl, -⟩⟩ := h
        · exact mem_iUnion₂.2 ⟨j, hjj, Or.inl ⟨i, hi, rfl⟩⟩
        · exact mem_iUnion₂.2 ⟨j, hjj, Or.inr ⟨i, hi, rfl⟩⟩
      · exfalso
        have : y ∈ D.kept P j0 :=
          D.ms4_kept_anti P (show j0 ≤ j - 1 by omega) (h.mem_entering hD)
        exact hyV (subset_closure this)
  have hfin : (V ∩ D.centers P).Finite := hF.subset hsub
  have hx' : x ∈ closure (V ∩ D.centers P) := hV.inter_closure ⟨hj0, hx⟩
  rw [hfin.isClosed.closure_eq] at hx'
  exact hx'.2

end ConstructionData

end ParabolicRectifiability
