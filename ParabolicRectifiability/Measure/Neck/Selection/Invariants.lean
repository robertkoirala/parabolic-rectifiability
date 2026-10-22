import ParabolicRectifiability.Measure.Neck.Selection.StageSets

/-!
# Stage invariants and collapsed centers of the source construction

Proofs of two statements about the stages of the construction:

* `stageInvariants_of_construction_proof` (`stageInvariants_of_construction`): the kept sets are
  Borel, decreasing and inside `S`; the continuing `κ r_j`-balls cover what the collapsed
  phase leaves (`κ ≤ 1 < 5`); a terminal center or noncontinuing candidate occurs at one
  stage and index only, the two kinds never coincide, and each is removed at its own
  stage.  The argument: a terminal center lies in its own ball of radius `f ≥ r_j > 0`,
  and a candidate in its own ball of radius `5 r_j`; every later point (later terminal
  centers, later candidates, later kept points) avoids these balls by the definition of
  the ordered removal, and two candidates of one stage are `κ r_j`-separated.
* `collapsedCenter_spec_proof` (`collapsedCenter_spec`): a stopping center that is
  not terminal is a collapsed center, and its radius is `5 r_j` at its recorded stage.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NeckSelection

variable {n k : ℕ} {T : NeckType}

/-- The terminal center `term j i` lies in its own (open) terminal ball. -/
theorem term_mem_ball {P : SourceSetup n} {D : ConstructionData n k T} (hR : 0 < P.R)
    (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ} (hi : i < D.termCount j) :
    D.term j i ∈ Metric.ball (D.term j i) (P.f (D.term j i)) :=
  Metric.mem_ball_self ((P.scale_pos T hR j).trans_le (hD.term_large j hj i hi))

theorem cand_mem_ball {P : SourceSetup n} (D : ConstructionData n k T) (hR : 0 < P.R)
    (j i : ℕ) : D.cand j i ∈ Metric.ball (D.cand j i) (5 * P.scale T j) :=
  Metric.mem_ball_self (by linarith [P.scale_pos T hR j])

/-- A point of the kept set of stage `j` avoids every terminal ball of stage `j`. -/
theorem not_mem_termBall_of_kept {P : SourceSetup n} (D : ConstructionData n k T) {j : ℕ}
    (hj : 1 ≤ j) {i : ℕ} (hi : i < D.termCount j) {z : Space n} (hz : z ∈ D.kept P j) :
    z ∉ Metric.ball (D.term j i) (P.f (D.term j i)) := fun hzb =>
  (kept_subset_afterTerm D P hj hz).2 (mem_iUnion₂.mpr ⟨i, hi, hzb⟩)

/-- A point of the kept set of stage `j` avoids every collapsed ball of stage `j`. -/
theorem not_mem_collBall_of_kept {P : SourceSetup n} (D : ConstructionData n k T) {j : ℕ}
    (hj : 1 ≤ j) {i : ℕ} (hi : i < D.candCount j) (hc : ¬ D.IsContinuing P j i) {z : Space n}
    (hz : z ∈ D.kept P j) : z ∉ Metric.ball (D.cand j i) (5 * P.scale T j) := fun hzb =>
  (kept_subset_afterColl D P hj hz).2 (mem_iUnion₂.mpr ⟨i, ⟨hi, hc⟩, hzb⟩)

/-- Two terminal centers of one stage with distinct indices are distinct. -/
theorem term_injective_of_stage {P : SourceSetup n} {D : ConstructionData n k T}
    (hR : 0 < P.R) (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i i' : ℕ}
    (hi : i < D.termCount j) (hi' : i' < D.termCount j) (heq : D.term j i = D.term j i') :
    i = i' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · refine (hD.term_mem j hj i' hi').2 (mem_iUnion₂.mpr ⟨i, h, ?_⟩)
    rw [← heq]
    exact term_mem_ball hR hD hj hi
  · refine (hD.term_mem j hj i hi).2 (mem_iUnion₂.mpr ⟨i', h, ?_⟩)
    rw [heq]
    exact term_mem_ball hR hD hj hi'

end NeckSelection

open NeckSelection

/-- **`stageInvariants_of_construction`**: the stage invariants of the construction. -/
theorem stageInvariants_of_construction_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      D.StageInvariants P := by
  intro k T P D _ _ hP hD
  have hR := hP.R_pos
  have hterm_ent : ∀ j, 1 ≤ j → ∀ i, i < D.termCount j → D.term j i ∈ D.entering P j :=
    fun j hj i hi => (hD.term_mem j hj i hi).1
  have hcand_ent : ∀ j, 1 ≤ j → ∀ i, i < D.candCount j → D.cand j i ∈ D.entering P j :=
    fun j hj i hi => afterTerm_subset D P j _ (hD.cand_mem j hj i hi)
  refine
    { measurableSet_kept := measurableSet_kept D P hP.measurableSet_S
      kept_subset := fun j => kept_subset_S D P j
      kept_succ_subset := fun j => kept_succ_subset D P j
      afterColl_subset := ?_
      term_unique := ?_
      coll_unique := ?_
      term_ne_coll := ?_
      term_not_kept := ?_
      coll_not_kept := ?_ }
  · -- the continuing balls cover what the collapsed phase leaves
    intro j hj z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hD.cand_cover j hj hz.1)
    by_cases hc : D.IsContinuing P j i
    · exact mem_iUnion₂.mpr ⟨i, ⟨hi, hc⟩, hzi⟩
    · exfalso
      refine hz.2 (mem_iUnion₂.mpr ⟨i, ⟨hi, hc⟩, ?_⟩)
      refine Metric.ball_subset_ball ?_ hzi
      have h1 := T.sourceSeparation_le_one
      have h2 := P.scale_pos T hR j
      nlinarith
  · -- uniqueness of terminal centers
    intro j j' i i' hj hj' hi hi' heq
    rcases lt_trichotomy j j' with hlt | rfl | hgt
    · exfalso
      have hz : D.term j' i' ∈ D.kept P j :=
        entering_subset_kept D P hlt (hterm_ent j' hj' i' hi')
      refine not_mem_termBall_of_kept D hj hi hz ?_
      rw [← heq]
      exact term_mem_ball hR hD hj hi
    · exact ⟨rfl, term_injective_of_stage hR hD hj hi hi' heq⟩
    · exfalso
      have hz : D.term j i ∈ D.kept P j' :=
        entering_subset_kept D P hgt (hterm_ent j hj i hi)
      refine not_mem_termBall_of_kept D hj' hi' hz ?_
      rw [heq]
      exact term_mem_ball hR hD hj' hi'
  · -- uniqueness of noncontinuing candidates
    intro j j' i i' hj hj' hi hi' hc hc' heq
    rcases lt_trichotomy j j' with hlt | rfl | hgt
    · exfalso
      have hz : D.cand j' i' ∈ D.kept P j :=
        entering_subset_kept D P hlt (hcand_ent j' hj' i' hi')
      refine not_mem_collBall_of_kept D hj hi hc hz ?_
      rw [← heq]
      exact cand_mem_ball D hR j i
    · refine ⟨rfl, ?_⟩
      by_contra hne
      have hsep := hD.cand_separated j hj i hi i' hi' hne
      rw [heq, dist_self] at hsep
      have := mul_pos (T.sourceSeparation_pos) (P.scale_pos T hR j)
      linarith
    · exfalso
      have hz : D.cand j i ∈ D.kept P j' :=
        entering_subset_kept D P hgt (hcand_ent j hj i hi)
      refine not_mem_collBall_of_kept D hj' hi' hc' hz ?_
      rw [heq]
      exact cand_mem_ball D hR j' i'
  · -- terminal centers are not noncontinuing candidates
    intro j j' i i' hj hj' hi hi' hc' heq
    rcases lt_trichotomy j j' with hlt | rfl | hgt
    · have hz : D.cand j' i' ∈ D.kept P j :=
        entering_subset_kept D P hlt (hcand_ent j' hj' i' hi')
      refine not_mem_termBall_of_kept D hj hi hz ?_
      rw [← heq]
      exact term_mem_ball hR hD hj hi
    · refine (hD.cand_mem j hj i' hi').2 (mem_iUnion₂.mpr ⟨i, hi, ?_⟩)
      rw [← heq]
      exact term_mem_ball hR hD hj hi
    · have hz : D.term j i ∈ D.kept P j' :=
        entering_subset_kept D P hgt (hterm_ent j hj i hi)
      refine not_mem_collBall_of_kept D hj' hi' hc' hz ?_
      rw [heq]
      exact cand_mem_ball D hR j' i'
  · -- terminal centers are removed at their own stage
    intro j i hj hi hz
    exact not_mem_termBall_of_kept D hj hi hz (term_mem_ball hR hD hj hi)
  · -- noncontinuing candidates are removed at their own stage
    intro j i hj hi hc hz
    exact not_mem_collBall_of_kept D hj hi hc hz (cand_mem_ball D hR j i)

/-- **`collapsedCenter_spec`**: a non-terminal stopping center is a collapsed center. -/
theorem collapsedCenter_spec_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      T.Available n k → k < n + 2 → P.IsAdmissible → D.IsSourceConstruction P →
      ∀ c ∈ D.stopping P, c ∉ D.terminal → ∃ j i : ℕ, 1 ≤ j ∧ i < D.candCount j ∧
        D.cand j i = c ∧ ¬ D.IsContinuing P j i ∧ D.radius P c = 5 * P.scale T j := by
  intro k T P D _ _ _ _ c hc hct
  have hcoll := isCollCenter_of_stopping D P hc hct
  obtain ⟨hj, i, hi, hnc, hci, -⟩ := collStage_spec D P hcoll
  exact ⟨D.collStage P c, i, hj, hi, hci, hnc, radius_of_coll D P hct hcoll⟩

end ParabolicRectifiability
