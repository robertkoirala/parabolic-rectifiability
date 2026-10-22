import ParabolicRectifiability.Measure.Neck.Selection.Invariants

/-!
# The source partition of the construction

Proof of `partitionFacts_of_stageInvariants`.

Every piece of stage `j` (terminal, collapsed or stage-error piece) lies in the entering
set `S_{j-1}` and avoids the kept set `S_j`; hence pieces of different stages are
disjoint. Inside one stage the first-ball order separates pieces of one kind, the
collapsed and error pieces avoid the terminal balls, and the error pieces avoid the
collapsed balls. A point of `S` is in the initial-tube error, or in every `S_j` (the core
assignment), or it leaves the kept sets at a first stage `j ≥ 1`; there it lies in a
terminal ball, a collapsed ball, or (by the continuing cover) in a parent piece whose
kept part would keep it, so it lies in the error part. The cutoff vanishes on
`S_∞ = ⋂_j S_j` because `f < r_j` after every terminal phase and `r_j → 0`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NeckSelection

variable {n k : ℕ} {T : NeckType} {P : SourceSetup n} {D : ConstructionData n k T}

theorem mem_nodeErrorSet {z : Space n} :
    z ∈ D.nodeErrorSet P ↔ ∃ j, 1 ≤ j ∧ ∃ i, (i < D.candCount j ∧ D.IsContinuing P j i) ∧
      z ∈ D.errorPiece P j (D.entering P j) i := by
  simp only [ConstructionData.nodeErrorSet, mem_iUnion, exists_prop]

theorem mem_assignment {c z : Space n} :
    z ∈ D.assignment P c ↔
      (∃ j, 1 ≤ j ∧ ∃ i, (i < D.termCount j ∧ D.term j i = c) ∧
        z ∈ D.termPiece P j (D.entering P j) i) ∨
      (∃ j, 1 ≤ j ∧ ∃ i, (i < D.candCount j ∧ ¬ D.IsContinuing P j i ∧ D.cand j i = c) ∧
        z ∈ D.collPiece P j (D.entering P j) i) := by
  simp only [ConstructionData.assignment, mem_union, mem_iUnion, exists_prop]

/-! ## Pieces and the kept sets -/

theorem collPiece_subset_entering (j i : ℕ) :
    D.collPiece P j (D.entering P j) i ⊆ D.entering P j :=
  (collPiece_subset_afterTerm D P j _ i).trans (afterTerm_subset D P j _)

theorem errorPiece_subset_afterColl (j i : ℕ) :
    D.errorPiece P j (D.entering P j) i ⊆ D.afterColl P j (D.entering P j) :=
  (errorPiece_subset_parentPiece D P j _ i).trans (parentPiece_subset_afterColl D P j _ i)

theorem errorPiece_subset_entering (j i : ℕ) :
    D.errorPiece P j (D.entering P j) i ⊆ D.entering P j :=
  ((errorPiece_subset_afterColl j i).trans (afterColl_subset_afterTerm D P j _)).trans
    (afterTerm_subset D P j _)

theorem termPiece_disjoint_kept {j i : ℕ} (hj : 1 ≤ j) (hi : i < D.termCount j) :
    Disjoint (D.termPiece P j (D.entering P j) i) (D.kept P j) :=
  Set.disjoint_left.mpr fun _ hz hzk =>
    not_mem_termBall_of_kept D hj hi hzk (termPiece_subset_ball D P j _ i hz)

theorem collPiece_disjoint_kept {j i : ℕ} (hj : 1 ≤ j) (hi : i < D.candCount j)
    (hc : ¬ D.IsContinuing P j i) :
    Disjoint (D.collPiece P j (D.entering P j) i) (D.kept P j) :=
  Set.disjoint_left.mpr fun _ hz hzk =>
    not_mem_collBall_of_kept D hj hi hc hzk (collPiece_subset_ball D P j _ i hz)

theorem errorPiece_disjoint_kept {j i : ℕ} (hj : 1 ≤ j) (hc : D.IsContinuing P j i) :
    Disjoint (D.errorPiece P j (D.entering P j) i) (D.kept P j) := by
  rw [Set.disjoint_left]
  intro z hz hzk
  rw [kept_eq_stageKept D P j hj] at hzk
  obtain ⟨i', ⟨-, hc'⟩, hzi'⟩ := mem_iUnion₂.mp hzk
  have heq : i' = i :=
    eq_of_mem_firstBallPiece (p := fun l => D.IsContinuing P j l) hc' hc
      (keptPiece_subset_parentPiece D P j _ i' hzi')
      (errorPiece_subset_parentPiece D P j _ i hz)
  subst heq
  exact hz.2 hzi'

/-- Pieces of two different stages are disjoint. -/
theorem stage_eq_of_mem {X Y : Set (Space n)} {j j' : ℕ} (hX : X ⊆ D.entering P j)
    (hXk : Disjoint X (D.kept P j)) (hY : Y ⊆ D.entering P j')
    (hYk : Disjoint Y (D.kept P j')) {z : Space n} (hzX : z ∈ X) (hzY : z ∈ Y) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact Set.disjoint_left.mp hXk hzX (entering_subset_kept D P h (hY hzY))
  · exact Set.disjoint_left.mp hYk hzY (entering_subset_kept D P h (hX hzX))

theorem term_term_eq {j j' i i' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') (hi : i < D.termCount j)
    (hi' : i' < D.termCount j') {z : Space n} (hz : z ∈ D.termPiece P j (D.entering P j) i)
    (hz' : z ∈ D.termPiece P j' (D.entering P j') i') : j = j' ∧ i = i' := by
  have h := stage_eq_of_mem (termPiece_subset D P j _ i) (termPiece_disjoint_kept hj hi)
    (termPiece_subset D P j' _ i') (termPiece_disjoint_kept hj' hi') hz hz'
  subst h
  exact ⟨rfl, eq_of_mem_firstBallPiece (p := fun _ => True) trivial trivial hz hz'⟩

theorem coll_coll_eq {j j' i i' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') (hi : i < D.candCount j)
    (hi' : i' < D.candCount j') (hc : ¬ D.IsContinuing P j i) (hc' : ¬ D.IsContinuing P j' i')
    {z : Space n} (hz : z ∈ D.collPiece P j (D.entering P j) i)
    (hz' : z ∈ D.collPiece P j' (D.entering P j') i') : j = j' ∧ i = i' := by
  have h := stage_eq_of_mem (collPiece_subset_entering j i) (collPiece_disjoint_kept hj hi hc)
    (collPiece_subset_entering j' i') (collPiece_disjoint_kept hj' hi' hc') hz hz'
  subst h
  exact ⟨rfl, eq_of_mem_firstBallPiece (p := fun l => ¬ D.IsContinuing P j l) hc hc' hz hz'⟩

theorem term_coll_false {j j' i i' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') (hi : i < D.termCount j)
    (hi' : i' < D.candCount j') (hc' : ¬ D.IsContinuing P j' i') {z : Space n}
    (hz : z ∈ D.termPiece P j (D.entering P j) i)
    (hz' : z ∈ D.collPiece P j' (D.entering P j') i') : False := by
  have h := stage_eq_of_mem (termPiece_subset D P j _ i) (termPiece_disjoint_kept hj hi)
    (collPiece_subset_entering j' i') (collPiece_disjoint_kept hj' hi' hc') hz hz'
  subst h
  exact (collPiece_subset_afterTerm D P j _ i' hz').2
    (mem_iUnion₂.mpr ⟨i, hi, termPiece_subset_ball D P j _ i hz⟩)

theorem term_error_false {j j' i i' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') (hi : i < D.termCount j)
    (hc' : D.IsContinuing P j' i') {z : Space n}
    (hz : z ∈ D.termPiece P j (D.entering P j) i)
    (hz' : z ∈ D.errorPiece P j' (D.entering P j') i') : False := by
  have h := stage_eq_of_mem (termPiece_subset D P j _ i) (termPiece_disjoint_kept hj hi)
    (errorPiece_subset_entering j' i') (errorPiece_disjoint_kept hj' hc') hz hz'
  subst h
  exact (afterColl_subset_afterTerm D P j _ (errorPiece_subset_afterColl j i' hz')).2
    (mem_iUnion₂.mpr ⟨i, hi, termPiece_subset_ball D P j _ i hz⟩)

theorem coll_error_false {j j' i i' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') (hi : i < D.candCount j)
    (hc : ¬ D.IsContinuing P j i) (hc' : D.IsContinuing P j' i') {z : Space n}
    (hz : z ∈ D.collPiece P j (D.entering P j) i)
    (hz' : z ∈ D.errorPiece P j' (D.entering P j') i') : False := by
  have h := stage_eq_of_mem (collPiece_subset_entering j i) (collPiece_disjoint_kept hj hi hc)
    (errorPiece_subset_entering j' i') (errorPiece_disjoint_kept hj' hc') hz hz'
  subst h
  exact (errorPiece_subset_afterColl j i' hz').2
    (mem_iUnion₂.mpr ⟨i, ⟨hi, hc⟩, collPiece_subset_ball D P j _ i hz⟩)

/-! ## Stopping centers -/

theorem not_isTermCenter_cand (hI : D.StageInvariants P) {j i : ℕ} (hj : 1 ≤ j)
    (hi : i < D.candCount j) (hc : ¬ D.IsContinuing P j i) : ¬ D.IsTermCenter (D.cand j i) := by
  rintro ⟨j', hj', i', hi', heq⟩
  exact hI.term_ne_coll j' j i' i hj' hj hi' hi hc heq

theorem collStage_cand (hI : D.StageInvariants P) {j i : ℕ} (hj : 1 ≤ j)
    (hi : i < D.candCount j) (hc : ¬ D.IsContinuing P j i)
    (hcoll : D.IsCollCenter P (D.cand j i)) : D.collStage P (D.cand j i) = j := by
  obtain ⟨hj', i', hi', hc', heq, -⟩ := collStage_spec D P hcoll
  exact (hI.coll_unique _ _ _ _ hj' hj hi' hi hc' hc heq).1

theorem radius_term_pos (hR : 0 < P.R) (hD : D.IsSourceConstruction P) {j i : ℕ}
    (hj : 1 ≤ j) (hi : i < D.termCount j) : 0 < D.radius P (D.term j i) := by
  rw [radius_of_term D P ⟨j, hj, i, hi, rfl⟩]
  exact (P.scale_pos T hR j).trans_le (hD.term_large j hj i hi)

theorem radius_cand_pos (hR : 0 < P.R) (hI : D.StageInvariants P) {j i : ℕ} (hj : 1 ≤ j)
    (hi : i < D.candCount j) (hc : ¬ D.IsContinuing P j i)
    (hcoll : D.IsCollCenter P (D.cand j i)) : 0 < D.radius P (D.cand j i) := by
  rw [radius_of_coll D P (not_isTermCenter_cand hI hj hi hc) hcoll]
  linarith [P.scale_pos T hR (D.collStage P (D.cand j i))]

/-! ## The cutoff on the core assignment -/

theorem cutoff_eq_zero_of_forall_lt (hR : 0 < P.R) {z : Space n} (h0 : 0 ≤ P.f z)
    (hlt : ∀ j, 1 ≤ j → P.f z < P.scale T j) : P.f z = 0 := by
  by_contra hne
  have hpos : 0 < P.f z := lt_of_le_of_ne h0 (Ne.symm hne)
  have hr0 := T.rootRadius_pos hR
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (T.rootRadius P.R / P.f z) (by norm_num : (1 : ℝ) < 10)
  have hN' : T.rootRadius P.R / P.f z < 10 ^ (N + 1) :=
    hN.trans_le (pow_le_pow_right₀ (by norm_num) (Nat.le_succ N))
  have h1 : T.rootRadius P.R < 10 ^ (N + 1) * P.f z := (div_lt_iff₀ hpos).mp hN'
  have h2 : P.scale T (N + 1) < P.f z := by
    show T.rootRadius P.R / 10 ^ (N + 1) < P.f z
    rw [div_lt_iff₀ (pow_pos (by norm_num) _)]
    linarith
  linarith [hlt (N + 1) (by omega)]

end NeckSelection

open NeckSelection

/-- **`partitionFacts_of_stageInvariants`**: the stage invariants give the partition facts. -/
theorem partitionFacts_of_stageInvariants_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n) (D : ConstructionData n k T),
      P.IsAdmissible → D.IsSourceConstruction P → D.StageInvariants P →
      D.PartitionFacts P := by
  intro k T P D hP hD hI
  have hR := hP.R_pos
  have hS := hP.measurableSet_S
  have hent : ∀ j, MeasurableSet (D.entering P j) := measurableSet_entering D P hS
  have hnode : MeasurableSet (D.nodeErrorSet P) :=
    MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun _ => measurableSet_errorPiece D P j (hent j) i
  have hcore_mem : ∀ {z}, z ∈ D.coreSet P → ∀ j, z ∈ D.kept P j := fun hz j => mem_iInter.mp hz j
  refine
    { measurableSet_errorSet := (hS.diff (measurableSet_tubeSet D P hS)).union hnode
      measurableSet_coreSet := MeasurableSet.iInter hI.measurableSet_kept
      measurableSet_assignment := fun c _ =>
        (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun i =>
          MeasurableSet.iUnion fun _ => measurableSet_termPiece D P j (hent j) i).union
        (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun i =>
          MeasurableSet.iUnion fun _ => measurableSet_collPiece D P j (hent j) i)
      errorSet_subset := ?_
      coreSet_subset := (iInter_subset _ 0).trans (kept_subset_S D P 0)
      assignment_subset := ?_
      cover := ?_
      disjoint_errorSet_coreSet := ?_
      disjoint_errorSet_assignment := ?_
      disjoint_coreSet_assignment := ?_
      disjoint_assignment := ?_
      cutoff_coreSet := ?_
      coreSet_subset_core := ?_
      assignment_subset_ball := ?_
      terminal_subset := ?_
      terminal_radius := ?_
      terminal_cutoff := ?_
      collapsed_radius := ?_ }
  · -- errorSet_subset
    refine union_subset Set.sdiff_subset fun z hz => ?_
    obtain ⟨j, -, i, -, hzi⟩ := mem_nodeErrorSet.mp hz
    exact entering_subset_S D P j (errorPiece_subset_entering j i hzi)
  · -- assignment_subset
    intro c _ z hz
    rcases mem_assignment.mp hz with ⟨j, -, i, -, hzi⟩ | ⟨j, -, i, -, hzi⟩
    · exact entering_subset_S D P j (termPiece_subset D P j _ i hzi)
    · exact entering_subset_S D P j (collPiece_subset_entering j i hzi)
  · -- cover
    intro z hzS
    by_cases htube : z ∈ D.tubeSet P
    swap
    · exact Or.inl (Or.inl (Or.inl ⟨hzS, htube⟩))
    by_cases hall : ∀ j, z ∈ D.kept P j
    · exact Or.inl (Or.inr (mem_iInter.mpr hall))
    push Not at hall
    classical
    obtain ⟨j, hjnot, hjmin⟩ : ∃ j, z ∉ D.kept P j ∧ ∀ i < j, z ∈ D.kept P i :=
      ⟨Nat.find hall, Nat.find_spec hall, fun i hi => not_not.mp (Nat.find_min hall hi)⟩
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        exact absurd htube hjnot
      · exact h
    have hzE : z ∈ D.entering P j := hjmin (j - 1) (by omega)
    have hjnot' : z ∉ D.stageKept P j (D.entering P j) := by
      rw [← kept_eq_stageKept D P j hj]
      exact hjnot
    by_cases hT : ∃ i, (i < D.termCount j ∧ True) ∧
        z ∈ Metric.ball (D.term j i) (P.f (D.term j i))
    · obtain ⟨i, hi, -, hzi⟩ := exists_mem_firstBallPiece (A := D.entering P j)
        (p := fun _ => True) (c := D.term j) (r := fun l => P.f (D.term j l)) hzE hT
      have hcT : D.IsTermCenter (D.term j i) := ⟨j, hj, i, hi, rfl⟩
      refine Or.inr (mem_iUnion₂.mpr ⟨D.term j i, ⟨mem_centers_of_term D P hcT,
        radius_term_pos hR hD hj hi⟩, ?_⟩)
      exact mem_assignment.mpr (Or.inl ⟨j, hj, i, ⟨hi, rfl⟩, hzi⟩)
    have hzT : z ∈ D.afterTerm P j (D.entering P j) := by
      refine ⟨hzE, fun hmem => hT ?_⟩
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hmem
      exact ⟨i, ⟨hi, trivial⟩, hzi⟩
    by_cases hC : ∃ i, (i < D.candCount j ∧ ¬ D.IsContinuing P j i) ∧
        z ∈ Metric.ball (D.cand j i) (5 * P.scale T j)
    · obtain ⟨i, hi, hc, hzi⟩ := exists_mem_firstBallPiece (A := D.afterTerm P j (D.entering P j))
        (p := fun l => ¬ D.IsContinuing P j l) (c := D.cand j) (r := fun _ => 5 * P.scale T j)
        hzT hC
      have hcC : D.IsCollCenter P (D.cand j i) := ⟨j, hj, i, hi, hc, rfl, ⟨z, hzi⟩⟩
      refine Or.inr (mem_iUnion₂.mpr ⟨D.cand j i, ⟨mem_centers_of_coll D P hcC,
        radius_cand_pos hR hI hj hi hc hcC⟩, ?_⟩)
      exact mem_assignment.mpr (Or.inr ⟨j, hj, i, ⟨hi, hc, rfl⟩, hzi⟩)
    have hzC : z ∈ D.afterColl P j (D.entering P j) := by
      refine ⟨hzT, fun hmem => hC ?_⟩
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hmem
      exact ⟨i, hi, hzi⟩
    have hcov : ∃ i, (i < D.candCount j ∧ D.IsContinuing P j i) ∧
        z ∈ Metric.ball (D.cand j i) (T.sourceSeparation * P.scale T j) := by
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hI.afterColl_subset j hj hzC)
      exact ⟨i, hi, hzi⟩
    obtain ⟨i, hi, hc, hzi⟩ := exists_mem_firstBallPiece (A := D.afterColl P j (D.entering P j))
      (p := fun l => D.IsContinuing P j l) (c := D.cand j)
      (r := fun _ => T.sourceSeparation * P.scale T j) hzC hcov
    by_cases hk : z ∈ D.keptPiece P j (D.entering P j) i
    · exact (hjnot' (mem_iUnion₂.mpr ⟨i, ⟨hi, hc⟩, hk⟩)).elim
    · exact Or.inl (Or.inl (Or.inr (mem_nodeErrorSet.mpr ⟨j, hj, i, ⟨hi, hc⟩, hzi, hk⟩)))
  · -- disjoint_errorSet_coreSet
    rw [Set.disjoint_left]
    intro z hz hzc
    rcases hz with ⟨-, htube⟩ | hz
    · exact htube (hcore_mem hzc 0)
    · obtain ⟨j, hj, i, ⟨-, hc⟩, hzi⟩ := mem_nodeErrorSet.mp hz
      exact Set.disjoint_left.mp (errorPiece_disjoint_kept hj hc) hzi (hcore_mem hzc j)
  · -- disjoint_errorSet_assignment
    intro c _
    rw [Set.disjoint_left]
    intro z hz hza
    rcases hz with ⟨-, htube⟩ | hz
    · rcases mem_assignment.mp hza with ⟨j, -, i, -, hzi⟩ | ⟨j, -, i, -, hzi⟩
      · exact htube (entering_subset_tubeSet D P j (termPiece_subset D P j _ i hzi))
      · exact htube (entering_subset_tubeSet D P j (collPiece_subset_entering j i hzi))
    · obtain ⟨j', hj', i', ⟨-, hc'⟩, hze⟩ := mem_nodeErrorSet.mp hz
      rcases mem_assignment.mp hza with ⟨j, hj, i, ⟨hi, -⟩, hzi⟩ | ⟨j, hj, i, ⟨hi, hc, -⟩, hzi⟩
      · exact term_error_false hj hj' hi hc' hzi hze
      · exact coll_error_false hj hj' hi hc hc' hzi hze
  · -- disjoint_coreSet_assignment
    intro c _
    rw [Set.disjoint_left]
    intro z hzc hza
    rcases mem_assignment.mp hza with ⟨j, hj, i, ⟨hi, -⟩, hzi⟩ | ⟨j, hj, i, ⟨hi, hc, -⟩, hzi⟩
    · exact Set.disjoint_left.mp (termPiece_disjoint_kept hj hi) hzi (hcore_mem hzc j)
    · exact Set.disjoint_left.mp (collPiece_disjoint_kept hj hi hc) hzi (hcore_mem hzc j)
  · -- disjoint_assignment
    intro c _ c' _ hne
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases mem_assignment.mp hz with ⟨j, hj, i, ⟨hi, hci⟩, hzi⟩ | ⟨j, hj, i, ⟨hi, hc, hci⟩, hzi⟩ <;>
      rcases mem_assignment.mp hz' with ⟨j', hj', i', ⟨hi', hci'⟩, hzi'⟩ |
        ⟨j', hj', i', ⟨hi', hc', hci'⟩, hzi'⟩
    · obtain ⟨rfl, rfl⟩ := term_term_eq hj hj' hi hi' hzi hzi'
      exact hne (hci.symm.trans hci')
    · exact term_coll_false hj hj' hi hi' hc' hzi hzi'
    · exact term_coll_false hj' hj hi' hi hc hzi' hzi
    · obtain ⟨rfl, rfl⟩ := coll_coll_eq hj hj' hi hi' hc hc' hzi hzi'
      exact hne (hci.symm.trans hci')
  · -- cutoff_coreSet
    intro z hzc
    have hzS : z ∈ P.S := kept_subset_S D P 0 (hcore_mem hzc 0)
    exact cutoff_eq_zero_of_forall_lt hR (hP.cutoff.nonneg z hzS) fun j hj =>
      hD.term_done j hj z (kept_subset_afterTerm D P hj (hcore_mem hzc j))
  · -- coreSet_subset_core
    intro z hzc
    have hnt : ¬ D.IsTermCenter z := by
      rintro ⟨j, hj, i, hi, rfl⟩
      exact hI.term_not_kept j i hj hi (hcore_mem hzc j)
    have hnc : ¬ D.IsCollCenter P z := by
      rintro ⟨j, hj, i, hi, hc, rfl, -⟩
      exact hI.coll_not_kept j i hj hi hc (hcore_mem hzc j)
    exact ⟨Or.inl (mem_iInter.mpr fun j => subset_closure (hcore_mem hzc j)),
      radius_of_not D P hnt hnc⟩
  · -- assignment_subset_ball
    intro c _ z hz
    rcases mem_assignment.mp hz with ⟨j, hj, i, ⟨hi, rfl⟩, hzi⟩ | ⟨j, hj, i, ⟨hi, hc, rfl⟩, hzi⟩
    · rw [radius_of_term D P ⟨j, hj, i, hi, rfl⟩]
      exact termPiece_subset_ball D P j _ i hzi
    · have hcoll : D.IsCollCenter P (D.cand j i) := ⟨j, hj, i, hi, hc, rfl, ⟨z, hzi⟩⟩
      rw [radius_of_coll D P (not_isTermCenter_cand hI hj hi hc) hcoll,
        collStage_cand hI hj hi hc hcoll]
      exact collPiece_subset_ball D P j _ i hzi
  · -- terminal_subset
    intro c hc
    obtain ⟨j, hj, i, hi, rfl⟩ := id hc
    exact ⟨mem_centers_of_term D P hc, radius_term_pos hR hD hj hi⟩
  · -- terminal_radius
    intro c hc
    obtain ⟨j, hj, i, hi, rfl⟩ := id hc
    exact ⟨entering_subset_S D P j (hD.term_mem j hj i hi).1, radius_of_term D P hc⟩
  · -- terminal_cutoff
    intro c hc z hz
    rw [radius_of_term D P hc]
    rcases mem_assignment.mp hz with ⟨j, hj, i, ⟨hi, rfl⟩, hzi⟩ | ⟨j, hj, i, ⟨hi, hci, rfl⟩, hzi⟩
    · obtain ⟨hzE, -, hznot⟩ := hzi
      refine hD.term_max j hj i hi z ⟨hzE, fun hmem => hznot ?_⟩
      obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hmem
      exact mem_iUnion₂.mpr ⟨l, ⟨hl, trivial⟩, hzl⟩
    · exact absurd hc (not_isTermCenter_cand hI hj hi hci)
  · -- collapsed_radius
    intro c hc hct
    have hcoll := isCollCenter_of_stopping D P hc hct
    obtain ⟨hj₀, i₀, hi₀, hc₀, hci₀, -⟩ := collStage_spec D P hcoll
    refine ⟨D.collStage P c, hj₀, radius_of_coll D P hct hcoll, fun z hz => ?_⟩
    rcases mem_assignment.mp hz with ⟨j, hj, i, ⟨hi, hci⟩, -⟩ | ⟨j, hj, i, ⟨hi, hc', hci⟩, hzi⟩
    · exact (hct ⟨j, hj, i, hi, hci⟩).elim
    · have hjj : j = D.collStage P c :=
        (hI.coll_unique _ _ _ _ hj hj₀ hi hi₀ hc' hc₀ (hci.trans hci₀.symm)).1
      rw [← hjj]
      exact hD.term_done j hj z (collPiece_subset_afterTerm D P j _ i hzi)

end ParabolicRectifiability
