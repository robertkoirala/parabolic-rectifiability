import ParabolicRectifiability.Measure.Neck.ConstructionConclusions

/-!
# Elementary facts about the stage sets of the source construction

Lemmas about the sets defined in `Construction`, valid
for arbitrary construction data `D` (no selection rule is assumed):

* first-ball pieces lie in their ball and in the assigned set, are pairwise disjoint
  among selected indices, and every point of a selected ball lies in the piece of the
  first selected ball containing it;
* the stage sets are nested: `stageKept ⊆ afterColl ⊆ afterTerm ⊆ E`, so the kept sets
  `S_j` decrease and lie in `S`;
* every stage set is Borel when the entering set and `S` are;
* the radius function and the stage of a collapsed center unfold as expected.

They serve the proofs of `sourceConstruction_of_choices`, `stageInvariants_of_construction`,
`partitionFacts_of_stageInvariants` and `collapsedCenter_spec`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NeckSelection

/-! ## First-ball pieces -/

section FirstBall

variable {X : Type*} [PseudoMetricSpace X] {A : Set X} {p : ℕ → Prop} {c : ℕ → X}
  {r : ℕ → ℝ}

theorem firstBallPiece_subset (i : ℕ) : firstBallPiece A p c r i ⊆ A :=
  inter_subset_left

theorem firstBallPiece_subset_ball (i : ℕ) :
    firstBallPiece A p c r i ⊆ Metric.ball (c i) (r i) :=
  fun _ hz => hz.2.1

theorem firstBallPiece_disjoint {i i' : ℕ} (hi : p i) (hi' : p i') (hne : i ≠ i') :
    Disjoint (firstBallPiece A p c r i) (firstBallPiece A p c r i') := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hz1, hz1'⟩ ⟨-, hz2, hz2'⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact hz2' (mem_iUnion₂.mpr ⟨i, ⟨h, hi⟩, hz1⟩)
  · exact hz1' (mem_iUnion₂.mpr ⟨i', ⟨h, hi'⟩, hz2⟩)

theorem eq_of_mem_firstBallPiece {i i' : ℕ} (hi : p i) (hi' : p i') {z : X}
    (hz : z ∈ firstBallPiece A p c r i) (hz' : z ∈ firstBallPiece A p c r i') : i = i' := by
  by_contra hne
  exact Set.disjoint_left.mp (firstBallPiece_disjoint hi hi' hne) hz hz'

/-- A point of `A` in some selected ball with index below `m` lies in the first-ball piece
of the first such index. -/
theorem exists_mem_firstBallPiece {m : ℕ} {z : X} (hz : z ∈ A)
    (h : ∃ i, (i < m ∧ p i) ∧ z ∈ Metric.ball (c i) (r i)) :
    ∃ i, i < m ∧ p i ∧ z ∈ firstBallPiece A p c r i := by
  classical
  obtain ⟨⟨hm, hp⟩, hzb⟩ := Nat.find_spec h
  refine ⟨Nat.find h, hm, hp, hz, hzb, ?_⟩
  intro hmem
  obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp hmem
  exact Nat.find_min h hl.1 ⟨⟨hl.1.trans hm, hl.2⟩, hzl⟩

theorem isOpen_iUnion_ball (q : ℕ → Prop) :
    IsOpen (⋃ (l : ℕ) (_ : q l), Metric.ball (c l) (r l)) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball

end FirstBall

theorem measurableSet_firstBallPiece {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A)
    (p : ℕ → Prop) (c : ℕ → Space n) (r : ℕ → ℝ) (i : ℕ) :
    MeasurableSet (firstBallPiece A p c r i) :=
  hA.inter (Metric.isOpen_ball.measurableSet.diff (isOpen_iUnion_ball _).measurableSet)

/-! ## Nesting of the stage sets -/

variable {n k : ℕ} {T : NeckType}

section Nesting

variable (D : ConstructionData n k T) (P : SourceSetup n)

theorem afterTerm_subset (j : ℕ) (E : Set (Space n)) : D.afterTerm P j E ⊆ E :=
  Set.sdiff_subset

theorem afterColl_subset_afterTerm (j : ℕ) (E : Set (Space n)) :
    D.afterColl P j E ⊆ D.afterTerm P j E :=
  Set.sdiff_subset

theorem parentPiece_subset_afterColl (j : ℕ) (E : Set (Space n)) (i : ℕ) :
    D.parentPiece P j E i ⊆ D.afterColl P j E :=
  firstBallPiece_subset i

theorem keptPiece_subset_parentPiece (j : ℕ) (E : Set (Space n)) (i : ℕ) :
    D.keptPiece P j E i ⊆ D.parentPiece P j E i :=
  inter_subset_left

theorem errorPiece_subset_parentPiece (j : ℕ) (E : Set (Space n)) (i : ℕ) :
    D.errorPiece P j E i ⊆ D.parentPiece P j E i :=
  Set.sdiff_subset

theorem termPiece_subset (j : ℕ) (E : Set (Space n)) (i : ℕ) : D.termPiece P j E i ⊆ E :=
  firstBallPiece_subset i

theorem termPiece_subset_ball (j : ℕ) (E : Set (Space n)) (i : ℕ) :
    D.termPiece P j E i ⊆ Metric.ball (D.term j i) (P.f (D.term j i)) :=
  firstBallPiece_subset_ball i

theorem collPiece_subset_afterTerm (j : ℕ) (E : Set (Space n)) (i : ℕ) :
    D.collPiece P j E i ⊆ D.afterTerm P j E :=
  firstBallPiece_subset i

theorem collPiece_subset_ball (j : ℕ) (E : Set (Space n)) (i : ℕ) :
    D.collPiece P j E i ⊆ Metric.ball (D.cand j i) (5 * P.scale T j) :=
  firstBallPiece_subset_ball i

theorem stageKept_subset_afterColl (j : ℕ) (E : Set (Space n)) :
    D.stageKept P j E ⊆ D.afterColl P j E :=
  iUnion₂_subset fun i _ =>
    (keptPiece_subset_parentPiece D P j E i).trans (parentPiece_subset_afterColl D P j E i)

theorem stageKept_subset (j : ℕ) (E : Set (Space n)) : D.stageKept P j E ⊆ E :=
  ((stageKept_subset_afterColl D P j E).trans (afterColl_subset_afterTerm D P j E)).trans
    (afterTerm_subset D P j E)

theorem kept_succ_subset (j : ℕ) : D.kept P (j + 1) ⊆ D.kept P j :=
  stageKept_subset D P (j + 1) (D.kept P j)

theorem kept_anti {i j : ℕ} (hij : i ≤ j) : D.kept P j ⊆ D.kept P i := by
  induction hij with
  | refl => exact subset_rfl
  | step _ ih => exact (kept_succ_subset D P _).trans ih

theorem tubeSet_subset : D.tubeSet P ⊆ P.S := inter_subset_left

theorem kept_subset_S (j : ℕ) : D.kept P j ⊆ P.S :=
  (kept_anti D P (Nat.zero_le j)).trans (tubeSet_subset D P)

theorem kept_eq_stageKept : ∀ j : ℕ, 1 ≤ j → D.kept P j = D.stageKept P j (D.entering P j)
  | 0, h => absurd h (by norm_num)
  | _ + 1, _ => rfl

theorem kept_subset_afterColl {j : ℕ} (hj : 1 ≤ j) :
    D.kept P j ⊆ D.afterColl P j (D.entering P j) := by
  rw [kept_eq_stageKept D P j hj]
  exact stageKept_subset_afterColl D P j _

theorem kept_subset_afterTerm {j : ℕ} (hj : 1 ≤ j) :
    D.kept P j ⊆ D.afterTerm P j (D.entering P j) :=
  (kept_subset_afterColl D P hj).trans (afterColl_subset_afterTerm D P j _)

theorem entering_subset_kept {j j' : ℕ} (h : j < j') : D.entering P j' ⊆ D.kept P j :=
  kept_anti D P (by omega)

theorem entering_subset_S (j : ℕ) : D.entering P j ⊆ P.S := kept_subset_S D P (j - 1)

theorem entering_subset_tubeSet (j : ℕ) : D.entering P j ⊆ D.tubeSet P :=
  kept_anti D P (Nat.zero_le (j - 1))

end Nesting

/-! ## Measurability -/

section Measurability

variable (D : ConstructionData n k T) (P : SourceSetup n)

theorem measurableSet_afterTerm (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) :
    MeasurableSet (D.afterTerm P j E) :=
  hE.diff (isOpen_iUnion_ball (c := D.term j) (r := fun i => P.f (D.term j i)) _).measurableSet

theorem measurableSet_afterColl (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) :
    MeasurableSet (D.afterColl P j E) :=
  (measurableSet_afterTerm D P j hE).diff
    (isOpen_iUnion_ball (c := D.cand j) (r := fun _ => 5 * P.scale T j) _).measurableSet

theorem measurableSet_parentPiece (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) (i : ℕ) :
    MeasurableSet (D.parentPiece P j E i) :=
  measurableSet_firstBallPiece (measurableSet_afterColl D P j hE) _ _ _ i

theorem measurableSet_keptPiece (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) (i : ℕ) :
    MeasurableSet (D.keptPiece P j E i) :=
  (measurableSet_parentPiece D P j hE i).inter
    (isClosed_le Metric.continuous_infEDist continuous_const).measurableSet

theorem measurableSet_errorPiece (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) (i : ℕ) :
    MeasurableSet (D.errorPiece P j E i) :=
  (measurableSet_parentPiece D P j hE i).diff (measurableSet_keptPiece D P j hE i)

theorem measurableSet_termPiece (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) (i : ℕ) :
    MeasurableSet (D.termPiece P j E i) :=
  measurableSet_firstBallPiece hE _ _ _ i

theorem measurableSet_collPiece (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) (i : ℕ) :
    MeasurableSet (D.collPiece P j E i) :=
  measurableSet_firstBallPiece (measurableSet_afterTerm D P j hE) _ _ _ i

theorem measurableSet_stageKept (j : ℕ) {E : Set (Space n)} (hE : MeasurableSet E) :
    MeasurableSet (D.stageKept P j E) :=
  MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => measurableSet_keptPiece D P j hE i

theorem measurableSet_tubeSet (hS : MeasurableSet P.S) : MeasurableSet (D.tubeSet P) :=
  hS.inter (isClosed_le Metric.continuous_infEDist continuous_const).measurableSet

theorem measurableSet_kept (hS : MeasurableSet P.S) : ∀ j, MeasurableSet (D.kept P j)
  | 0 => measurableSet_tubeSet D P hS
  | j + 1 => measurableSet_stageKept D P (j + 1) (measurableSet_kept hS j)

theorem measurableSet_entering (hS : MeasurableSet P.S) (j : ℕ) :
    MeasurableSet (D.entering P j) :=
  measurableSet_kept D P hS (j - 1)

end Measurability

/-! ## Radius and stage of the stopping centers -/

section Radius

variable (D : ConstructionData n k T) (P : SourceSetup n)

theorem radius_of_term {c : Space n} (h : D.IsTermCenter c) : D.radius P c = P.f c := by
  rw [ConstructionData.radius, ite_eq_left h]

theorem radius_of_coll {c : Space n} (h₁ : ¬ D.IsTermCenter c) (h₂ : D.IsCollCenter P c) :
    D.radius P c = 5 * P.scale T (D.collStage P c) := by
  rw [ConstructionData.radius, ite_eq_right h₁, ite_eq_left h₂]

theorem radius_of_not {c : Space n} (h₁ : ¬ D.IsTermCenter c) (h₂ : ¬ D.IsCollCenter P c) :
    D.radius P c = 0 := by
  rw [ConstructionData.radius, ite_eq_right h₁, ite_eq_right h₂]

theorem collStage_spec {c : Space n} (h : D.IsCollCenter P c) :
    1 ≤ D.collStage P c ∧ ∃ i, i < D.candCount (D.collStage P c) ∧
      ¬ D.IsContinuing P (D.collStage P c) i ∧ D.cand (D.collStage P c) i = c ∧
      (D.collPiece P (D.collStage P c) (D.entering P (D.collStage P c)) i).Nonempty := by
  have hs : D.collStage P c = Classical.choose h := by
    rw [ConstructionData.collStage, dite_eq_left h]
  rw [hs]
  exact Classical.choose_spec h

theorem mem_centers_of_term {c : Space n} (h : D.IsTermCenter c) : c ∈ D.centers P :=
  Or.inr (Or.inl h)

theorem mem_centers_of_coll {c : Space n} (h : D.IsCollCenter P c) : c ∈ D.centers P :=
  Or.inr (Or.inr h)

/-- A stopping center that is not terminal is a collapsed center. -/
theorem isCollCenter_of_stopping {c : Space n} (hc : c ∈ D.stopping P)
    (ht : ¬ D.IsTermCenter c) : D.IsCollCenter P c := by
  by_contra h
  have h0 := radius_of_not D P ht h
  have hpos := hc.2
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

end Radius

end NeckSelection

end ParabolicRectifiability
