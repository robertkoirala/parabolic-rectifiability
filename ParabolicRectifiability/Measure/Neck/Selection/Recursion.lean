import ParabolicRectifiability.Measure.Neck.Selection.StageSets

/-!
# The recursive assembly of the source construction

Proof of `sourceConstruction_of_choices`.

Fix a root choice `(L, τ, z)` and choose, for every stage `j ≥ 1` and every entering set
`E ⊆ S`, construction data satisfying the stage-`j` rules for `E`. The entering sets are
defined by recursion: `K 0` is the initial tube of `L × {τ}` (or `L × ℝ`), and
`K (j+1)` is the kept set produced from `K j` by the data chosen for stage `j + 1` and
entering set `K j`. The assembled data take their root from `(L, τ, z)` and their stage-`j`
fields from the data chosen for `(j, K (j-1))`. Since the stage-`j` sets of construction
data depend only on its stage-`j` fields, the kept sets of the assembled data are exactly
the `K j` (induction on `j`); they lie in `S`, so every chosen stage satisfies its rules
for the actual entering set, and all selection rules hold.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

namespace NeckSelection

variable {n k : ℕ} {T : NeckType}

/-- Two construction data agree at stage `j`. -/
structure StageAgree (D D' : ConstructionData n k T) (j : ℕ) : Prop where
  termCount : D.termCount j = D'.termCount j
  term : ∀ i, D.term j i = D'.term j i
  candCount : D.candCount j = D'.candCount j
  cand : ∀ i, D.cand j i = D'.cand j i
  plane : ∀ i, D.plane j i = D'.plane j i
  time : ∀ i, D.time j i = D'.time j i

section Congr

variable {D D' : ConstructionData n k T} {j : ℕ} (h : StageAgree D D' j) (P : SourceSetup n)
include h

theorem afterTerm_congr (E : Set (Space n)) : D.afterTerm P j E = D'.afterTerm P j E := by
  simp only [ConstructionData.afterTerm, h.termCount, h.term]

theorem isContinuing_congr (i : ℕ) : D.IsContinuing P j i ↔ D'.IsContinuing P j i := by
  simp only [ConstructionData.IsContinuing, h.cand]

theorem modelSet_congr (i : ℕ) : D.modelSet j i = D'.modelSet j i := by
  simp only [ConstructionData.modelSet, h.plane, h.time]

theorem afterColl_congr (E : Set (Space n)) : D.afterColl P j E = D'.afterColl P j E := by
  simp only [ConstructionData.afterColl, afterTerm_congr h P, h.candCount, h.cand,
    isContinuing_congr h P]

theorem keptPiece_congr (E : Set (Space n)) (i : ℕ) :
    D.keptPiece P j E i = D'.keptPiece P j E i := by
  simp only [ConstructionData.keptPiece, ConstructionData.parentPiece, firstBallPiece,
    afterColl_congr h P, h.cand, isContinuing_congr h P, modelSet_congr h]

theorem stageKept_congr (E : Set (Space n)) : D.stageKept P j E = D'.stageKept P j E := by
  simp only [ConstructionData.stageKept, h.candCount, isContinuing_congr h P,
    keptPiece_congr h P]

/-- The stage rules transfer between data that agree at that stage. -/
theorem IsStageChoice.of_agree {E : Set (Space n)} (h' : D'.IsStageChoice P j E) :
    D.IsStageChoice P j E where
  term_mem := by
    simp only [h.termCount, h.term]
    exact h'.term_mem
  term_large := by
    simp only [h.termCount, h.term]
    exact h'.term_large
  term_max := by
    simp only [h.termCount, h.term]
    exact h'.term_max
  term_done := by
    rw [afterTerm_congr h P]
    exact h'.term_done
  cand_mem := by
    simp only [h.candCount, h.cand, afterTerm_congr h P]
    exact h'.cand_mem
  cand_separated := by
    simp only [h.candCount, h.cand]
    exact h'.cand_separated
  cand_cover := by
    simp only [h.candCount, h.cand, afterTerm_congr h P]
    exact h'.cand_cover
  fit_minimal := by
    simp only [h.candCount, h.cand, modelSet_congr h]
    exact h'.fit_minimal

end Congr

/-- The entering sets of the recursive construction, for a root plane and time and a
total stage-choice function `pick`. -/
def recKept (P : SourceSetup n) (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ)
    (pick : ℕ → Set (Space n) → ConstructionData n k T) : ℕ → Set (Space n)
  | 0 => P.S ∩ {y | Metric.infEDist y (T.lowerModelSet L τ) ≤ ENNReal.ofReal (P.θ * P.R)}
  | j + 1 => (pick (j + 1) (recKept P L τ pick j)).stageKept P (j + 1) (recKept P L τ pick j)

/-- The assembled construction data. -/
def recData (P : SourceSetup n) (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ) (z : Space n)
    (pick : ℕ → Set (Space n) → ConstructionData n k T) : ConstructionData n k T where
  rootPlane := L
  rootTime := τ
  rootCenter := z
  termCount := fun j => (pick j (recKept P L τ pick (j - 1))).termCount j
  term := fun j => (pick j (recKept P L τ pick (j - 1))).term j
  candCount := fun j => (pick j (recKept P L τ pick (j - 1))).candCount j
  cand := fun j => (pick j (recKept P L τ pick (j - 1))).cand j
  plane := fun j => (pick j (recKept P L τ pick (j - 1))).plane j
  time := fun j => (pick j (recKept P L τ pick (j - 1))).time j

theorem recData_agree (P : SourceSetup n) (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ)
    (z : Space n) (pick : ℕ → Set (Space n) → ConstructionData n k T) (j : ℕ) :
    StageAgree (recData P L τ z pick) (pick j (recKept P L τ pick (j - 1))) j :=
  ⟨rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem recData_kept (P : SourceSetup n) (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ)
    (z : Space n) (pick : ℕ → Set (Space n) → ConstructionData n k T) :
    ∀ j, (recData P L τ z pick).kept P j = recKept P L τ pick j
  | 0 => rfl
  | j + 1 => by
    have ih := recData_kept P L τ z pick j
    show (recData P L τ z pick).stageKept P (j + 1) ((recData P L τ z pick).kept P j) =
      (pick (j + 1) (recKept P L τ pick j)).stageKept P (j + 1) (recKept P L τ pick j)
    rw [ih]
    exact stageKept_congr (recData_agree P L τ z pick (j + 1)) P _

open Classical in
/-- A total stage-choice function: the supplied choice for `j ≥ 1` and `E ⊆ S`, and a
fixed default otherwise. -/
def stagePick (P : SourceSetup n) (D₀ : ConstructionData n k T)
    (hstage : ∀ j : ℕ, 1 ≤ j → ∀ E : Set (Space n), E ⊆ P.S →
      ∃ D : ConstructionData n k T, D.IsStageChoice P j E)
    (j : ℕ) (E : Set (Space n)) : ConstructionData n k T :=
  if h : 1 ≤ j ∧ E ⊆ P.S then Classical.choose (hstage j h.1 E h.2) else D₀

theorem stagePick_spec (P : SourceSetup n) (D₀ : ConstructionData n k T)
    (hstage : ∀ j : ℕ, 1 ≤ j → ∀ E : Set (Space n), E ⊆ P.S →
      ∃ D : ConstructionData n k T, D.IsStageChoice P j E)
    {j : ℕ} {E : Set (Space n)} (hj : 1 ≤ j) (hE : E ⊆ P.S) :
    (stagePick P D₀ hstage j E).IsStageChoice P j E := by
  have h : stagePick P D₀ hstage j E = Classical.choose (hstage j hj E hE) := by
    rw [stagePick, dite_eq_left (And.intro hj hE)]
  rw [h]
  exact Classical.choose_spec (hstage j hj E hE)

end NeckSelection

open NeckSelection

/-- **`sourceConstruction_of_choices`**: the stagewise choices assemble into a source
construction. -/
theorem sourceConstruction_of_choices_proof (n : ℕ) :
    ∀ {k : ℕ} {T : NeckType} (P : SourceSetup n),
      (∃ (L : AffineSpatialPlane n (T.rank k)) (τ : ℝ) (z : Space n),
        P.IsRootChoice k T L τ z) →
      (∀ j : ℕ, 1 ≤ j → ∀ E : Set (Space n), E ⊆ P.S →
        ∃ D : ConstructionData n k T, D.IsStageChoice P j E) →
      ∃ D : ConstructionData n k T, D.IsSourceConstruction P := by
  intro k T P hroot hstage
  obtain ⟨L, τ, z, hmin, hmem, htime, hdist⟩ := hroot
  obtain ⟨D₀, -⟩ := hstage 1 le_rfl ∅ (empty_subset _)
  set pick := stagePick P D₀ hstage with hpick
  set D := recData P L τ z pick with hD
  have hK : ∀ j, D.kept P j = recKept P L τ pick j := recData_kept P L τ z pick
  have hKS : ∀ j, recKept P L τ pick j ⊆ P.S := fun j => by
    rw [← hK j]
    exact kept_subset_S D P j
  have hst : ∀ j, 1 ≤ j → D.IsStageChoice P j (D.entering P j) := by
    intro j hj
    have hE : D.entering P j = recKept P L τ pick (j - 1) := hK (j - 1)
    rw [hE]
    exact IsStageChoice.of_agree (recData_agree P L τ z pick j) P
      (stagePick_spec P D₀ hstage hj (hKS (j - 1)))
  exact ⟨D,
    { root_minimal := hmin
      root_mem := hmem
      root_time := htime
      root_dist := hdist
      term_mem := fun j hj => (hst j hj).term_mem
      term_large := fun j hj => (hst j hj).term_large
      term_max := fun j hj => (hst j hj).term_max
      term_done := fun j hj => (hst j hj).term_done
      cand_mem := fun j hj => (hst j hj).cand_mem
      cand_separated := fun j hj => (hst j hj).cand_separated
      cand_cover := fun j hj => (hst j hj).cand_cover
      fit_minimal := fun j hj => (hst j hj).fit_minimal }⟩

end ParabolicRectifiability
