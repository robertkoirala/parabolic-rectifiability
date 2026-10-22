import ParabolicRectifiability.Measure.Neck.Definitions

/-!
# Pruning the children of one contracting step

A child of a contracting
step lies in the open ball of its center and radius, so a child of radius `≤ 0` has empty
source. Removing such children from the index set keeps every other field of the step,
and the step identity: the removed restrictions are zero.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ContractingStep

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ} {ν : Measure (Space n)} {S : Set (Space n)}
  {N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ} {B Eerr ρ ε : ℝ}

/-- A child of nonpositive radius has empty source (it lies in an empty open ball). -/
theorem ms6_childSource_eq_empty (D : ContractingStep ν S N B Eerr ρ ε) {w : ℕ}
    (hw : w ∈ D.childIndex) (hr : D.childRadius w ≤ 0) : D.childSource w = ∅ :=
  Set.eq_empty_of_subset_empty
    ((D.childSource_subset_ball w hw).trans (Metric.ball_eq_empty.mpr hr).subset)

/-- The pruned step: the same data, with the children of nonpositive radius removed. -/
def ms6Prune (D : ContractingStep ν S N B Eerr ρ ε) : ContractingStep ν S N B Eerr ρ ε where
  errorSet := D.errorSet
  coreSet := D.coreSet
  childIndex := {w | w ∈ D.childIndex ∧ 0 < D.childRadius w}
  childSource := D.childSource
  childCenter := D.childCenter
  childRadius := D.childRadius
  childParent := D.childParent
  measurableSet_errorSet := D.measurableSet_errorSet
  measurableSet_coreSet := D.measurableSet_coreSet
  measurableSet_childSource := fun w hw => D.measurableSet_childSource w hw.1
  errorSet_subset := D.errorSet_subset
  coreSet_subset := D.coreSet_subset
  childSource_subset := fun w hw => D.childSource_subset w hw.1
  cover := by
    intro z hz
    rcases D.cover hz with h | h
    · exact Or.inl h
    · obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp h
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, ?_⟩, hzw⟩)
      by_contra hr
      rw [D.ms6_childSource_eq_empty hw (not_lt.mp hr)] at hzw
      exact hzw
  disjoint_errorSet_coreSet := D.disjoint_errorSet_coreSet
  disjoint_errorSet_child := fun w hw => D.disjoint_errorSet_child w hw.1
  disjoint_coreSet_child := fun w hw => D.disjoint_coreSet_child w hw.1
  disjoint_children := fun w hw w' hw' h => D.disjoint_children w hw.1 w' hw'.1 h
  coreSet_subset_core := D.coreSet_subset_core
  errorSet_le := D.errorSet_le
  childParent_mem := fun w hw => D.childParent_mem w hw.1
  childSource_subset_hole := fun w hw => D.childSource_subset_hole w hw.1
  childSource_subset_ball := fun w hw => D.childSource_subset_ball w hw.1
  childRadius_eq := fun w hw => D.childRadius_eq w hw.1
  finite_children := fun c => (D.finite_children c).subset fun _ hw => ⟨hw.1.1, hw.2⟩
  childRadius_le := fun w hw => D.childRadius_le w hw.1
  child_content_le :=
    (ENNReal.tsum_mono_subtype (fun w => ENNReal.ofReal (D.childRadius w ^ k))
      (fun _ hw => hw.1)).trans D.child_content_le

/-- The sum of the child restrictions is unchanged by pruning. -/
theorem ms6_sum_prune (D : ContractingStep ν S N B Eerr ρ ε) :
    Measure.sum (fun w : D.childIndex => ν.restrict (D.childSource w)) =
      Measure.sum (fun w : ({w | w ∈ D.childIndex ∧ 0 < D.childRadius w} : Set ℕ) =>
        ν.restrict (D.childSource w)) := by
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs,
    tsum_subtype D.childIndex (fun w => ν.restrict (D.childSource w) s),
    tsum_subtype ({w | w ∈ D.childIndex ∧ 0 < D.childRadius w} : Set ℕ)
      (fun w => ν.restrict (D.childSource w) s)]
  congr 1
  funext w
  by_cases hw : w ∈ D.childIndex
  · by_cases hr : 0 < D.childRadius w
    · have hw' : w ∈ ({w | w ∈ D.childIndex ∧ 0 < D.childRadius w} : Set ℕ) := ⟨hw, hr⟩
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw']
    · have hw' : w ∉ ({w | w ∈ D.childIndex ∧ 0 < D.childRadius w} : Set ℕ) :=
        fun h => hr h.2
      rw [Set.indicator_of_mem hw, Set.indicator_of_notMem hw']
      simp [D.ms6_childSource_eq_empty hw (not_lt.mp hr)]
  · have hw' : w ∉ ({w | w ∈ D.childIndex ∧ 0 < D.childRadius w} : Set ℕ) :=
      fun h => hw h.1
    rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw']

/-- **`ContractingStep.exists_prune`**: a contracting step can be pruned of its children of
radius `≤ 0`. -/
theorem exists_prune_proof (D : ContractingStep ν S N B Eerr ρ ε) :
    ∃ D' : ContractingStep ν S N B Eerr ρ ε,
      (∀ w ∈ D'.childIndex, 0 < D'.childRadius w) ∧
      (∀ w ∈ D'.childIndex, w ∈ D.childIndex ∧ D'.childRadius w = D.childRadius w ∧
        D'.childParent w = D.childParent w) ∧
      (ν = ν.restrict D.errorSet + ν.restrict D.coreSet +
          Measure.sum (fun w : D.childIndex => ν.restrict (D.childSource w)) →
        ν = ν.restrict D'.errorSet + ν.restrict D'.coreSet +
          Measure.sum (fun w : D'.childIndex => ν.restrict (D'.childSource w))) := by
  refine ⟨D.ms6Prune, fun w hw => hw.2, fun w hw => ⟨hw.1, rfl, rfl⟩, ?_⟩
  intro hid
  rw [D.ms6_sum_prune] at hid
  exact hid

end ContractingStep

end ParabolicRectifiability
