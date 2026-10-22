import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Mass bounds for the decorated segment set

The one-dimensional Hausdorff measure of the decorated segment set is at least one (it
contains the root segment) and at most `100/99` (by the total labelled length).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (horizontalSegment)

/-- The root gives unit arclength. Countable subadditivity bounds the union by the
labelled lengths, even when segments overlap or have multiple labels. -/
theorem e2_sap_mass_proof (hS : E2sapSegment) (hG : E2sapLabelBounds)
    (hT : E2sapTreeLength) : E2sapMass := by
  have hroot : Encodable.encode ([] : List (ℕ × ℕ)) ∈ e2_sapIndex := by
    simp [e2_sapIndex, e2_sapLabel, e2_sapValid]
  let root : e2_sapIndex := ⟨_, hroot⟩
  have hrootseg :
      horizontalSegment (e2_sapLeft root) (e2_sapRight root) (e2_sapHeight root) =
        horizontalSegment 0 1 0 := by
    simp [root, e2_sapLeft, e2_sapRight, e2_sapLength, e2_sapHeight,
      e2_sapLabel, e2_sapSeg]
  have hsub : horizontalSegment 0 1 0 ⊆ e2_sapSet := by
    rw [← hrootseg]
    exact Set.subset_iUnion (fun i : e2_sapIndex =>
      horizontalSegment (e2_sapLeft i) (e2_sapRight i) (e2_sapHeight i)) root
  constructor
  · have hm := measure_mono (μ := μH[1]) hsub
    rw [(hS 0 1 0 (by norm_num)).2.1] at hm
    simpa using hm
  · calc
      μH[1] e2_sapSet ≤ ∑' i : e2_sapIndex,
          μH[1] (horizontalSegment (e2_sapLeft i) (e2_sapRight i) (e2_sapHeight i)) :=
        measure_iUnion_le _
      _ = ∑' i : e2_sapIndex, ENNReal.ofReal (e2_sapLength i) := by
        apply tsum_congr
        intro i
        rw [(hS _ _ _ (hG i i.property).1.le).2.1]
        congr 1
        simp [e2_sapRight]
      _ ≤ ENNReal.ofReal (100 / 99) := hT

end ParabolicRectifiability.Examples
