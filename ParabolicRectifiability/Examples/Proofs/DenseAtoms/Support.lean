import ParabolicRectifiability.Examples.Proofs.DenseAtoms.Statements

/-! The positive atomic measure has exactly the prescribed closed support. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace ParabolicRectifiability.Examples

theorem e2_dense_support_proof : E2DenseWeightStatement → E2DenseSupportStatement := by
  intro hweight n k z hz hdense
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
    change denseAtomMeasure k z (Metric.closedBall (point 0 0) (1 / 4))ᶜ = 0
    rw [denseAtomMeasure, Measure.sum_apply_eq_zero]
    intro j
    rw [Measure.smul_apply,
      Measure.dirac_apply' _ Metric.isClosed_closedBall.measurableSet.compl,
      indicator_of_notMem (show z j ∉ (Metric.closedBall (point 0 0) (1 / 4))ᶜ from
        fun h => h (hz j))]
    simp
  · apply hdense.trans
    apply closure_minimal _ Measure.isClosed_support
    rintro x ⟨j, rfl⟩
    apply (Measure.mem_support_iff_forall (z j)).2
    intro U hU
    have hpos : 0 < (ENNReal.ofReal (denseAtomWeight k z j) • Measure.dirac (z j)) U := by
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
      simpa using ENNReal.ofReal_pos.2 ((hweight n k z).1 j)
    exact hpos.trans_le ((Measure.le_sum
      (fun i => ENNReal.ofReal (denseAtomWeight k z i) • Measure.dirac (z i)) j) U)

end ParabolicRectifiability.Examples
