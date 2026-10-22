import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Basic properties of the decorated segment set

The countable union of labelled horizontal segments is a Borel subset of the plane, and the
label bounds place it in the closed ball of radius `2` about the origin.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane horizontalSegment)

/-- The labelled union is Borel, and the label bounds put it in a fixed planar ball. -/
theorem e2_sap_setBasic_proof (hG : E2sapLabelBounds) : E2sapSetBasic := by
  constructor
  · apply MeasurableSet.iUnion
    intro i
    exact ((isClosed_le continuous_const (EuclideanSpace.proj 0).continuous).inter
      ((isClosed_le (EuclideanSpace.proj 0).continuous continuous_const).inter
        (isClosed_eq (EuclideanSpace.proj 1).continuous continuous_const))).measurableSet
  · apply (Metric.isBounded_closedBall (x := (0 : Plane)) (r := 2)).subset
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨_, ha, hv, hb, hb'⟩ := hG i i.property
    obtain ⟨hu, hvx, hy⟩ := hi
    have hx0 : 0 ≤ x 0 := ha.trans hu
    have hx1 : x 0 ≤ 1 := hvx.trans hv
    have hy0 : 0 ≤ x 1 := by simpa only [hy] using hb
    have hy1 : x 1 ≤ 1 := by simpa only [hy] using hb'
    rw [EuclideanSpace.closedBall_zero_eq 2 (by norm_num)]
    simp only [mem_ofPred_eq, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1),
      mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg hy0 (sub_nonneg.mpr hy1)]

end ParabolicRectifiability.Examples
