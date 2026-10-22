import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Baseline and satellite inside a ball

Both segments fit strictly inside the radius `2h` ball.
The satellite has horizontal displacement at most `5h/8` and vertical
 displacement `h`; its squared distance is at most `89h²/64 < 4h²`. -/

noncomputable section
namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (horizontalSegment)

/-- The baseline and satellite lie in the open ball, even at radius `2h`. -/
theorem e2_sap_ballContain_proof : E2sapBallContain := by
  intro x y h δ ξ r hh hδ hδmax hξ hr
  have hrpos : 0 < r := by linarith
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
  have hξbounds := abs_le.mp hξ
  have hsquare (w : ParabolicRectifiability.BetaP.Plane) :
      dist w (e2_sapPt x y) ^ 2 = (w 0 - x) ^ 2 + (w 1 - y) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_two, e2_sapPt, Real.dist_eq, sq_abs]
  constructor
  · intro w hw
    rcases hw with ⟨hwlo, hwhi, hwy⟩
    have hs : (w 0 - x) ^ 2 ≤ h ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ h - (w 0 - x))
        (by linarith : 0 ≤ h + (w 0 - x))]
    have hd : dist w (e2_sapPt x y) ^ 2 < r ^ 2 := by
      rw [hsquare, hwy]
      nlinarith
    exact Metric.mem_ball.mpr (by nlinarith [(dist_nonneg : 0 ≤ dist w (e2_sapPt x y))])
  · intro w hw
    rcases hw with ⟨hwlo, hwhi, hwy⟩
    have hδh : δ * h ≤ h / 4 := by nlinarith
    have hlo : -(5 * h / 8) ≤ w 0 - x := by linarith
    have hhi : w 0 - x ≤ 5 * h / 8 := by linarith
    have hs : (w 0 - x) ^ 2 ≤ (5 * h / 8) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 5 * h / 8 - (w 0 - x))
        (by linarith : 0 ≤ 5 * h / 8 + (w 0 - x))]
    have hd : dist w (e2_sapPt x y) ^ 2 < r ^ 2 := by
      rw [hsquare, hwy]
      nlinarith
    exact Metric.mem_ball.mpr (by nlinarith [(dist_nonneg : 0 ≤ dist w (e2_sapPt x y))])

end ParabolicRectifiability.Examples
