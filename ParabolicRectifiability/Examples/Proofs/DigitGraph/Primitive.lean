import ParabolicRectifiability.Examples.Proofs.DigitGraph.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-! # Centered moment of the marked digits

For `j ≥ 1`, every centre `x₀` and `h > 0`,
`|∫_{-h}^{h} X (b_j(x₀+X) - δ_j) dX| ≤ 4 δ_j P_j h` (`e2_sb_primitive_proof`). The second mean
value theorem on each half interval reduces this to the periodic discrepancy bound. -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

/-- Splitting the signed linear weight at zero lets the second mean value theorem
use an interval discrepancy bound once on each half. -/
private theorem centered_moment_of_discrepancy {g : ℝ → ℝ} {D h : ℝ}
    (hh : 0 < h) (hgi : ∀ a b, IntervalIntegrable g volume a b)
    (hdisc : ∀ a b, a ≤ b → |∫ x in a..b, g x| ≤ D) :
    |∫ x in (-h)..h, x * g x| ≤ 2 * D * h := by
  obtain ⟨c, hc, hleft⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn
      (f := fun x : ℝ => -x) (g := g) (a := -h) (b := 0)
      (by linarith) (by simp)
      (by intro x hx y hy hxy; exact neg_le_neg hxy) (hgi (-h) 0)
  obtain ⟨d, hd, hright⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
      (f := fun x : ℝ => x) (g := g) (a := 0) (b := h)
      hh.le (by simp) (by intro x hx y hy hxy; exact hxy) (hgi 0 h)
  have hl : |∫ x in (-h)..0, x * g x| ≤ h * D := by
    have heq : (∫ x in (-h)..0, -x * g x) = -(∫ x in (-h)..0, x * g x) := by
      simp only [neg_mul, intervalIntegral.integral_neg]
    rw [heq, neg_neg] at hleft
    calc
      _ = |h * ∫ x in (-h)..c, g x| := by rw [← hleft, abs_neg]
      _ = h * |∫ x in (-h)..c, g x| := by rw [abs_mul, abs_of_pos hh]
      _ ≤ h * D := mul_le_mul_of_nonneg_left (hdisc (-h) c hc.1) hh.le
  have hr : |∫ x in 0..h, x * g x| ≤ h * D := by
    rw [hright, abs_mul, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (hdisc d h hd.2) hh.le
  have hwi : ∀ a b, IntervalIntegrable (fun x => x * g x) volume a b := by
    intro a b
    exact (hgi a b).continuousOn_mul continuousOn_id
  rw [← intervalIntegral.integral_add_adjacent_intervals (hwi (-h) 0) (hwi 0 h)]
  exact (abs_add_le _ _).trans (by linarith)

/-- The centered marked-digit moment bound follows from the periodic discrepancy
estimate by the second mean value theorem on the two half intervals. -/
theorem e2_sb_primitive_proof (hG : E2sbGrid) : E2sbPrimitive := by
  intro j hj x₀ h hh
  have hmeas : MeasurableSet (e2_sbMarked j) := by
    change MeasurableSet ((fun x : ℝ => ⌊x / e2_sbEll j⌋) ⁻¹'
      {z : ℤ | ((j + 1 : ℕ) : ℤ) ∣ z})
    exact ((Set.to_countable {z : ℤ | ((j + 1 : ℕ) : ℤ) ∣ z}).measurableSet).preimage
      (measurable_id.div_const _).floor
  have hbi : ∀ a b, IntervalIntegrable (e2_sbBit j) volume a b := by
    intro a b
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_const (c := (1 : ℝ))).def'.indicator hmeas
  let g : ℝ → ℝ := fun x => e2_sbBit j (x₀ + x) - e2_sbDelta j
  have hgi : ∀ a b, IntervalIntegrable g volume a b := by
    intro a b
    have hb : IntervalIntegrable (fun x => e2_sbBit j (x₀ + x)) volume a b := by
      simpa using (hbi (x₀ + a) (x₀ + b)).comp_add_left x₀
    exact hb.sub intervalIntegrable_const
  have hdisc : ∀ a b : ℝ, a ≤ b →
      |∫ x in a..b, g x| ≤ 2 * e2_sbDelta j * e2_sbPeriod j := by
    intro a b hab
    have hb : IntervalIntegrable (fun x => e2_sbBit j (x₀ + x)) volume a b := by
      simpa using (hbi (x₀ + a) (x₀ + b)).comp_add_left x₀
    dsimp [g]
    rw [intervalIntegral.integral_sub hb intervalIntegrable_const,
      intervalIntegral.integral_comp_add_left]
    simpa only [intervalIntegral.integral_const, smul_eq_mul,
      add_sub_add_left_eq_sub, mul_comm] using
      (e2_sb_periodic_proof hG).1 j hj (x₀ + a) (x₀ + b) (by linarith)
  have hm := centered_moment_of_discrepancy hh hgi hdisc
  convert hm using 1; ring

end ParabolicRectifiability.Examples
