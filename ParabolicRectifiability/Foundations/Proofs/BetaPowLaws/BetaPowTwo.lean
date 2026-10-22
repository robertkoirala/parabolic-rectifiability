import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # `B_2 = betaSq`

`Foundations.BetaPowTwoStatement`, proved as `betaPow_two_eq_betaSq_all`. At `p = 2` the integrand `infEDist ^ (2 : ℝ)` of `fitPow` is the
square `modelCost` of `fit`, and the factor `r^{-k-2}` is the same real and natural power; both
quantities vanish at nonpositive radii. Every family, measure, centre and radius.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- At exponent `2` the `p`-fitting integral is the quadratic fitting integral. -/
theorem f3_fitPow_two {n k : ℕ} {T : FamilyKind} (μ : Measure (Space n)) (L : Models n k T)
    (z : Space n) (r : ℝ) : fitPow μ 2 L z r = fit μ L z r := by
  simp only [fitPow, fit, modelCost, ENNReal.rpow_two]

/-- `betaPow μ k T 2 z r = betaSq μ k T z r` for every family, source, centre and
radius. -/
theorem f3_betaPow_two_eq_betaSq_proof : BetaPowTwoStatement := by
  intro n _ k _ _ T μ z r
  unfold betaPow betaSq
  split_ifs with hr
  · simp only [f3_fitPow_two]
    congr 1
    rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring, ENNReal.rpow_natCast]
  · rfl

end ParabolicRectifiability.Foundations
