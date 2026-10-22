import ParabolicRectifiability.BetaP.Statements.Laws

/-! # Empty testing ball and restriction laws

* `EmptyTestingBallStatement`: a testing ball of zero source mass makes
  every `fitPow` vanish, so the infimum over a nonempty family is `0` and `B_p = 0`; the
  nonpositive-radius branch is `0` by definition.
* `BetaPowRestrictionStatement`: `μ.restrict E ≤ μ`, so every `fitPow`
  decreases, hence `B_p`, the monotone power `B_p^{2/p}` (`2/p > 0`) and both scale integrals.
  The availability hypothesis is not used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- `B_p` at a positive radius. -/
theorem claws_betaPow_of_pos {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ)
    (z : Space n) {r : ℝ} (hr : 0 < r) :
    betaPow μ k T p z r =
      (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) * ⨅ L : Models n k T, fitPow μ p L z r := by
  simp only [betaPow, hr, ↓reduceIte]

/-- A ball of zero mass has zero `p`-fitting integral, for every model and exponent. -/
theorem claws_fitPow_eq_zero_of_ball {n k : ℕ} {T : FamilyKind} {μ : Measure (Space n)}
    {p : ℝ} (L : Models n k T) {z : Space n} {r : ℝ} (h : μ (Metric.ball z r) = 0) :
    fitPow μ p L z r = 0 :=
  setLIntegral_measure_zero _ _ h

/-- For a nonempty family, a ball of zero mass has `B_p = 0` (every radius). -/
theorem claws_betaPow_eq_zero_of_ball {n k : ℕ} {T : FamilyKind} [Nonempty (Models n k T)]
    {μ : Measure (Space n)} {p : ℝ} {z : Space n} {r : ℝ} (h : μ (Metric.ball z r) = 0) :
    betaPow μ k T p z r = 0 := by
  unfold betaPow
  split_ifs
  · simp only [claws_fitPow_eq_zero_of_ball _ h, iInf_const, mul_zero]
  · rfl

/-- Empty testing ball. -/
theorem claws_emptyTestingBall_proof : EmptyTestingBallStatement := by
  intro n _ k _ _ T hT μ p _ z r h
  have := hT
  exact claws_betaPow_eq_zero_of_ball (T := T) h

/-- `fitPow` is monotone in the source measure. -/
theorem claws_fitPow_mono_measure {n k : ℕ} {T : FamilyKind} {ν μ : Measure (Space n)}
    (h : ν ≤ μ) (p : ℝ) (L : Models n k T) (z : Space n) (r : ℝ) :
    fitPow ν p L z r ≤ fitPow μ p L z r :=
  lintegral_mono' (Measure.restrict_mono_measure h _) le_rfl

/-- `B_p` is monotone in the source measure (every family, centre and radius). -/
theorem claws_betaPow_mono_measure {n : ℕ} {ν μ : Measure (Space n)} (h : ν ≤ μ) (k : ℕ)
    (T : FamilyKind) (p : ℝ) (z : Space n) (r : ℝ) :
    betaPow ν k T p z r ≤ betaPow μ k T p z r := by
  unfold betaPow
  split_ifs
  · exact mul_le_mul' le_rfl (iInf_mono fun L => claws_fitPow_mono_measure h p L z r)
  · exact le_rfl

/-- Monotonicity under restriction of the source. -/
theorem claws_restriction_proof : BetaPowRestrictionStatement := by
  intro n _ k _ _ T _ μ E p hp
  have hle : μ.restrict E ≤ μ := Measure.restrict_le_self
  refine ⟨fun z r => claws_betaPow_mono_measure hle k T p z r, fun a _ z => ⟨?_, ?_⟩⟩
  · exact lintegral_mono fun r =>
      ENNReal.rpow_le_rpow (claws_betaPow_mono_measure hle k T p z r) (div_pos two_pos hp).le
  · exact lintegral_mono fun r => claws_betaPow_mono_measure hle k T p z r

end ParabolicRectifiability.BetaP
