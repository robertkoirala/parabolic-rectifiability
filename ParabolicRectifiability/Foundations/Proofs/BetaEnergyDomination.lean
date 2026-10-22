import ParabolicRectifiability.Measure.BetaLaws

/-! # Beta domination under measure domination

Proof of `fmeas3_betaSq_le_of_le_ofReal_smul`: the type of
`fmeas3_betaSq_le_of_le_ofReal_smul_proof` is that of the statement of beta domination
under measure domination.

Route: `r ≤ 0` gives `0 ≤ _` (`betaSq_of_nonpos`); `r > 0` with an available family gives
`betaSq_mono_measure` and `betaSq_smul` (with the `Nonempty` instance installed); `r > 0`
with an unavailable family gives `betaSq_of_isEmpty` and `ENNReal.mul_top` (`c > 0` essential).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Available family: monotonicity and finite-scalar homogeneity. -/
theorem fm3_betaSq_le_of_nonempty {n : ℕ} (k : ℕ) (T : FamilyKind)
    [Nonempty (Models n k T)] {μ ν : Measure (Space n)} {c : ℝ}
    (h : ν ≤ ENNReal.ofReal c • μ) (z : Space n) (r : ℝ) :
    betaSq ν k T z r ≤ ENNReal.ofReal c * betaSq μ k T z r := by
  calc betaSq ν k T z r ≤ betaSq (ENNReal.ofReal c • μ) k T z r :=
        betaSq_mono_measure h k T z r
    _ = ENNReal.ofReal c * betaSq μ k T z r :=
        betaSq_smul μ (ENNReal.ofReal c) ENNReal.ofReal_ne_top k T z r

/-- Unavailable family, positive radius: the right side is `ofReal c * ⊤ = ⊤`. -/
theorem fm3_betaSq_le_of_isEmpty {n : ℕ} (k : ℕ) (T : FamilyKind)
    [IsEmpty (Models n k T)] {μ ν : Measure (Space n)} {c : ℝ} (hc : 0 < c)
    (z : Space n) {r : ℝ} (hr : 0 < r) :
    betaSq ν k T z r ≤ ENNReal.ofReal c * betaSq μ k T z r := by
  rw [betaSq_of_isEmpty μ k T z hr, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']
  exact le_top

theorem fmeas3_betaSq_le_of_le_ofReal_smul_proof {n : ℕ} (k : ℕ) (T : FamilyKind)
    {μ ν : Measure (Space n)} {c : ℝ} (hc : 0 < c) (h : ν ≤ ENNReal.ofReal c • μ)
    (z : Space n) (r : ℝ) :
    betaSq ν k T z r ≤ ENNReal.ofReal c * betaSq μ k T z r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [betaSq_of_nonpos ν k T z hr]
    exact zero_le
  · rcases isEmpty_or_nonempty (Models n k T) with hE | hN
    · exact fm3_betaSq_le_of_isEmpty k T hc z hr
    · exact fm3_betaSq_le_of_nonempty k T h z r

end ParabolicRectifiability.Foundations
