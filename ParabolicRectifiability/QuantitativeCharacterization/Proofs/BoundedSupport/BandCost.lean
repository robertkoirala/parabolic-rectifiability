import ParabolicRectifiability.QuantitativeCharacterization.Statements.BoundedSupportComponents
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds

/-! # The cost of the declared-bad band

Proof of the statement `dp2_band_cost` (`dp2_BandCostStatement`).

Proof idea: `Measure.prod_prod` (only `SFinite scaleMeasure` is needed, so `S` is arbitrary); the
`dr/r` measure of `[r, R)` is at most `log (R / r)` (`bf1m45_scaleMeasure_Ioo` plus the null
singleton `{r}`); and `r ^ k * log (R / r) ≤ R ^ k` since `log x ≤ x - 1 ≤ x ≤ x ^ k` for
`x = R / r ≥ 1` and `k ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- The `dr/r` measure of `[r, R)` is at most `log (R / r)` for `0 < r ≤ R`. -/
theorem dp2_scaleMeasure_Ico_le {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    scaleMeasure (Ico r R) ≤ ENNReal.ofReal (Real.log (R / r)) := by
  calc scaleMeasure (Ico r R) ≤ scaleMeasure (Ioo r R ∪ {r}) := by
        refine measure_mono fun x hx => ?_
        rcases hx.1.eq_or_lt with h | h
        · exact Or.inr h.symm
        · exact Or.inl ⟨h, hx.2⟩
    _ ≤ scaleMeasure (Ioo r R) + scaleMeasure {r} := measure_union_le _ _
    _ = ENNReal.ofReal (Real.log (R / r)) := by
        rw [Foundations.bf1m45_scaleMeasure_Ioo hr hrR, scaleMeasure_singleton, add_zero]

/-- The real inequality `Q r ^ k log (R / r) ≤ Q R ^ k` for `k ≥ 1`, `0 ≤ Q`, `0 < r ≤ R`. -/
theorem dp2_band_real {k : ℕ} (hk : 1 ≤ k) {Q r R : ℝ} (hQ : 0 ≤ Q) (hr : 0 < r) (hrR : r ≤ R) :
    Q * r ^ k * Real.log (R / r) ≤ Q * R ^ k := by
  have hx : 1 ≤ R / r := (one_le_div hr).2 hrR
  have hlog : Real.log (R / r) ≤ (R / r) ^ k :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans
      ((by linarith : R / r - 1 ≤ R / r).trans (le_self_pow₀ hx (by omega)))
  have hpow : r ^ k * (R / r) ^ k = R ^ k := by
    rw [← mul_pow]; field_simp
  calc Q * r ^ k * Real.log (R / r) ≤ Q * r ^ k * (R / r) ^ k := by gcongr
    _ = Q * R ^ k := by rw [mul_assoc, hpow]

/-- **The cost of the declared-bad band.** Proof of `dp2_BandCostStatement`. -/
theorem dp2_band_cost_proof : dp2_BandCostStatement := by
  intro n k hk μ S Q r R hQ hr hrR hS
  rw [pointScaleMeasure, Measure.prod_prod]
  calc μ S * scaleMeasure (Ico r R)
      ≤ ENNReal.ofReal (Q * r ^ k) * ENNReal.ofReal (Real.log (R / r)) :=
        mul_le_mul' hS (dp2_scaleMeasure_Ico_le hr hrR)
    _ = ENNReal.ofReal (Q * r ^ k * Real.log (R / r)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (Q * R ^ k) := ENNReal.ofReal_le_ofReal (dp2_band_real hk hQ hr hrR)

end ParabolicRectifiability.QuantitativeCharacterization
