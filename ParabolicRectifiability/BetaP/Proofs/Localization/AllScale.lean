import ParabolicRectifiability.BetaP.Proofs.Localization.LocalizationStatements

/-! # The all-scale bound `2M` of a small restriction

Proves `cloc_allScale_proof : ClocAllScaleStatement`, the
implication form whose inputs are `BetaPowRestrictionStatement` and
`ClocPTailStatement` (both hypotheses of the statement).

The proof is the quadratic `allScaleEnergy_restrict_le_two_mul` with `B_p^{2/p}` in place of
`betaSq`:
* `(0,2)`: `S^2_{p,μ⌊G}(z) ≤ S^2_{p,μ}(z) ≤ M` (restriction law at endpoint `2`);
* the support of `μ⌊G` is compact of diameter `≤ 1/32 < 1`;
* `(2,∞)`: `(2^{q_p} - 1)^{-1}` times the `(1,2)` part (exact tail), and the factor is `≤ 1`
  since `q_p ≥ 2`; the `(1,2)` part is at most the `(0,2)` part, hence `≤ M`;
* the endpoint `2` is `scaleMeasure`-null. Total `≤ 2M`, also at `M = 0`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The tail factor `(2^{q_p} - 1)^{-1}` is at most one, since `q_p = 2 + 2k/p ≥ 2`. -/
theorem clocp_tailFactor_le_one (k : ℕ) {p : ℝ} (hp : 0 < p) :
    (ENNReal.ofReal ((2 : ℝ) ^ (2 + 2 * (k : ℝ) / p) - 1))⁻¹ ≤ 1 := by
  have hq2 : (2 : ℝ) ≤ 2 + 2 * (k : ℝ) / p :=
    le_add_of_nonneg_right (div_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg k)) hp.le)
  have hpow : (4 : ℝ) ≤ 2 ^ (2 + 2 * (k : ℝ) / p) := by
    calc (4 : ℝ) = 2 ^ (2 : ℝ) := by rw [Real.rpow_two]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two hq2
  exact ENNReal.inv_le_one.mpr (ENNReal.one_le_ofReal.mpr (by linarith))

/-- **All-scale bound `2M`** (`ClocAllScaleStatement`, in implication form). -/
theorem cloc_allScale_proof : ClocAllScaleStatement := by
  intro hR hTail n hn k hk hkn T hT μ p hp M hM G c hsupp z hz hzM
  set ν := μ.restrict G with hν
  -- the `(0,2)` square of the restriction is at most `M`
  have hlow : ∫⁻ r in Ioo (0 : ℝ) 2, betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure ≤
      ENNReal.ofReal M :=
    (((hR n hn k hk hkn T hT μ G p hp).2 2 two_pos z).1).trans hzM
  -- compact support of diameter at most `1/32 < 1`
  have hc : IsCompact ν.support :=
    (isCompact_closedBall c (1 / 64)).of_isClosed_subset Measure.isClosed_support hsupp
  have hd : Metric.diam ν.support < 1 :=
    (Metric.diam_mono hsupp Metric.isBounded_closedBall).trans_lt
      ((Metric.diam_closedBall (by norm_num : (0 : ℝ) ≤ 1 / 64)).trans_lt (by norm_num))
  -- the exact tail identity, with factor at most one
  have htail := hTail ν k T p hp hc hd hz
  have hhigh : ∫⁻ r in Ioi (2 : ℝ), betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure ≤
      ENNReal.ofReal M := by
    rw [htail]
    calc
      _ ≤ 1 * ∫⁻ r in Ioo (1 : ℝ) 2, betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure := by
        gcongr
        exact clocp_tailFactor_le_one k hp
      _ = ∫⁻ r in Ioo (1 : ℝ) 2, betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure := one_mul _
      _ ≤ ∫⁻ r in Ioo (0 : ℝ) 2, betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure :=
        lintegral_mono_set (Ioo_subset_Ioo_left zero_le_one)
      _ ≤ ENNReal.ofReal M := hlow
  -- split the positive scales at the null endpoint `2`
  have hsplit : Ioi (0 : ℝ) ⊆ Ioo 0 2 ∪ Ici 2 := by
    intro r hr
    by_cases h : r < 2
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr (le_of_not_gt h)
  have hIci : ∫⁻ r in Ici (2 : ℝ), betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure =
      ∫⁻ r in Ioi (2 : ℝ), betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure :=
    setLIntegral_congr (Ioi_ae_eq_Ici' (scaleMeasure_singleton 2)).symm
  calc
    allScaleEnergyP ν k T p z =
        ∫⁻ r in Ioi (0 : ℝ), betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure := rfl
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) 2 ∪ Ici 2, betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure :=
      lintegral_mono_set hsplit
    _ ≤ (∫⁻ r in Ioo (0 : ℝ) 2, betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure) +
          ∫⁻ r in Ici (2 : ℝ), betaPow ν k T p z r ^ (2 / p) ∂scaleMeasure :=
      lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal M := by
      rw [hIci]
      exact add_le_add hlow hhigh
    _ = ENNReal.ofReal (2 * M) := by rw [two_mul, ENNReal.ofReal_add hM hM]

end ParabolicRectifiability.BetaP
