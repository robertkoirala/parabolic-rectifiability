import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements

/-! # The capped-value limit

Proof of `i2_CappedValueLimitStatement`, the auxiliary statement `i2_cappedValue_limit`.

Route:
1. for `L > 0` the factor `(ofReal L)⁻¹ ≠ ∞` moves inside the integral (`lintegral_const_mul'`);
2. the new integrand `(ofReal L)⁻¹ * min{S, L}` lies in `[0, 1]`; it is eventually `1` where
   `S = ∞` and is squeezed by `(ofReal L)⁻¹ * S → 0` where `S < ∞`; so it tends to `1_{S = ∞}`;
3. dominated convergence along the countably generated filter `atTop` on `ℝ` for `μ.restrict A`,
   with bound `1` and `μ A < ∞` (`A` bounded, `IsFiniteMeasureOnCompacts`), and
   `∫_A 1_{S=∞} dμ = μ(A ∩ {S = ∞})` (`lintegral_indicator_const`, `{S = ∞}` Borel).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- Pointwise limit of the normalised cap: `(ofReal L)⁻¹ * min{s, L} → 1_{s = ∞}` as `L → ∞`. -/
theorem i2_cv_tendsto_inv_mul_min (s : ℝ≥0∞) :
    Tendsto (fun L : ℝ => (ENNReal.ofReal L)⁻¹ * min s (ENNReal.ofReal L)) atTop
      (𝓝 ({u : ℝ≥0∞ | u = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) s)) := by
  by_cases hs : s = ⊤
  · have h1 : {u : ℝ≥0∞ | u = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) s = 1 :=
      indicator_of_mem (show s ∈ {u : ℝ≥0∞ | u = ⊤} from hs) _
    rw [h1]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [hs, min_eq_right le_top, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hL).ne'
      ENNReal.ofReal_ne_top]
  · have h0 : {u : ℝ≥0∞ | u = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) s = 0 :=
      indicator_of_notMem (show s ∉ {u : ℝ≥0∞ | u = ⊤} from hs) _
    rw [h0]
    have hinv : Tendsto (fun L : ℝ => (ENNReal.ofReal L)⁻¹) atTop (𝓝 0) := by
      rw [← ENNReal.inv_top]
      exact tendsto_inv_iff.2 ENNReal.tendsto_ofReal_atTop
    have hup : Tendsto (fun L : ℝ => (ENNReal.ofReal L)⁻¹ * s) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hinv (Or.inr hs)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => zero_le) (fun L => mul_le_mul_right (min_le_left _ _) _)

/-- **Limit of the capped values** (`i2_cappedValue_limit`). -/
theorem i2_cappedValue_limit_proof : i2_CappedValueLimitStatement := by
  intro n _ k _ _ μ hμ _ T _ R _ A _ hAb
  have := hμ
  set S := squareEnergy μ k T R with hS
  have hSm : Measurable S := measurable_squareEnergy μ k T R
  have hN : MeasurableSet {z | S z = ⊤} := measurableSet_eq_fun hSm measurable_const
  -- the limit is the integral of the indicator of `{S = ∞}` over `A`
  have hlimval : ∫⁻ z in A, {u : ℝ≥0∞ | u = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) (S z) ∂μ
      = μ (A ∩ {z | S z = ⊤}) := by
    have : (fun z => {u : ℝ≥0∞ | u = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) (S z))
        = {z | S z = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext z
      by_cases hz : S z = ⊤
      · rw [indicator_of_mem (show S z ∈ {u : ℝ≥0∞ | u = ⊤} from hz),
          indicator_of_mem (show z ∈ {z | S z = ⊤} from hz)]
      · rw [indicator_of_notMem (show S z ∉ {u : ℝ≥0∞ | u = ⊤} from hz),
          indicator_of_notMem (show z ∉ {z | S z = ⊤} from hz)]
    rw [this, lintegral_indicator_const hN, one_mul, Measure.restrict_apply hN, inter_comm]
  rw [← hlimval]
  -- step 1: for `L > 0` move the factor inside
  have hcongr : (fun L : ℝ => ∫⁻ z in A, (ENNReal.ofReal L)⁻¹ * min (S z) (ENNReal.ofReal L) ∂μ)
      =ᶠ[atTop] fun L : ℝ =>
        (ENNReal.ofReal L)⁻¹ * ∫⁻ z in A, min (S z) (ENNReal.ofReal L) ∂μ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hL).ne')
  refine Tendsto.congr' hcongr ?_
  -- steps 2-3: dominated convergence with bound `1`
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun L => measurable_const.mul (hSm.min measurable_const)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    refine ae_of_all _ fun z => ?_
    calc (ENNReal.ofReal L)⁻¹ * min (S z) (ENNReal.ofReal L)
        ≤ (ENNReal.ofReal L)⁻¹ * ENNReal.ofReal L := mul_le_mul_right (min_le_right _ _) _
      _ = 1 := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hL).ne' ENNReal.ofReal_ne_top
  · rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
    exact (hAb.measure_lt_top (μ := μ)).ne
  · exact ae_of_all _ fun z => i2_cv_tendsto_inv_mul_min (S z)

end ParabolicRectifiability.IntegralCanonical
