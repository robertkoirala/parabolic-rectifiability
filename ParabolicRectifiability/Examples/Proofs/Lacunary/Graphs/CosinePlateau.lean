import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Cosine plateaus in an arbitrary open period

The indicator of a measurable periodic set has the same integral on every full
period. Positive dilation then gives the exact inverse-frequency factor. For
cosine, explicit intervals of length `2π/3` lie in each of the two plateaus.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

private theorem e2_indicator_interval_eq_measureReal (S : Set ℝ) (hS : MeasurableSet S)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, S.indicator (fun _ => (1 : ℝ)) x) = volume.real (S ∩ Ioo a b) := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    integral_indicator_const 1 hS, smul_eq_mul, mul_one, measureReal_restrict_apply hS]

/-- Transport a lower bound from one period to an arbitrary positively scaled period. -/
private theorem e2_periodic_set_scaled_lower (S : Set ℝ) (hS : MeasurableSet S)
    (hperiod : Function.Periodic (S.indicator (fun _ => (1 : ℝ))) (2 * Real.pi))
    (a : ℝ) (hbase : 2 * Real.pi / 3 ≤ volume.real (S ∩ Ioo a (a + 2 * Real.pi)))
    (ω : ℝ) (hω : 0 < ω) (t : ℝ) :
    ENNReal.ofReal (2 * Real.pi / (3 * ω)) ≤
      volume ((fun s : ℝ => ω * s) ⁻¹' S ∩ Ioo (t - Real.pi / ω) (t + Real.pi / ω)) := by
  have hpre : MeasurableSet ((fun s : ℝ => ω * s) ⁻¹' S) :=
    hS.preimage (continuous_const.mul continuous_id).measurable
  have hwin : t - Real.pi / ω ≤ t + Real.pi / ω := by
    have := div_pos Real.pi_pos hω
    linarith
  have hind : ((fun s : ℝ => ω * s) ⁻¹' S).indicator (fun _ => (1 : ℝ)) =
      fun s => S.indicator (fun _ => (1 : ℝ)) (ω * s) := by
    rfl
  have hend : ω * (t + Real.pi / ω) = ω * (t - Real.pi / ω) + 2 * Real.pi := by
    field_simp
    ring
  apply ENNReal.ofReal_le_of_le_toReal
  change 2 * Real.pi / (3 * ω) ≤ volume.real _
  rw [← e2_indicator_interval_eq_measureReal _ hpre hwin, hind,
    intervalIntegral.integral_comp_mul_left _ hω.ne', hend,
    hperiod.intervalIntegral_add_eq _ a,
    e2_indicator_interval_eq_measureReal S hS (by linarith [Real.pi_pos]), smul_eq_mul]
  calc
    2 * Real.pi / (3 * ω) = ω⁻¹ * (2 * Real.pi / 3) := by ring
    _ ≤ ω⁻¹ * volume.real (S ∩ Ioo a (a + 2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hω.le)

private theorem e2_cos_half_le_of_abs_le {x : ℝ} (hx : |x| ≤ Real.pi / 3) :
    1 / 2 ≤ Real.cos x := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
    (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hx
  simpa only [Real.cos_pi_div_three, Real.cos_abs] using h

/-- Each cosine plateau occupies at least one third of every open period. -/
theorem e2_cosPlateau_proof : E2CosPlateauStatement := by
  intro ω hω t
  have hpos : MeasurableSet {x : ℝ | 1 / 2 ≤ Real.cos x} :=
    isClosed_le continuous_const Real.continuous_cos |>.measurableSet
  have hneg : MeasurableSet {x : ℝ | Real.cos x ≤ -(1 / 2)} :=
    isClosed_le Real.continuous_cos continuous_const |>.measurableSet
  have hp_period : Function.Periodic
      ({x : ℝ | 1 / 2 ≤ Real.cos x}.indicator (fun _ => (1 : ℝ))) (2 * Real.pi) := by
    intro x
    simp only [Set.indicator, mem_ofPred_eq, Real.cos_periodic x]
  have hn_period : Function.Periodic
      ({x : ℝ | Real.cos x ≤ -(1 / 2)}.indicator (fun _ => (1 : ℝ))) (2 * Real.pi) := by
    intro x
    simp only [Set.indicator, mem_ofPred_eq, Real.cos_periodic x]
  have hp_sub : Ioo (-(Real.pi / 3)) (Real.pi / 3) ⊆
      {x : ℝ | 1 / 2 ≤ Real.cos x} ∩ Ioo (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    intro x hx
    refine ⟨e2_cos_half_le_of_abs_le (abs_le.mpr ⟨hx.1.le, hx.2.le⟩), ?_⟩
    constructor <;> linarith [Real.pi_pos, hx.1, hx.2]
  have hn_sub : Ioo (2 * Real.pi / 3) (4 * Real.pi / 3) ⊆
      {x : ℝ | Real.cos x ≤ -(1 / 2)} ∩ Ioo 0 (0 + 2 * Real.pi) := by
    intro x hx
    have hc := e2_cos_half_le_of_abs_le (x := x - Real.pi)
      (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    rw [Real.cos_sub_pi] at hc
    refine ⟨by change Real.cos x ≤ -(1 / 2); linarith, ?_⟩
    constructor <;> linarith [Real.pi_pos, hx.1, hx.2]
  have hp_base : 2 * Real.pi / 3 ≤ volume.real
      ({x : ℝ | 1 / 2 ≤ Real.cos x} ∩ Ioo (-Real.pi) (-Real.pi + 2 * Real.pi)) := by
    have hm := measureReal_mono (μ := volume) hp_sub
      (ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (measure_mono inter_subset_right))
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])] at hm
    convert hm using 1
    ring
  have hn_base : 2 * Real.pi / 3 ≤ volume.real
      ({x : ℝ | Real.cos x ≤ -(1 / 2)} ∩ Ioo 0 (0 + 2 * Real.pi)) := by
    have hm := measureReal_mono (μ := volume) hn_sub
      (ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
        (measure_mono inter_subset_right))
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])] at hm
    convert hm using 1
    ring
  exact ⟨e2_periodic_set_scaled_lower _ hpos hp_period (-Real.pi) hp_base ω hω t,
    e2_periodic_set_scaled_lower _ hneg hn_period 0 hn_base ω hω t⟩

end ParabolicRectifiability.Examples
