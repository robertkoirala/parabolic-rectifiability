module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Scalar normalization for the half-time derivative

For the Fourier character `exp (-2 * π * I * h * τ)`, the normalization
integrand is `(1 - cos (2 * π * h)) * |h| ^ (-3 / 2 : ℝ)`.
Quadratic cancellation controls the origin, while the power `-3 / 2`
is integrable in the tails. Positivity near `h = 1 / 2` then gives a
strictly positive normalization integral.

This is the normalization of the fractional kernel of the half-time
derivative; the constant is `kappa`. All integrals use ordinary real Lebesgue measure.
Frequency scaling, complex multiplier identities and truncation limits are
subsequent results; none is assumed here.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace ParabolicRectifiability.FractionalKernel

/-- The real integrand defining the half-derivative normalization. The power
is `Real.rpow`; in particular its negative-power factor is zero at zero. -/
def normalizationIntegrand (h : ℝ) : ℝ :=
  (1 - Real.cos (2 * Real.pi * h)) * |h| ^ (-3 / 2 : ℝ)

@[simp]
theorem normalizationIntegrand_zero : normalizationIntegrand 0 = 0 := by
  simp [normalizationIntegrand]

theorem measurable_normalizationIntegrand : Measurable normalizationIntegrand := by
  unfold normalizationIntegrand
  fun_prop

theorem normalizationIntegrand_nonneg (h : ℝ) : 0 ≤ normalizationIntegrand h :=
  mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Real.rpow_nonneg (abs_nonneg _) _)

@[simp]
theorem normalizationIntegrand_neg (h : ℝ) :
    normalizationIntegrand (-h) = normalizationIntegrand h := by
  simp [normalizationIntegrand]

/-- The quadratic cancellation bound, with the `2π` convention of the Fourier phase. -/
theorem one_sub_cos_two_pi_mul_le (h : ℝ) :
    1 - Real.cos (2 * Real.pi * h) ≤ 2 * Real.pi ^ 2 * h ^ 2 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * h)
  nlinarith

/-- Cancellation controls the singular kernel by a positive half power.
The estimate includes zero and holds globally, so it can be restricted to
any neighborhood of zero. -/
theorem normalizationIntegrand_le_rpow_half (h : ℝ) :
    normalizationIntegrand h ≤ 2 * Real.pi ^ 2 * |h| ^ (1 / 2 : ℝ) := by
  calc
    normalizationIntegrand h ≤ (2 * Real.pi ^ 2 * h ^ 2) * |h| ^ (-3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (one_sub_cos_two_pi_mul_le h)
        (Real.rpow_nonneg (abs_nonneg _) _)
    _ = 2 * Real.pi ^ 2 * |h| ^ (1 / 2 : ℝ) := by
      rw [← sq_abs h, mul_assoc, ← Real.rpow_two |h|,
        ← Real.rpow_add' (abs_nonneg h) (by norm_num : (2 : ℝ) + (-3 / 2) ≠ 0)]
      norm_num

/-- The bounded cosine numerator gives the integrable far-tail majorant. -/
theorem normalizationIntegrand_le_rpow_neg_three_halves (h : ℝ) :
    normalizationIntegrand h ≤ 2 * |h| ^ (-3 / 2 : ℝ) := by
  exact mul_le_mul_of_nonneg_right (by linarith [Real.neg_one_le_cos (2 * Real.pi * h)])
    (Real.rpow_nonneg (abs_nonneg _) _)

theorem continuousAt_normalizationIntegrand {h : ℝ} (hh : h ≠ 0) :
    ContinuousAt normalizationIntegrand h := by
  unfold normalizationIntegrand
  apply ContinuousAt.mul
  · fun_prop
  · exact continuous_abs.continuousAt.rpow_const (Or.inl (abs_ne_zero.mpr hh))

/-- Absolute integrability is proved before using the total Bochner integral. -/
theorem integrable_normalizationIntegrand : Integrable normalizationIntegrand volume := by
  have hmajor : IntegrableOn (fun h : ℝ => 2 * Real.pi ^ 2 * |h| ^ (1 / 2 : ℝ))
      (Icc (0 : ℝ) 1) :=
    (continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by norm_num)))).integrableOn_Icc
  have hnear : IntegrableOn normalizationIntegrand (Icc (0 : ℝ) 1) := by
    apply hmajor.mono' measurable_normalizationIntegrand.aestronglyMeasurable
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (normalizationIntegrand_nonneg h)]
      exact normalizationIntegrand_le_rpow_half h
  have hmajorTail : IntegrableOn (fun h : ℝ => 2 * h ^ (-3 / 2 : ℝ)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul 2
  have htail : IntegrableOn normalizationIntegrand (Ioi (1 : ℝ)) := by
    apply hmajorTail.mono' measurable_normalizationIntegrand.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (normalizationIntegrand_nonneg h)]
    have hh' : 0 < h := lt_trans (by norm_num : (0 : ℝ) < 1) hh
    simpa [abs_of_pos hh'] using
      normalizationIntegrand_le_rpow_neg_three_halves h
  have hpos : IntegrableOn normalizationIntegrand (Ioi (0 : ℝ)) := by
    apply (hnear.union htail).mono_set
    intro h hh
    by_cases hle : h ≤ 1
    · exact Or.inl ⟨le_of_lt hh, hle⟩
    · exact Or.inr (lt_of_not_ge hle)
  have hneg : IntegrableOn normalizationIntegrand (Iic (0 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding (fun h : ℝ => -h) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp only [Function.comp_def, normalizationIntegrand_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  simpa only [Iic_union_Ioi, integrableOn_univ] using hneg.union hpos

theorem normalizationIntegrand_half_pos : 0 < normalizationIntegrand (1 / 2) := by
  unfold normalizationIntegrand
  have harg : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  rw [harg, Real.cos_pi]
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)

/-- Strict positivity comes from a neighborhood of `1/2`, not from a
nonzero value at a single point of Lebesgue measure zero. -/
theorem integral_normalizationIntegrand_pos : 0 < ∫ h : ℝ, normalizationIntegrand h := by
  apply (integral_pos_iff_support_of_nonneg normalizationIntegrand_nonneg
    integrable_normalizationIntegrand).mpr
  apply Measure.measure_pos_of_mem_nhds
  exact (continuousAt_normalizationIntegrand (by norm_num : (1 / 2 : ℝ) ≠ 0)).eventually_ne
    normalizationIntegrand_half_pos.ne'

/-- Positive normalization constant for the `exp (-2π i h τ)` convention. -/
def kappa : ℝ := (∫ h : ℝ, normalizationIntegrand h)⁻¹

theorem kappa_pos : 0 < kappa := inv_pos.mpr integral_normalizationIntegrand_pos

theorem kappa_ne_zero : kappa ≠ 0 := ne_of_gt kappa_pos

theorem kappa_mul_integral_normalizationIntegrand :
    kappa * (∫ h : ℝ, normalizationIntegrand h) = 1 :=
  inv_mul_cancel₀ integral_normalizationIntegrand_pos.ne'

end ParabolicRectifiability.FractionalKernel
