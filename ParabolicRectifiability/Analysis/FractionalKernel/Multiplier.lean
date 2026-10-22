module

public import ParabolicRectifiability.Analysis.FractionalKernel.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Scalar half-derivative multipliers

Ordinary Lebesgue measure and the Fourier phase `exp (-2 * π * I * τ * h)`.
The normalization is the one proved in `FractionalKernel.Basic`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace ParabolicRectifiability.FractionalKernel

/-- The real frequency integrand, using Lean's real powers also at zero. -/
def frequencyIntegrand (τ h : ℝ) : ℝ :=
  (1 - Real.cos (2 * Real.pi * τ * h)) * |h| ^ (-3 / 2 : ℝ)

@[simp] theorem frequencyIntegrand_zero (τ : ℝ) : frequencyIntegrand τ 0 = 0 := by
  simp [frequencyIntegrand]

@[simp] theorem frequencyIntegrand_zero_frequency (h : ℝ) :
    frequencyIntegrand 0 h = 0 := by
  simp [frequencyIntegrand]

theorem measurable_frequencyIntegrand (τ : ℝ) : Measurable (frequencyIntegrand τ) := by
  unfold frequencyIntegrand
  fun_prop

theorem frequencyIntegrand_nonneg (τ h : ℝ) : 0 ≤ frequencyIntegrand τ h :=
  mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Real.rpow_nonneg (abs_nonneg _) _)

@[simp] theorem frequencyIntegrand_neg (τ h : ℝ) :
    frequencyIntegrand τ (-h) = frequencyIntegrand τ h := by
  simp [frequencyIntegrand]

/-- Dilation identity, pointwise including `h = 0`; only the frequency is nonzero. -/
theorem frequencyIntegrand_dilation {τ : ℝ} (hτ : τ ≠ 0) (h : ℝ) :
    frequencyIntegrand τ h =
      |τ| ^ (3 / 2 : ℝ) * normalizationIntegrand (|τ| * h) := by
  have ha : 0 < |τ| := abs_pos.mpr hτ
  have hc : Real.cos (2 * Real.pi * (|τ| * h)) =
      Real.cos (2 * Real.pi * τ * h) := by
    rcases le_or_gt 0 τ with hpos | hneg
    · rw [abs_of_nonneg hpos]; congr 1; ring
    · rw [abs_of_neg hneg]
      convert Real.cos_neg (2 * Real.pi * τ * h) using 1; congr 1; ring
  unfold frequencyIntegrand normalizationIntegrand
  rw [hc, abs_mul, abs_abs, Real.mul_rpow (abs_nonneg τ) (abs_nonneg h)]
  have hp : |τ| ^ (3 / 2 : ℝ) * |τ| ^ (-3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add ha]; norm_num
  calc
    _ = (|τ| ^ (3 / 2 : ℝ) * |τ| ^ (-3 / 2 : ℝ)) *
        ((1 - Real.cos (2 * Real.pi * τ * h)) * |h| ^ (-3 / 2 : ℝ)) := by
      rw [hp, one_mul]
    _ = _ := by ring

theorem integrable_frequencyIntegrand (τ : ℝ) : Integrable (frequencyIntegrand τ) volume := by
  by_cases hτ : τ = 0
  · subst τ
    apply (integrable_zero ℝ ℝ volume).congr
    exact Eventually.of_forall fun h => by simp
  · simpa only [← frequencyIntegrand_dilation hτ] using
      (integrable_normalizationIntegrand.comp_mul_left' (abs_ne_zero.mpr hτ)).const_mul
        (|τ| ^ (3 / 2 : ℝ))

/-- The real multiplier at every frequency, including zero. -/
theorem kappa_mul_integral_frequencyIntegrand (τ : ℝ) :
    kappa * (∫ h : ℝ, frequencyIntegrand τ h) = |τ| ^ (1 / 2 : ℝ) := by
  by_cases hτ : τ = 0
  · subst τ; simp
  have ha : 0 < |τ| := abs_pos.mpr hτ
  have hp : |τ| ^ (3 / 2 : ℝ) * |(|τ|)⁻¹| = |τ| ^ (1 / 2 : ℝ) := by
    rw [abs_of_pos (inv_pos.mpr ha), ← Real.rpow_neg_one, ← Real.rpow_add ha]
    norm_num
  simp_rw [frequencyIntegrand_dilation hτ]
  rw [integral_const_mul, Measure.integral_comp_mul_left, smul_eq_mul]
  calc
    _ = (|τ| ^ (3 / 2 : ℝ) * |(|τ|)⁻¹|) *
        (kappa * ∫ h : ℝ, normalizationIntegrand h) := by ring
    _ = _ := by rw [hp, kappa_mul_integral_normalizationIntegrand, mul_one]

/-- The imaginary component of the Fourier integrand. -/
def sineIntegrand (τ h : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * τ * h) * |h| ^ (-3 / 2 : ℝ)

@[simp] theorem sineIntegrand_zero (τ : ℝ) : sineIntegrand τ 0 = 0 := by
  simp [sineIntegrand]

@[simp] theorem sineIntegrand_neg (τ h : ℝ) :
    sineIntegrand τ (-h) = -sineIntegrand τ h := by
  simp [sineIntegrand]

theorem measurable_sineIntegrand (τ : ℝ) : Measurable (sineIntegrand τ) := by
  unfold sineIntegrand
  fun_prop

/-- Near zero the absolute sine kernel is bounded by an integrable negative half-power. -/
theorem abs_sineIntegrand_le_rpow_neg_half (τ h : ℝ) :
    |sineIntegrand τ h| ≤ (2 * Real.pi * |τ|) * |h| ^ (-1 / 2 : ℝ) := by
  have hp : |h| * |h| ^ (-3 / 2 : ℝ) = |h| ^ (-1 / 2 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one |h|]
    rw [← Real.rpow_add' (abs_nonneg h) (by norm_num : (1 : ℝ) + (-3 / 2) ≠ 0)]
    norm_num
  calc
    |sineIntegrand τ h| = |Real.sin (2 * Real.pi * τ * h)| * |h| ^ (-3 / 2 : ℝ) := by
      rw [sineIntegrand, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
    _ ≤ |2 * Real.pi * τ * h| * |h| ^ (-3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right Real.abs_sin_le_abs (Real.rpow_nonneg (abs_nonneg h) _)
    _ = _ := by
      simp only [abs_mul, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [mul_assoc, hp]

/-- The far-tail bound, uniform in frequency. -/
theorem abs_sineIntegrand_le_rpow_neg_three_halves (τ h : ℝ) :
    |sineIntegrand τ h| ≤ |h| ^ (-3 / 2 : ℝ) := by
  rw [sineIntegrand, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
  simpa using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (2 * Real.pi * τ * h))
    (Real.rpow_nonneg (abs_nonneg h) (-3 / 2 : ℝ))

theorem integrable_sineIntegrand (τ : ℝ) : Integrable (sineIntegrand τ) volume := by
  have hnear : IntegrableOn (sineIntegrand τ) (Ioc (0 : ℝ) 1) := by
    have hmajor : IntegrableOn (fun h : ℝ => (2 * Real.pi * |τ|) * h ^ (-1 / 2 : ℝ))
        (Ioc (0 : ℝ) 1) :=
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2)
        (a := 0) (b := 1)).1).const_mul _
    apply hmajor.mono' (measurable_sineIntegrand τ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    simpa only [Real.norm_eq_abs, abs_of_pos hh.1] using abs_sineIntegrand_le_rpow_neg_half τ h
  have htail : IntegrableOn (sineIntegrand τ) (Ioi (1 : ℝ)) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).mono' (measurable_sineIntegrand τ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    simpa only [Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hh)] using
      abs_sineIntegrand_le_rpow_neg_three_halves τ h
  have hpos : IntegrableOn (sineIntegrand τ) (Ioi (0 : ℝ)) := by
    apply (hnear.union htail).mono_set
    intro h hh
    by_cases hle : h ≤ 1
    · exact Or.inl ⟨hh, hle⟩
    · exact Or.inr (lt_of_not_ge hle)
  have hneg : IntegrableOn (sineIntegrand τ) (Iic (0 : ℝ)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding (fun h : ℝ => -h) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simp only [Function.comp_def, sineIntegrand_neg, neg_preimage, neg_Iic, neg_zero]
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos).neg
  simpa only [Iic_union_Ioi, integrableOn_univ] using hneg.union hpos

/-- Reflection cancels the sine part on any measurable symmetric set. -/
theorem integral_sineIntegrand_of_symmetric (τ : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hsneg : ∀ h : ℝ, -h ∈ s ↔ h ∈ s) :
    ∫ h in s, sineIntegrand τ h = 0 := by
  have hodd : ∀ h : ℝ, s.indicator (sineIntegrand τ) (-h) =
      -(s.indicator (sineIntegrand τ) h) := by
    intro h
    by_cases hh : h ∈ s <;> simp [hh, hsneg h]
  have heq := integral_neg_eq_self (s.indicator (sineIntegrand τ)) (volume : Measure ℝ)
  simp_rw [hodd] at heq
  rw [integral_neg, integral_indicator hs] at heq
  linarith

theorem integral_sineIntegrand (τ : ℝ) : ∫ h : ℝ, sineIntegrand τ h = 0 := by
  simpa using integral_sineIntegrand_of_symmetric τ MeasurableSet.univ (by simp)

/-- Exact negative Fourier phase for ordinary Lebesgue measure on `ℝ`. -/
def complexFrequencyIntegrand (τ h : ℝ) : ℂ :=
  (1 - Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (h : ℂ))) *
    ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ)

theorem complexFrequencyIntegrand_eq (τ h : ℝ) :
    complexFrequencyIntegrand τ h =
      (frequencyIntegrand τ h : ℂ) + (sineIntegrand τ h : ℂ) * Complex.I := by
  unfold complexFrequencyIntegrand frequencyIntegrand sineIntegrand
  have he : -2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * (h : ℂ) =
      ((-(2 * Real.pi * τ * h) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

@[simp] theorem complexFrequencyIntegrand_zero (τ : ℝ) :
    complexFrequencyIntegrand τ 0 = 0 := by simp [complexFrequencyIntegrand]

@[simp] theorem complexFrequencyIntegrand_zero_frequency (h : ℝ) :
    complexFrequencyIntegrand 0 h = 0 := by simp [complexFrequencyIntegrand]

theorem integrable_complexFrequencyIntegrand (τ : ℝ) :
    Integrable (complexFrequencyIntegrand τ) volume := by
  change Integrable (fun h => complexFrequencyIntegrand τ h) volume
  simp_rw [complexFrequencyIntegrand_eq]
  exact (integrable_frequencyIntegrand τ).ofReal.add
    ((integrable_sineIntegrand τ).ofReal.mul_const Complex.I)

/-- Complex and real integrals agree on measurable symmetric sets, before normalization. -/
theorem integral_complexFrequencyIntegrand_of_symmetric (τ : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hsneg : ∀ h : ℝ, -h ∈ s ↔ h ∈ s) :
    (∫ h in s, complexFrequencyIntegrand τ h) = (∫ h in s, frequencyIntegrand τ h : ℝ) := by
  simp_rw [complexFrequencyIntegrand_eq]
  have hr : Integrable (fun h => (frequencyIntegrand τ h : ℂ)) (volume.restrict s) :=
    (integrable_frequencyIntegrand τ).ofReal.integrableOn
  have hi : Integrable (fun h => (sineIntegrand τ h : ℂ)) (volume.restrict s) :=
    (integrable_sineIntegrand τ).ofReal.integrableOn
  rw [integral_add hr (hi.mul_const Complex.I),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_sineIntegrand_of_symmetric τ hs hsneg]
  simp

/-- The complex multiplier with the exact Fourier phase `exp (-2 * π * I * τ * h)`. -/
theorem kappa_mul_integral_complexFrequencyIntegrand (τ : ℝ) :
    (kappa : ℂ) * (∫ h : ℝ, complexFrequencyIntegrand τ h) =
      ((|τ| ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  have h := integral_complexFrequencyIntegrand_of_symmetric τ MeasurableSet.univ (by simp)
  simp only [setIntegral_univ] at h
  rw [h, ← Complex.ofReal_mul, kappa_mul_integral_frequencyIntegrand]

end ParabolicRectifiability.FractionalKernel
