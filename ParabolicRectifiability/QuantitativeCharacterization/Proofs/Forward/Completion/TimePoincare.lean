import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion

/-! # First-order time Poincaré on an interval

Proof of `d1e_time_poincare_proof : d1e_TimePoincareStatement`.

For a `C¹` curve `g : ℝ → ℝ^d`, `a < b` and `s₀ ∈ [a, b]`:
`∫_{(a,b)} |g - g(s₀)|² ≤ (b - a)² ∫_{(a,b)} |g'|²` (lower Lebesgue integrals).

Route: `g s - g s₀ = ∫_{s₀}^{s} g'` (FTC, `intervalIntegral.integral_deriv_eq_sub`);
`|∫_{s₀}^{s} g'| ≤ ∫_{Ι s₀ s} |g'|`; scalar Cauchy–Schwarz (`ENNReal.lintegral_mul_le_Lp_mul_Lq`,
`p = q = 2`) gives `(∫_{Ι s₀ s} |g'|)² ≤ |Ι s₀ s| ∫_{Ι s₀ s} |g'|²
≤ (b - a) ∫_{(a,b]} |g'|²`; integrate over `(a, b)` (volume `b - a`). Only norms enter, so the
constant `1` does not depend on `d`.

Helpers carry the prefix `d1etimep_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Interval

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- Scalar Cauchy–Schwarz for lower Lebesgue integrals:
`(∫ f)² ≤ μ(univ) · ∫ f²`. -/
theorem d1etimep_sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ μ univ * ∫⁻ x, f x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := f) aemeasurable_const hf
  have h' : ∫⁻ x, f x ∂μ ≤ μ univ ^ (1 / 2 : ℝ) * (∫⁻ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa only [Pi.mul_apply, one_mul, ENNReal.one_rpow, one_pow, lintegral_one,
      ENNReal.rpow_two] using h
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  calc (∫⁻ x, f x ∂μ) ^ 2 = (∫⁻ x, f x ∂μ) ^ (2 : ℝ) := (ENNReal.rpow_two _).symm
    _ ≤ (μ univ ^ (1 / 2 : ℝ) * (∫⁻ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h' h2
    _ = μ univ * ∫⁻ x, f x ^ 2 ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h2, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- Pointwise time Poincaré: for `s₀, s ∈ [a, b]`,
`|g s - g s₀|² ≤ (b - a) ∫_{(a,b]} |g'|²`. -/
theorem d1etimep_pointwise {d : ℕ} {g : ℝ → Spatial d} {a b : ℝ} (hg : ContDiff ℝ 1 g)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Icc a b) (hs : s ∈ Icc a b) :
    ‖g s - g s₀‖ₑ ^ 2 ≤ ENNReal.ofReal (b - a) * ∫⁻ τ in Ioc a b, ‖deriv g τ‖ₑ ^ 2 := by
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hftc : ∫ τ in s₀..s, deriv g τ = g s - g s₀ :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff x) (hcont.intervalIntegrable _ _)
  have hsub : Ι s₀ s ⊆ Ioc a b := by
    intro x hx
    have hx' : min s₀ s < x ∧ x ≤ max s₀ s := hx
    exact ⟨lt_of_le_of_lt (le_min hs₀.1 hs.1) hx'.1, hx'.2.trans (max_le hs₀.2 hs.2)⟩
  have h1 : ‖g s - g s₀‖ₑ ≤ ∫⁻ τ in Ι s₀ s, ‖deriv g τ‖ₑ := by
    rw [← hftc]
    calc ‖∫ τ in s₀..s, deriv g τ‖ₑ = ‖∫ τ in Ι s₀ s, deriv g τ‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm,
            intervalIntegral.norm_integral_eq_norm_integral_uIoc]
      _ ≤ ∫⁻ τ in Ι s₀ s, ‖deriv g τ‖ₑ := enorm_integral_le_lintegral_enorm _
  have h2 := d1etimep_sq_lintegral_le (volume.restrict (Ι s₀ s))
    (f := fun τ => ‖deriv g τ‖ₑ) hcont.measurable.enorm.aemeasurable
  rw [Measure.restrict_apply_univ] at h2
  calc ‖g s - g s₀‖ₑ ^ 2 ≤ (∫⁻ τ in Ι s₀ s, ‖deriv g τ‖ₑ) ^ 2 := by gcongr
    _ ≤ volume (Ι s₀ s) * ∫⁻ τ in Ι s₀ s, ‖deriv g τ‖ₑ ^ 2 := h2
    _ ≤ ENNReal.ofReal (b - a) * ∫⁻ τ in Ioc a b, ‖deriv g τ‖ₑ ^ 2 := by
        refine mul_le_mul' ?_ (lintegral_mono_set hsub)
        calc volume (Ι s₀ s) ≤ volume (Ioc a b) := measure_mono hsub
          _ = ENNReal.ofReal (b - a) := Real.volume_Ioc

/-- **First-order time Poincaré on an interval**: the type
`d1e_TimePoincareStatement`. -/
theorem d1e_time_poincare_proof : d1e_TimePoincareStatement := by
  intro d g a b hab hg s₀ hs₀
  have hE : ∫⁻ s in Ioo a b, ‖deriv g s‖ₑ ^ 2 = ∫⁻ τ in Ioc a b, ‖deriv g τ‖ₑ ^ 2 :=
    setLIntegral_congr Ioo_ae_eq_Ioc
  rw [hE]
  calc ∫⁻ s in Ioo a b, ‖g s - g s₀‖ₑ ^ 2
      ≤ ∫⁻ _ in Ioo a b,
          ENNReal.ofReal (b - a) * ∫⁻ τ in Ioc a b, ‖deriv g τ‖ₑ ^ 2 :=
        setLIntegral_mono measurable_const
          (fun s hs => d1etimep_pointwise hg hs₀ (Ioo_subset_Icc_self hs))
    _ = ENNReal.ofReal (b - a) * (∫⁻ τ in Ioc a b, ‖deriv g τ‖ₑ ^ 2) *
          ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Ioo]
    _ = ENNReal.ofReal ((b - a) ^ 2) * ∫⁻ τ in Ioc a b, ‖deriv g τ‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (sub_nonneg.2 hab.le)]
        ring

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
