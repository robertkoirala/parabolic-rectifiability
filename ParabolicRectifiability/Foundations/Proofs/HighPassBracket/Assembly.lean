import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.Lemmas
import ParabolicRectifiability.Foundations.Statements.HighPassBracket

/-! # Integrability of the spatial bracket: assembly

`fhpa_halfTimeBracketIntegrable` proves `HalfTimeBracketIntegrableStatement` from
`fhpa_ae_fibre_halfTimeDeriv`, `fhpa_integrable_mul_testKernel`,
`fhpa_integrable_differenceBracket`, `fhpa_spatialIntegral_testKernel_decay` and
`fhpa_integrable_sqrtGrowth_mul_decay`.

Structure: the a.e. fibre transfer replaces the `L²` derivative by the pointwise test kernel
for a.e. time; spatial integrability gives the a.e. integrand clause and the split with
`u₀ = 0`; the difference term has an `|t|^{-3/2}` tail; the mean term has an `|t|^{-5/2}` tail
against the growth `|G(0,t)| ≤ |G(0,0)| + L √|t|` (proved here from the Lipschitz bound).
-/

noncomputable section

open MeasureTheory
open scoped NNReal ContDiff

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Growth of the time section through the spatial origin:
`|G(0,t)| ≤ |G(0,0)| + L √|t|`. -/
theorem fhpa_abs_le_of_lipschitz {m : ℕ} (G : FourierSpace m → ℝ) (L : ℝ≥0)
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (t : ℝ) :
    |G (WithLp.toLp 2 (0, t))| ≤ |G (WithLp.toLp 2 (0, 0))| + L * Real.sqrt |t| := by
  have h := hL.dist_le_mul (point (0 : Spatial m) t) (point 0 0)
  rw [dist_point, sub_zero, norm_zero, sub_zero,
    max_eq_right (Real.sqrt_nonneg _), Real.dist_eq] at h
  have h' : |G (WithLp.toLp 2 (0, t)) - G (WithLp.toLp 2 (0, 0))| ≤ L * Real.sqrt |t| := h
  have := abs_sub_abs_le_abs_sub (G (WithLp.toLp 2 (0, t))) (G (WithLp.toLp 2 (0, 0)))
  linarith

/-- **The spatial bracket of a parabolic Lipschitz function is in `L¹(dt)`**: exactly
`HalfTimeBracketIntegrableStatement`. -/
theorem fhpa_halfTimeBracketIntegrable : HalfTimeBracketIntegrableStatement := by
  intro m G hG φ hφ hc h0
  obtain ⟨L, hL⟩ := hG
  have hsec : ∀ t : ℝ, Continuous fun u : Spatial m => (G (WithLp.toLp 2 (u, t)) : ℂ) :=
    fun t => Complex.continuous_ofReal.comp (hL.continuous.comp
      (continuous_id.prodMk continuous_const : Continuous fun u : Spatial m => point u t))
  have hzero : Continuous fun t : ℝ => G (WithLp.toLp 2 (0, t)) :=
    hL.continuous.comp (continuous_const.prodMk Metric.Snowflaking.continuous_toSnowflaking :
      Continuous fun t : ℝ => point (0 : Spatial m) t)
  have hK : ∀ t : ℝ, Integrable fun u : Spatial m =>
      (G (WithLp.toLp 2 (u, t)) : ℂ) * testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t)) :=
    fun t => fhpa_integrable_mul_testKernel φ hφ hc _ (hsec t) t
  have hae : ∀ᵐ t : ℝ, halfTimeSpatialIntegrand G (realCompactTest φ hφ hc) t =ᵐ[volume]
      fun u => (G (WithLp.toLp 2 (u, t)) : ℂ) *
        testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t)) := by
    filter_upwards [fhpa_ae_fibre_halfTimeDeriv (realCompactTest φ hφ hc)] with t ht
    filter_upwards [ht] with u hu
    exact congrArg (fun z => (G (WithLp.toLp 2 (u, t)) : ℂ) * z) hu
  refine ⟨hae.mono fun t ht => (hK t).congr ht.symm, ?_⟩
  have hbr : halfTimeSpatialBracket G (realCompactTest φ hφ hc) =ᵐ[volume] fun t =>
      ∫ u : Spatial m, (G (WithLp.toLp 2 (u, t)) : ℂ) *
        testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t)) :=
    hae.mono fun t ht => integral_congr_ae ht
  refine Integrable.congr ?_ hbr.symm
  have hsplit : (fun t : ℝ => ∫ u : Spatial m, (G (WithLp.toLp 2 (u, t)) : ℂ) *
      testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))) =
      fun t : ℝ => (∫ u : Spatial m,
          ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
            testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))) +
        (G (WithLp.toLp 2 (0, t)) : ℂ) *
          ∫ u : Spatial m, testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t)) := by
    funext t
    have h1 : Integrable fun u : Spatial m =>
        ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
          testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t)) :=
      fhpa_integrable_mul_testKernel φ hφ hc
        (fun u => (G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ))
        ((hsec t).sub continuous_const) t
    have h2 : Integrable fun u : Spatial m =>
        (G (WithLp.toLp 2 (0, t)) : ℂ) *
          testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t)) :=
      fhpa_integrable_mul_testKernel φ hφ hc (fun _ => (G (WithLp.toLp 2 (0, t)) : ℂ))
        continuous_const t
    rw [← integral_const_mul, ← integral_add h1 h2]
    congr 1
    funext u
    ring
  rw [hsplit]
  refine (fhpa_integrable_differenceBracket G ⟨L, hL⟩ φ hφ hc).add ?_
  obtain ⟨hmeas, C, S, hS, hbound, htail⟩ := fhpa_spatialIntegral_testKernel_decay φ hφ hc h0
  exact fhpa_integrable_sqrtGrowth_mul_decay _ hzero |G (WithLp.toLp 2 (0, 0))| L
    (fhpa_abs_le_of_lipschitz G L hL) _ hmeas C S hS hbound htail

end ParabolicRectifiability.Foundations
