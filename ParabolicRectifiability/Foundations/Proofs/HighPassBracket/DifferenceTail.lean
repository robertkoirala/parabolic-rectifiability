import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel
import ParabolicRectifiability.Foundations.HalfTimeDerivative

/-! # The difference term has an `|t|^{-3/2}` tail

Proof of `fhpa_integrable_differenceBracket`, as `fhpa_integrable_differenceBracket_proof`.
No mean-zero condition is used.

Route. Write `A` for the compact spatial projection
`spatialTestSupport` of the test's support and `ρ > 0` for a norm bound on `A`.

1. Same-time Lipschitz bound `|G(u,t) - G(0,t)| ≤ L ‖u‖` (`dist_point`).
2. Pointwise on `ℝ^m × ℝ`, the **difference** integrand
   `F(u,t) = [G(u,t) - G(0,t)] K(u,t)` satisfies
   `‖F(u,t)‖ ≤ 1_A(u) · (L ρ C) · temporalWeight (2S) t`, where `C` is the kernel majorant
   constant of `exists_temporal_majorant` (from `norm_testKernel_le` and
   `norm_testKernel_temporal_tail`). Off `A` the kernel vanishes
   (`testKernel_eq_zero_of_notMem_spatialTestSupport`), so the indicator is genuine.
3. The majorant is integrable on the product (`Integrable.mul_prod`, `integrable_temporalWeight`),
   so `F` is absolutely integrable on `ℝ^m × ℝ`; the factor `vol(A)` appears only through the
   spatial integral of the indicator. Integrating space first (`Integrable.integral_prod_right`)
   gives integrability of `t ↦ ∫ F(u,t) du`; measurability is part of this parameter integration.

This is absolute integrability of the difference integrand only; no Fubini statement about the
original product `G · K` is made or used. Spatial rank `m = 0` is included (nothing special is
needed: the bound holds uniformly).
-/

noncomputable section

open MeasureTheory Filter
open scoped NNReal ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Same-time Lipschitz bound for a parabolic Lipschitz function in Fourier coordinates. -/
theorem fhpab3_abs_sub_le {m : ℕ} (G : FourierSpace m → ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (u : Spatial m) (t : ℝ) :
    |G (WithLp.toLp 2 (u, t)) - G (WithLp.toLp 2 (0, t))| ≤ L * ‖u‖ := by
  have h := hL.dist_le_mul (point u t) (point 0 t)
  have e1 : (G ∘ (fourierToParabolic m).symm) (point u t) = G (WithLp.toLp 2 (u, t)) := rfl
  have e2 : (G ∘ (fourierToParabolic m).symm) (point 0 t) = G (WithLp.toLp 2 (0, t)) := rfl
  rw [e1, e2, Real.dist_eq, dist_point, sub_zero, sub_self, abs_zero, Real.sqrt_zero,
    max_eq_left (norm_nonneg _)] at h
  exact h

/-- A parabolic Lipschitz function is continuous in Fourier coordinates. -/
theorem fhpab3_continuous {m : ℕ} (G : FourierSpace m → ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) : Continuous G := by
  have h := hL.continuous.comp (fourierToParabolic m).continuous
  convert h using 1
  funext x
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply]

/-- **The difference term has an `|t|^{-3/2}` tail.** The difference bracket `t ↦ ∫ [G(u,t) - G(0,t)] K(u,t) du` is
integrable on `ℝ`, for every parabolic Lipschitz `G` and every real compact smooth test `φ`. -/
theorem fhpa_integrable_differenceBracket_proof {m : ℕ} (G : FourierSpace m → ℝ)
    (hG : ∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm))
    (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun t : ℝ => ∫ u : Spatial m,
      ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
        testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))) := by
  obtain ⟨L, hL⟩ := hG
  set ψ := realCompactTest φ hφ hc with hψ
  have hψc : HasCompactSupport ψ := by
    change IsCompact (tsupport ψ)
    rw [hψ, tsupport_realCompactTest]
    exact hc
  obtain ⟨S, hS, hs⟩ := exists_time_support_bound ψ hψc
  obtain ⟨C, hC, hb⟩ := exists_temporal_majorant ψ hS hs
  have hA := isCompact_spatialTestSupport ψ hψc
  obtain ⟨ρ, hρ0, hρ⟩ := hA.isBounded.exists_pos_norm_le
  have hGc := fhpab3_continuous G hL
  -- the difference integrand on ordinary coordinates `ℝ^m × ℝ`
  let f : Spatial m × ℝ → ℂ := fun p =>
    ((G (WithLp.toLp 2 p) : ℂ) - (G (WithLp.toLp 2 ((0 : Spatial m), p.2)) : ℂ)) *
      testKernel ψ (WithLp.toLp 2 p)
  -- the integrable majorant `1_A(u) · (L ρ C) · temporalWeight (2S) t`
  have hi : Integrable ((spatialTestSupport ψ).indicator
      (fun _ : Spatial m => (L : ℝ) * ρ * C)) volume :=
    (integrableOn_const hA.measure_ne_top).integrable_indicator hA.measurableSet
  have hmaj : Integrable (fun p : Spatial m × ℝ =>
      (spatialTestSupport ψ).indicator (fun _ : Spatial m => (L : ℝ) * ρ * C) p.1 *
        temporalWeight (2 * S) p.2)
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) :=
    hi.mul_prod (integrable_temporalWeight (by positivity : 0 < 2 * S))
  have hbound : ∀ p : Spatial m × ℝ, ‖f p‖ ≤
      (spatialTestSupport ψ).indicator (fun _ : Spatial m => (L : ℝ) * ρ * C) p.1 *
        temporalWeight (2 * S) p.2 := by
    rintro ⟨u, t⟩
    by_cases hu : u ∈ spatialTestSupport ψ
    · rw [Set.indicator_of_mem hu]
      have h1 : ‖((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 ((0 : Spatial m), t)) : ℂ))‖
          ≤ L * ρ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact (fhpab3_abs_sub_le G hL u t).trans
          (mul_le_mul_of_nonneg_left (hρ u hu) L.coe_nonneg)
      have hw := temporalWeight_nonneg (2 * S) t
      calc ‖f (u, t)‖ = ‖((G (WithLp.toLp 2 (u, t)) : ℂ) -
              (G (WithLp.toLp 2 ((0 : Spatial m), t)) : ℂ))‖ *
            ‖testKernel ψ (WithLp.toLp 2 (u, t))‖ := norm_mul _ _
        _ ≤ (L * ρ) * (C * temporalWeight (2 * S) t) :=
          mul_le_mul h1 (hb u t) (norm_nonneg _) (by positivity)
        _ = L * ρ * C * temporalWeight (2 * S) t := by ring
    · rw [Set.indicator_of_notMem hu, zero_mul]
      have hK : testKernel ψ (WithLp.toLp 2 (u, t)) = 0 :=
        testKernel_eq_zero_of_notMem_spatialTestSupport ψ hu t
      change ‖((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 ((0 : Spatial m), t)) : ℂ)) *
        testKernel ψ (WithLp.toLp 2 (u, t))‖ ≤ 0
      rw [hK, mul_zero, norm_zero]
  have hmeas : AEStronglyMeasurable f
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
    have hG1 : Continuous fun p : Spatial m × ℝ => G (WithLp.toLp 2 p) :=
      hGc.comp (fourierCoordinatesHomeomorph m).symm.continuous
    have hG2 : Continuous fun p : Spatial m × ℝ => G (WithLp.toLp 2 ((0 : Spatial m), p.2)) :=
      hG1.comp (continuous_const.prodMk continuous_snd)
    have hK : AEStronglyMeasurable (fun p : Spatial m × ℝ => testKernel ψ (WithLp.toLp 2 p))
        ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) :=
      ((stronglyMeasurable_testKernel ψ).comp_measurable
        (fourierCoordinatesMeasurableEquiv m).symm.measurable).aestronglyMeasurable
    exact (((Complex.continuous_ofReal.comp hG1).sub
      (Complex.continuous_ofReal.comp hG2)).aestronglyMeasurable).mul hK
  have hf : Integrable f ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) :=
    hmaj.mono' hmeas (Eventually.of_forall hbound)
  exact hf.integral_prod_right

end ParabolicRectifiability.Foundations
