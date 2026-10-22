import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements

/-! # The mean term of the split

Proof of `fhpbc_b1_meanBracket`, in implication form over `FhpbcOneDimWeightedStatement` and
`FhpbcMarginalStatement`.

Route: by `FhpbcMarginalStatement`, `∫ testKernel θ (u,t) du = D F(t)` for every `t`, where `F` is
the spatial marginal of `θ` (`C¹`, integrable, `∫ F = ∫ θ = 0`,
`∫⁻ (1 + |s|) (‖F‖ₑ + ‖F'‖ₑ) ≤ N(θ)`). The parabolic Lipschitz bound at the spatial base point
gives `|G(0,t)| ≤ |G(0,0)| + L √|t| ≤ M (1 + √|t|)` with `M = max(|G(0,0)|, L)`. `FhpbcOneDimWeightedStatement` then gives
`∫⁻ ‖G(0,t) D F(t)‖ₑ ≤ M C_W N(θ)`. Measurability: `t ↦ G(0,t)` is continuous and the kernel
marginal is strongly measurable (`StronglyMeasurable.integral_prod_right'`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- Growth of a parabolic Lipschitz function along the time axis at the spatial origin:
`|G(0,t)| ≤ max(|G(0,0)|, L) (1 + √|t|)`. -/
theorem fhpbb1e_norm_G_le {m : ℕ} {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (t : ℝ) :
    ‖(G (WithLp.toLp 2 ((0 : Spatial m), t)) : ℂ)‖ ≤
      max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) * (1 + Real.sqrt |t|) := by
  have hd := hL.dist_le_mul (point (0 : Spatial m) t) (point 0 0)
  have h1 : (G ∘ (fourierToParabolic m).symm) (point (0 : Spatial m) t) =
      G (WithLp.toLp 2 ((0 : Spatial m), t)) := rfl
  have h0 : (G ∘ (fourierToParabolic m).symm) (point (0 : Spatial m) 0) =
      G (WithLp.toLp 2 ((0 : Spatial m), 0)) := rfl
  have hs : 0 ≤ Real.sqrt |t| := Real.sqrt_nonneg _
  rw [h1, h0, dist_point, sub_self, norm_zero, sub_zero, max_eq_right hs, Real.dist_eq] at hd
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hab := abs_sub_abs_le_abs_sub (G (WithLp.toLp 2 ((0 : Spatial m), t)))
    (G (WithLp.toLp 2 ((0 : Spatial m), 0)))
  have hb : |G (WithLp.toLp 2 ((0 : Spatial m), 0))| ≤
      max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) := le_max_left _ _
  have hLm : (L : ℝ) ≤ max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) := le_max_right _ _
  have hLs := mul_le_mul_of_nonneg_right hLm hs
  calc |G (WithLp.toLp 2 ((0 : Spatial m), t))|
      ≤ |G (WithLp.toLp 2 ((0 : Spatial m), 0))| + (L : ℝ) * Real.sqrt |t| := by linarith
    _ ≤ max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) +
          max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) * Real.sqrt |t| :=
        add_le_add hb hLs
    _ = max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) * (1 + Real.sqrt |t|) := by ring

/-- The spatial marginal of the test kernel is strongly measurable in time. -/
theorem fhpbb1e_stronglyMeasurable_kernelMarginal {m : ℕ} (θ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable
      (fun t : ℝ => ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t))) := by
  have hc : Continuous (fun p : ℝ × Spatial m => (WithLp.toLp 2 (p.2, p.1) : FourierSpace m)) :=
    (WithLp.prod_continuous_toLp 2 (Spatial m) ℝ).comp (continuous_snd.prodMk continuous_fst)
  exact ((stronglyMeasurable_testKernel θ).comp_measurable hc.measurable).integral_prod_right'

/-- **The mean term of the split** (`fhpbc_b1_meanBracket`, implication form over
`FhpbcOneDimWeightedStatement` and `FhpbcMarginalStatement`): the mean term `t ↦ G(0,t) ∫ testKernel θ (u,t) du` is a.e. strongly measurable and
`∫⁻ ‖·‖ₑ ≤ C N(θ)` with `C = max(|G(0,0)|, L) · C_W`. -/
theorem fhpbc_b1_meanBracket_proof : FhpbcOneDimWeightedStatement → FhpbcMarginalStatement →
    ∀ (m : ℕ) (G : FourierSpace m → ℝ),
      (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
      ∀ A : Set (Spatial m), IsCompact A → ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ : 𝓢(FourierSpace m, ℂ), fhp_IsSpatiallySupportedIn (⇑θ) A → ∫ x, θ x = 0 →
          AEStronglyMeasurable (fun t : ℝ => (G (WithLp.toLp 2 (0, t)) : ℂ) *
            ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t))) ∧
          ∫⁻ t : ℝ, ‖(G (WithLp.toLp 2 (0, t)) : ℂ) *
              ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t))‖ₑ ≤
            ENNReal.ofReal C * fhp_weightedTestNorm (⇑θ) := by
  rintro ⟨CW, hCW0, hW⟩ hMarg m G ⟨L, hL⟩ A hA
  have hM0 : 0 ≤ max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) * CW, mul_nonneg hM0 hCW0, ?_⟩
  intro θ hθA hθ0
  obtain ⟨hF1, hFint, hFmean, hFnorm, hFker⟩ := hMarg m A hA θ hθA
  have hGcont : Continuous G := by
    have hG : G = (G ∘ (fourierToParabolic m).symm) ∘ (fourierToParabolic m) := by
      funext x
      simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    rw [hG]
    exact hL.continuous.comp (fourierToParabolic m).continuous
  have hline : Continuous (fun t : ℝ => (WithLp.toLp 2 ((0 : Spatial m), t) : FourierSpace m)) :=
    (WithLp.prod_continuous_toLp 2 (Spatial m) ℝ).comp (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp (hGcont.comp hline)).aestronglyMeasurable.mul
      (fhpbb1e_stronglyMeasurable_kernelMarginal θ).aestronglyMeasurable
  · calc ∫⁻ t : ℝ, ‖(G (WithLp.toLp 2 (0, t)) : ℂ) *
            ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t))‖ₑ
        ≤ ∫⁻ t : ℝ, ENNReal.ofReal (max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ)) *
            (ENNReal.ofReal (1 + Real.sqrt |t|) *
              ‖fhpbc_halfDeriv1D
                (fun s : ℝ => ∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))) t‖ₑ) := by
          refine lintegral_mono fun t => ?_
          rw [enorm_mul, hFker t, ← mul_assoc, ← ENNReal.ofReal_mul hM0]
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (fhpbb1e_norm_G_le hL t)
      _ = ENNReal.ofReal (max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ)) *
            ∫⁻ t : ℝ, ENNReal.ofReal (1 + Real.sqrt |t|) *
              ‖fhpbc_halfDeriv1D
                (fun s : ℝ => ∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))) t‖ₑ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ)) *
            (ENNReal.ofReal CW *
              ∫⁻ s : ℝ, ENNReal.ofReal (1 + |s|) *
                (‖∫ u : Spatial m, θ (WithLp.toLp 2 (u, s))‖ₑ +
                  ‖deriv (fun s' : ℝ => ∫ u : Spatial m, θ (WithLp.toLp 2 (u, s'))) s‖ₑ)) := by
          gcongr
          exact hW _ hF1 hFint (hFmean.trans hθ0)
      _ ≤ ENNReal.ofReal (max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ)) *
            (ENNReal.ofReal CW * fhp_weightedTestNorm (⇑θ)) := by
          gcongr
      _ = ENNReal.ofReal (max |G (WithLp.toLp 2 ((0 : Spatial m), 0))| (L : ℝ) * CW) *
            fhp_weightedTestNorm (⇑θ) := by
          rw [ENNReal.ofReal_mul hM0, mul_assoc]

end ParabolicRectifiability.Foundations
