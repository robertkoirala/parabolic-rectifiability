import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Foundations.Proofs.HighPass.Marginal

/-! # The difference term of the split, quantitatively

Proof of `fhpbc_b1_differenceBracket`, as `fhpbc_b1_differenceBracket_proof`, in implication
form over `FhpbcOneDimUnweightedStatement` (the first argument). The split is at the spatial
base point `0`; no mean-zero hypothesis is needed.

For parabolic Lipschitz `G` (constant `L`), compact `A ⊆ {‖u‖ ≤ R}` and a Schwartz test `θ`
vanishing at every `(u,t)` with `u ∉ A`, write `K = testKernel θ` and `f_u(s) = θ(u,s)`.

1. **Pointwise.** `|G(u,t) - G(0,t)| ≤ L dist((u,t),(0,t)) = L ‖u‖ ≤ L R` on `A` (same time,
   `dist_point`); off `A` the kernel vanishes, since the slice `f_u` vanishes identically.
2. **Tonelli.** `‖∫ ·‖ₑ ≤ ∫⁻ ‖·‖ₑ`, then swap `(t,u)` (joint measurability of `K` from
   `stronglyMeasurable_testKernel`).
3. **Fibres.** `K(u,t) = D f_u (t)` (unfold, `timeShift_toLp`), `f_u ∈ C¹` with
   `f_u' = ∂_t θ(u,·)`, and the unweighted estimate gives `∫⁻ ‖K(u,·)‖ₑ ≤ C_U ∫⁻ (‖θ(u,·)‖ₑ + ‖∂_t θ(u,·)‖ₑ)`.
4. **Weight.** `1 ≤ 1 + |t|` and the coordinate form of `N(θ)` (`fhpbb1m_weightedTestNorm_eq`)
   give the bound `L R C_U N(θ)`.
5. **Measurability.** `G` is continuous, so the integrand is jointly measurable in `(t,u)` and
   `StronglyMeasurable.integral_prod_right'` applies.

The fibre calculus (`fhpbb1m_*`) comes from the proof of `FhpbcMarginalStatement` and is
imported, not re-proved.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

section Helpers

variable {m : ℕ}

/-! ## Fibres of the test kernel -/

/-- On each time fibre the test kernel is the one-dimensional operator of the slice:
`testKernel θ (u,t) = D f_u (t)` with `f_u(s) = θ(u,s)`. -/
theorem fhpbb1d_testKernel_eq (θ : 𝓢(FourierSpace m, ℂ)) (u : Spatial m) (t : ℝ) :
    testKernel θ (WithLp.toLp 2 (u, t)) =
      fhpbc_halfDeriv1D (fun s : ℝ => θ (WithLp.toLp 2 (u, s))) t := by
  rw [testKernel, fhpbc_halfDeriv1D]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun h => fhpab4_integrand_eq θ u t h)

/-- Off the spatial support the test kernel vanishes. -/
theorem fhpbb1d_testKernel_eq_zero {θ : 𝓢(FourierSpace m, ℂ)} {A : Set (Spatial m)}
    (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) {u : Spatial m} (hu : u ∉ A) (t : ℝ) :
    testKernel θ (WithLp.toLp 2 (u, t)) = 0 := by
  rw [testKernel, integral_congr_ae (Eventually.of_forall fun h =>
    fhpbb1m_integrand_eq_zero hθ hu t h), integral_zero, mul_zero]

/-- The derivative of a slice is the time derivative of the test. -/
theorem fhpbb1d_deriv_slice (θ : 𝓢(FourierSpace m, ℂ)) (u : Spatial m) :
    deriv (fun s : ℝ => θ (WithLp.toLp 2 (u, s))) =
      fun s => fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m) :=
  funext fun s => (fhpbb1m_hasDerivAt_slice θ u s).deriv

/-- Every slice of a Schwartz test is `C¹`. -/
theorem fhpbb1d_contDiff_slice (θ : 𝓢(FourierSpace m, ℂ)) (u : Spatial m) :
    ContDiff ℝ 1 (fun s : ℝ => θ (WithLp.toLp 2 (u, s))) := by
  refine contDiff_one_iff_deriv.2
    ⟨fun s => (fhpbb1m_hasDerivAt_slice θ u s).differentiableAt, ?_⟩
  rw [fhpbb1d_deriv_slice]
  exact (fhpbb1m_continuous_dt θ).comp (fhpbb1m_continuous_line u)

/-- **Fibre estimate from the unweighted estimate.** For every spatial point `u`,
`∫⁻ ‖K(u,t)‖ₑ dt ≤ C_U ∫⁻ w(u,t) dt`, with `w` the integrand of `N(θ)`. -/
theorem fhpbb1d_fibre_le {CU : ℝ}
    (hU : ∀ f : ℝ → ℂ, ContDiff ℝ 1 f →
      ∫⁻ t, ‖fhpbc_halfDeriv1D f t‖ₑ ≤ ENNReal.ofReal CU * ∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ))
    (θ : 𝓢(FourierSpace m, ℂ)) (u : Spatial m) :
    ∫⁻ t : ℝ, ‖testKernel θ (WithLp.toLp 2 (u, t))‖ₑ ≤
      ENNReal.ofReal CU * ∫⁻ t : ℝ, fhpbb1m_weight θ (WithLp.toLp 2 (u, t)) := by
  simp_rw [fhpbb1d_testKernel_eq θ u]
  refine (hU _ (fhpbb1d_contDiff_slice θ u)).trans ?_
  rw [fhpbb1d_deriv_slice]
  refine mul_le_mul_right (lintegral_mono fun t => ?_) _
  unfold fhpbb1m_weight
  exact le_mul_of_one_le_left'
    (ENNReal.one_le_ofReal.2 (le_add_of_nonneg_right (abs_nonneg _)))

/-! ## The Lipschitz factor -/

/-- A parabolic Lipschitz function is continuous in ordinary coordinates. -/
theorem fhpbb1d_continuous {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) : Continuous G := by
  have h : G = (G ∘ (fourierToParabolic m).symm) ∘ fourierToParabolic m := by
    funext x
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  rw [h]
  exact hL.continuous.comp (fourierToParabolic m).continuous

/-- Same time: `|G(u,t) - G(0,t)| ≤ L ‖u‖` (`dist_point`). -/
theorem fhpbb1d_norm_sub_le {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) (u : Spatial m) (t : ℝ) :
    ‖((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ))‖ ≤ L * ‖u‖ := by
  have h := hL.dist_le_mul (point u t) (point 0 t)
  simp only [dist_point, sub_zero, sub_self, abs_zero, Real.sqrt_zero,
    max_eq_left (norm_nonneg u)] at h
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Real.dist_eq]
  exact h

/-- The pointwise bound of the integrand: `‖(G(u,t) - G(0,t)) K(u,t)‖ₑ ≤ L R ‖K(u,t)‖ₑ`
(on `A` by the Lipschitz bound, off `A` since `K` vanishes). -/
theorem fhpbb1d_enorm_integrand_le {G : FourierSpace m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm)) {θ : 𝓢(FourierSpace m, ℂ)}
    {A : Set (Spatial m)} (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) {R : ℝ}
    (hR : ∀ u ∈ A, ‖u‖ ≤ R) (u : Spatial m) (t : ℝ) :
    ‖((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
        testKernel θ (WithLp.toLp 2 (u, t))‖ₑ ≤
      ENNReal.ofReal (L * R) * ‖testKernel θ (WithLp.toLp 2 (u, t))‖ₑ := by
  by_cases hu : u ∈ A
  · rw [enorm_mul]
    refine mul_le_mul_left ?_ _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((fhpbb1d_norm_sub_le hL u t).trans
      (mul_le_mul_of_nonneg_left (hR u hu) L.coe_nonneg))
  · rw [fhpbb1d_testKernel_eq_zero hθ hu, mul_zero, enorm_zero, mul_zero]

/-! ## Measurability -/

theorem fhpbb1d_measurable_swap :
    Measurable fun p : ℝ × Spatial m => (WithLp.toLp 2 (p.2, p.1) : FourierSpace m) :=
  (fourierCoordinatesMeasurableEquiv m).symm.measurable.comp
    (measurable_snd.prodMk measurable_fst)

theorem fhpbb1d_measurable_kernel (θ : 𝓢(FourierSpace m, ℂ)) :
    Measurable fun p : ℝ × Spatial m => ‖testKernel θ (WithLp.toLp 2 (p.2, p.1))‖ₑ :=
  (stronglyMeasurable_testKernel θ).measurable.enorm.comp fhpbb1d_measurable_swap

theorem fhpbb1d_measurable_weight (θ : 𝓢(FourierSpace m, ℂ)) :
    Measurable fun p : Spatial m × ℝ => fhpbb1m_weight θ (WithLp.toLp 2 (p.1, p.2)) :=
  (fhpbb1m_measurable_weight θ).comp (fourierCoordinatesMeasurableEquiv m).symm.measurable

/-- The difference bracket `t ↦ ∫ (G(u,t) - G(0,t)) K(u,t) du` is strongly measurable. -/
theorem fhpbb1d_stronglyMeasurable {G : FourierSpace m → ℝ} (hG : Continuous G)
    (θ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable (fun t : ℝ => ∫ u : Spatial m,
      ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
        testKernel θ (WithLp.toLp 2 (u, t))) := by
  have hGm : Measurable fun x : FourierSpace m => (G x : ℂ) :=
    (Complex.continuous_ofReal.comp hG).measurable
  have h0 : Measurable fun p : ℝ × Spatial m =>
      (WithLp.toLp 2 ((0 : Spatial m), p.1) : FourierSpace m) :=
    (fourierCoordinatesMeasurableEquiv m).symm.measurable.comp
      (measurable_const.prodMk measurable_fst)
  have hf : Measurable fun p : ℝ × Spatial m =>
      ((G (WithLp.toLp 2 (p.2, p.1)) : ℂ) - (G (WithLp.toLp 2 (0, p.1)) : ℂ)) *
        testKernel θ (WithLp.toLp 2 (p.2, p.1)) :=
    ((hGm.comp fhpbb1d_measurable_swap).sub (hGm.comp h0)).mul
      ((stronglyMeasurable_testKernel θ).measurable.comp fhpbb1d_measurable_swap)
  exact hf.stronglyMeasurable.integral_prod_right'

/-! ## The quantitative bound -/

/-- **The estimate.** `∫⁻ ‖∫ (G(u,t) - G(0,t)) K(u,t) du‖ₑ dt ≤ L R C_U N(θ)`. -/
theorem fhpbb1d_lintegral_le {CU : ℝ}
    (hU : ∀ f : ℝ → ℂ, ContDiff ℝ 1 f →
      ∫⁻ t, ‖fhpbc_halfDeriv1D f t‖ₑ ≤ ENNReal.ofReal CU * ∫⁻ t, (‖f t‖ₑ + ‖deriv f t‖ₑ))
    {G : FourierSpace m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L (G ∘ (fourierToParabolic m).symm))
    {A : Set (Spatial m)} {R : ℝ} (hR : ∀ u ∈ A, ‖u‖ ≤ R) (hR0 : 0 ≤ R)
    {θ : 𝓢(FourierSpace m, ℂ)} (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) :
    ∫⁻ t : ℝ, ‖∫ u : Spatial m,
        ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
          testKernel θ (WithLp.toLp 2 (u, t))‖ₑ ≤
      ENNReal.ofReal (L * R * CU) * fhp_weightedTestNorm (⇑θ) := by
  calc ∫⁻ t : ℝ, ‖∫ u : Spatial m,
        ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
          testKernel θ (WithLp.toLp 2 (u, t))‖ₑ
      ≤ ∫⁻ t : ℝ, ∫⁻ u : Spatial m,
          ENNReal.ofReal (L * R) * ‖testKernel θ (WithLp.toLp 2 (u, t))‖ₑ :=
        lintegral_mono fun t => (enorm_integral_le_lintegral_enorm _).trans
          (lintegral_mono fun u => fhpbb1d_enorm_integrand_le hL hθ hR u t)
    _ = ∫⁻ u : Spatial m, ∫⁻ t : ℝ,
          ENNReal.ofReal (L * R) * ‖testKernel θ (WithLp.toLp 2 (u, t))‖ₑ :=
        lintegral_lintegral_swap
          ((measurable_const.mul (fhpbb1d_measurable_kernel θ)).aemeasurable)
    _ = ENNReal.ofReal (L * R) *
          ∫⁻ u : Spatial m, ∫⁻ t : ℝ, ‖testKernel θ (WithLp.toLp 2 (u, t))‖ₑ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (L * R) * ∫⁻ u : Spatial m,
          ENNReal.ofReal CU * ∫⁻ t : ℝ, fhpbb1m_weight θ (WithLp.toLp 2 (u, t)) :=
        mul_le_mul_right (lintegral_mono fun u => fhpbb1d_fibre_le hU θ u) _
    _ = ENNReal.ofReal (L * R) * (ENNReal.ofReal CU *
          ∫⁻ u : Spatial m, ∫⁻ t : ℝ, fhpbb1m_weight θ (WithLp.toLp 2 (u, t))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (L * R) * (ENNReal.ofReal CU *
          ∫⁻ t : ℝ, ∫⁻ u : Spatial m, fhpbb1m_weight θ (WithLp.toLp 2 (u, t))) := by
        congr 2
        exact lintegral_lintegral_swap (fhpbb1d_measurable_weight θ).aemeasurable
    _ = ENNReal.ofReal (L * R * CU) * fhp_weightedTestNorm (⇑θ) := by
        rw [fhpbb1m_weightedTestNorm_eq, ENNReal.ofReal_mul (mul_nonneg L.coe_nonneg hR0),
          mul_assoc]

end Helpers

/-! ## The statement -/

/-- **The difference term** (`fhpbc_b1_differenceBracket`), in implication form over
`FhpbcOneDimUnweightedStatement`: for parabolic Lipschitz `G` and compact `A` there
is `C ≥ 0` (namely `C = L R C_U` with `A ⊆ {‖u‖ ≤ R}`) such that for every Schwartz test `θ`
supported spatially in `A`, the difference bracket `t ↦ ∫ (G(u,t) - G(0,t)) K(u,t) du` is a.e.
strongly measurable and `∫⁻ ‖·‖ₑ ≤ C N(θ)`. No mean-zero condition. -/
theorem fhpbc_b1_differenceBracket_proof : FhpbcOneDimUnweightedStatement →
    ∀ (m : ℕ) (G : FourierSpace m → ℝ),
      (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
      ∀ A : Set (Spatial m), IsCompact A → ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ : 𝓢(FourierSpace m, ℂ), fhp_IsSpatiallySupportedIn (⇑θ) A →
          AEStronglyMeasurable (fun t : ℝ => ∫ u : Spatial m,
            ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
              testKernel θ (WithLp.toLp 2 (u, t))) ∧
          ∫⁻ t : ℝ, ‖∫ u : Spatial m,
              ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
                testKernel θ (WithLp.toLp 2 (u, t))‖ₑ ≤
            ENNReal.ofReal C * fhp_weightedTestNorm (⇑θ) := by
  rintro ⟨CU, hCU, hU⟩ m G ⟨L, hL⟩ A hA
  obtain ⟨R₀, hR₀⟩ := hA.isBounded.exists_norm_le
  have hR : ∀ u ∈ A, ‖u‖ ≤ max R₀ 0 := fun u hu => (hR₀ u hu).trans (le_max_left _ _)
  have hR0 : 0 ≤ max R₀ 0 := le_max_right _ _
  refine ⟨L * max R₀ 0 * CU, mul_nonneg (mul_nonneg L.coe_nonneg hR0) hCU, fun θ hθ => ?_⟩
  exact ⟨(fhpbb1d_stronglyMeasurable (fhpbb1d_continuous hL) θ).aestronglyMeasurable,
    fhpbb1d_lintegral_le hU hL hR hR0 hθ⟩

end ParabolicRectifiability.Foundations
