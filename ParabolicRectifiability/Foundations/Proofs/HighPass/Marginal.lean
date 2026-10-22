import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.MarginalDecay

/-! # The spatial marginal of a spatially compact Schwartz test

Proof of `fhpbc_b1_marginal`, as `fhpbc_b1_marginal_proof`, of type `FhpbcMarginalStatement`.

For a complex Schwartz test `θ` on `ℝ^m × ℝ` vanishing at every `(u,t)` with `u ∉ A`, `A`
compact, write `F(s) = ∫ θ(u,s) du` (the base `fhpab4_marginal θ`, definitionally the marginal of
the statement) and `∂_t θ(x) = Dθ(x) e_t`.

1. **Checkpoint 1 (marginal calculus).** Along the time line `s ↦ (u,s)` the slice has derivative
   `∂_t θ(u,s)` (chain rule), which vanishes for `u ∉ A` (the slice is identically zero there).
   The compact-support indicator `1_A · ‖θ‖_{0,1} ‖e_t‖` dominates every `∂_t θ(·,s)`, so
   differentiation under the integral sign gives `F' = ∫ ∂_t θ(u,·) du` everywhere and
   dominated continuity gives `F' ∈ C⁰`; hence `F ∈ C¹`. Integrability and `∫ F = ∫ θ` follow
   from Fubini through the measure-preserving coordinates; the weighted bound from
   `‖F s‖ₑ ≤ ∫⁻ ‖θ(u,s)‖ₑ du`, the same for `F'`, and Tonelli in the same coordinates.
2. **Checkpoint 2 (kernel interchange).** At fixed `t` the kernel integrand
   `|h|^{-3/2} (θ(u,t) - θ(u,t-h))` is dominated on `ℝ^m × ℝ` by
   `1_A(u) · testKernelControl θ · cancellationWeight h` (`norm_testKernelIntegrand_le`), so
   Fubini in `(u,h)` gives `∫ testKernel θ (u,t) du = D F (t)` for every `t`.

The helpers `fhpab4_*` from the proof of `fhpa_spatialIntegral_testKernel_decay` are reused.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-- As in the construction of `testKernel`: a direct route to this instance (its search on the `L²`
product times out); proof-local. -/
local instance fhpbb1m_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-! ## Time lines and slices -/

/-- The time line `s ↦ (u,s)` has velocity `e_t`. -/
theorem fhpbb1m_hasDerivAt_line (u : Spatial m) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (WithLp.toLp 2 (u, s) : FourierSpace m)) (timeVector m) s := by
  have hp : HasDerivAt (fun s : ℝ => ((u, s) : Spatial m × ℝ)) ((0 : Spatial m), (1 : ℝ)) s :=
    (hasDerivAt_const s u).prodMk (hasDerivAt_id' (x := s))
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ (Spatial m) ℝ).symm.hasFDerivAt.comp_hasDerivAt
    s hp
  simp only [Function.comp_def, WithLp.prodContinuousLinearEquiv_symm_apply] at h
  exact h

theorem fhpbb1m_continuous_line (u : Spatial m) :
    Continuous fun s : ℝ => (WithLp.toLp 2 (u, s) : FourierSpace m) :=
  (WithLp.prod_continuous_toLp 2 (Spatial m) ℝ).comp (continuous_const.prodMk continuous_id)

/-- The time derivative of a slice is `∂_t θ = Dθ e_t`. -/
theorem fhpbb1m_hasDerivAt_slice (θ : 𝓢(FourierSpace m, ℂ)) (u : Spatial m) (s : ℝ) :
    HasDerivAt (fun s : ℝ => θ (WithLp.toLp 2 (u, s)))
      (fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m)) s :=
  θ.differentiableAt.hasFDerivAt.comp_hasDerivAt s (fhpbb1m_hasDerivAt_line u s)

theorem fhpbb1m_continuous_dt (θ : 𝓢(FourierSpace m, ℂ)) :
    Continuous fun x : FourierSpace m => fderiv ℝ (⇑θ) x (timeVector m) :=
  ((θ.smooth ⊤).continuous_fderiv (by simp)).clm_apply continuous_const

theorem fhpbb1m_norm_dt_le (θ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    ‖fderiv ℝ (⇑θ) x (timeVector m)‖ ≤ SchwartzMap.seminorm ℝ 0 1 θ * ‖timeVector m‖ := by
  refine ((fderiv ℝ (⇑θ) x).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa only [norm_iteratedFDeriv_one] using θ.norm_iteratedFDeriv_le_seminorm ℝ 1 x

section Support

variable {θ : 𝓢(FourierSpace m, ℂ)} {A : Set (Spatial m)}

theorem fhpbb1m_slice_eq_zero (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) {u : Spatial m}
    (hu : u ∉ A) (s : ℝ) : θ (WithLp.toLp 2 (u, s)) = 0 :=
  hθ _ hu

/-- Off `A` the slice vanishes identically, so its time derivative vanishes. -/
theorem fhpbb1m_dt_eq_zero (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) {u : Spatial m}
    (hu : u ∉ A) (s : ℝ) : fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m) = 0 := by
  have h0 : (fun s : ℝ => θ (WithLp.toLp 2 (u, s))) = fun _ => 0 :=
    funext (fhpbb1m_slice_eq_zero hθ hu)
  have h := fhpbb1m_hasDerivAt_slice θ u s
  rw [h0] at h
  exact h.unique (hasDerivAt_const s 0)

theorem fhpbb1m_integrable_slice (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A)
    (s : ℝ) : Integrable (fun u : Spatial m => θ (WithLp.toLp 2 (u, s))) volume :=
  fhpab4_integrable_of_le hA (θ.continuous.comp (fhpab4_continuous_toLp s)).aestronglyMeasurable
    (B := SchwartzMap.seminorm ℝ 0 0 θ) (fun _ _ => θ.norm_le_seminorm ℝ _)
    (fun _ hu => fhpbb1m_slice_eq_zero hθ hu s)

/-- The compact-support indicator dominates every time derivative. -/
theorem fhpbb1m_norm_dt_le_indicator (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) (s : ℝ)
    (u : Spatial m) :
    ‖fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m)‖ ≤
      A.indicator (fun _ => SchwartzMap.seminorm ℝ 0 1 θ * ‖timeVector m‖) u :=
  fhpab4_norm_le_indicator (f := fun u => fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m))
    (fun _ _ => fhpbb1m_norm_dt_le θ _) (fun _ hu => fhpbb1m_dt_eq_zero hθ hu s) u

end Support

/-! ## Checkpoint 1: marginal calculus -/

/-- The candidate derivative `F'(s) = ∫ ∂_t θ(u,s) du` of the marginal. -/
def fhpbb1m_marginalDeriv (θ : 𝓢(FourierSpace m, ℂ)) (s : ℝ) : ℂ :=
  ∫ u : Spatial m, fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m)

section Calculus

variable {θ : 𝓢(FourierSpace m, ℂ)} {A : Set (Spatial m)}

/-- Differentiation under the integral sign, dominated by the compact-support indicator. -/
theorem fhpbb1m_hasDerivAt_marginal (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A)
    (s₀ : ℝ) : HasDerivAt (fhpab4_marginal θ) (fhpbb1m_marginalDeriv θ s₀) s₀ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s u => θ (WithLp.toLp 2 (u, s)))
    (F' := fun s u => fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m))
    (bound := A.indicator fun _ => SchwartzMap.seminorm ℝ 0 1 θ * ‖timeVector m‖)
    (x₀ := s₀) (s := univ) univ_mem
    (Eventually.of_forall fun s =>
      (θ.continuous.comp (fhpab4_continuous_toLp s)).aestronglyMeasurable)
    (fhpbb1m_integrable_slice hA hθ s₀)
    ((fhpbb1m_continuous_dt θ).comp (fhpab4_continuous_toLp s₀)).aestronglyMeasurable
    (Eventually.of_forall fun u s _ => fhpbb1m_norm_dt_le_indicator hθ s u)
    (fhpab4_integrable_indicator hA _)
    (Eventually.of_forall fun u s _ => fhpbb1m_hasDerivAt_slice θ u s)).2

theorem fhpbb1m_deriv_marginal (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) :
    deriv (fhpab4_marginal θ) = fhpbb1m_marginalDeriv θ :=
  funext fun s => (fhpbb1m_hasDerivAt_marginal hA hθ s).deriv

theorem fhpbb1m_continuous_marginalDeriv (hA : IsCompact A)
    (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) : Continuous (fhpbb1m_marginalDeriv θ) :=
  continuous_of_dominated
    (fun s => ((fhpbb1m_continuous_dt θ).comp (fhpab4_continuous_toLp s)).aestronglyMeasurable)
    (fun s => Eventually.of_forall (fhpbb1m_norm_dt_le_indicator hθ s))
    (fhpab4_integrable_indicator hA _)
    (Eventually.of_forall fun u => (fhpbb1m_continuous_dt θ).comp (fhpbb1m_continuous_line u))

theorem fhpbb1m_contDiff_marginal (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) :
    ContDiff ℝ 1 (fhpab4_marginal θ) := by
  refine contDiff_one_iff_deriv.2
    ⟨fun s => (fhpbb1m_hasDerivAt_marginal hA hθ s).differentiableAt, ?_⟩
  rw [fhpbb1m_deriv_marginal hA hθ]
  exact fhpbb1m_continuous_marginalDeriv hA hθ

end Calculus

/-- The test in ordinary coordinates is integrable for the product volume. -/
theorem fhpbb1m_integrable_coordinates (θ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun p : Spatial m × ℝ => θ (WithLp.toLp 2 p))
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
  rw [← volume_coordinates_eq_prod]
  exact (integrable_fourierCoordinates_symm_iff (θ : FourierSpace m → ℂ)).mpr θ.integrable

theorem fhpbb1m_integrable_marginal (θ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fhpab4_marginal θ) volume :=
  (fhpbb1m_integrable_coordinates θ).integral_prod_right

theorem fhpbb1m_integral_marginal (θ : 𝓢(FourierSpace m, ℂ)) :
    ∫ s, fhpab4_marginal θ s = ∫ x, θ x := by
  calc ∫ s, fhpab4_marginal θ s = ∫ p : Coordinates m, θ (WithLp.toLp 2 p) := by
        rw [volume_coordinates_eq_prod]
        exact (integral_prod_symm _ (fhpbb1m_integrable_coordinates θ)).symm
    _ = ∫ x, θ x := integral_fourierCoordinates_symm (θ : FourierSpace m → ℂ)

/-- The integrand of the weighted norm `N(θ)`. -/
def fhpbb1m_weight (θ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + |(WithLp.ofLp x).2|) *
    (‖θ x‖ₑ + ‖fderiv ℝ (⇑θ) x (timeVector m)‖ₑ)

theorem fhpbb1m_measurable_weight (θ : 𝓢(FourierSpace m, ℂ)) :
    Measurable (fhpbb1m_weight θ) :=
  (ENNReal.measurable_ofReal.comp
      (measurable_const.add (measurable_timeCoordinate m).abs)).mul
    (θ.continuous.measurable.enorm.add (fhpbb1m_continuous_dt θ).measurable.enorm)

/-- Tonelli in ordinary coordinates: `N(θ) = ∫⁻ s, ∫⁻ u, w(u,s)`. -/
theorem fhpbb1m_weightedTestNorm_eq (θ : 𝓢(FourierSpace m, ℂ)) :
    fhp_weightedTestNorm (⇑θ) =
      ∫⁻ s : ℝ, ∫⁻ u : Spatial m, fhpbb1m_weight θ (WithLp.toLp 2 (u, s)) := by
  calc fhp_weightedTestNorm (⇑θ) = ∫⁻ x, fhpbb1m_weight θ x := rfl
    _ = ∫⁻ p : Spatial m × ℝ, fhpbb1m_weight θ (WithLp.toLp 2 p)
          ∂((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) :=
        ((fourierCoordinates_symm_measurePreserving_prod m).lintegral_comp_emb
          (fourierCoordinatesMeasurableEquiv m).symm.measurableEmbedding
          (fhpbb1m_weight θ)).symm
    _ = _ := lintegral_prod_symm _
        ((fhpbb1m_measurable_weight θ).comp
          (fourierCoordinatesMeasurableEquiv m).symm.measurable).aemeasurable

/-- The weighted bound `∫⁻ (1 + |s|) (‖F s‖ₑ + ‖F' s‖ₑ) ≤ N(θ)`. -/
theorem fhpbb1m_weighted_le {θ : 𝓢(FourierSpace m, ℂ)} {A : Set (Spatial m)} (hA : IsCompact A)
    (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) :
    ∫⁻ s : ℝ, ENNReal.ofReal (1 + |s|) *
        (‖fhpab4_marginal θ s‖ₑ + ‖deriv (fhpab4_marginal θ) s‖ₑ) ≤
      fhp_weightedTestNorm (⇑θ) := by
  rw [fhpbb1m_weightedTestNorm_eq, fhpbb1m_deriv_marginal hA hθ]
  refine lintegral_mono fun s => ?_
  calc ENNReal.ofReal (1 + |s|) * (‖fhpab4_marginal θ s‖ₑ + ‖fhpbb1m_marginalDeriv θ s‖ₑ)
      ≤ ENNReal.ofReal (1 + |s|) *
          ((∫⁻ u : Spatial m, ‖θ (WithLp.toLp 2 (u, s))‖ₑ) +
            ∫⁻ u : Spatial m, ‖fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m)‖ₑ) := by
        gcongr
        · exact enorm_integral_le_lintegral_enorm _
        · exact enorm_integral_le_lintegral_enorm _
    _ ≤ ENNReal.ofReal (1 + |s|) *
          ∫⁻ u : Spatial m, (‖θ (WithLp.toLp 2 (u, s))‖ₑ +
            ‖fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m)‖ₑ) := by
        gcongr
        exact le_lintegral_add _ _
    _ ≤ ∫⁻ u : Spatial m, ENNReal.ofReal (1 + |s|) * (‖θ (WithLp.toLp 2 (u, s))‖ₑ +
            ‖fderiv ℝ (⇑θ) (WithLp.toLp 2 (u, s)) (timeVector m)‖ₑ) :=
        lintegral_const_mul_le _ _
    _ = ∫⁻ u : Spatial m, fhpbb1m_weight θ (WithLp.toLp 2 (u, s)) := rfl

/-! ## Checkpoint 2: the kernel interchange at fixed time -/

section Kernel

variable {θ : 𝓢(FourierSpace m, ℂ)} {A : Set (Spatial m)}

theorem fhpbb1m_integrand_eq_zero (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) {u : Spatial m}
    (hu : u ∉ A) (t h : ℝ) : testKernelIntegrand θ (WithLp.toLp 2 (u, t)) h = 0 := by
  rw [fhpab4_integrand_eq, fhpbb1m_slice_eq_zero hθ hu, fhpbb1m_slice_eq_zero hθ hu, sub_self,
    mul_zero]

/-- At fixed time the kernel integrand is integrable in `(u,h)`, dominated by
`1_A(u) · testKernelControl θ · cancellationWeight h`. -/
theorem fhpbb1m_integrable_prod (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A)
    (t : ℝ) :
    Integrable (fun p : Spatial m × ℝ => testKernelIntegrand θ (WithLp.toLp 2 (p.1, t)) p.2)
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
  have hmeas : Measurable fun p : Spatial m × ℝ =>
      ((WithLp.toLp 2 (p.1, t) : FourierSpace m), p.2) :=
    ((fourierCoordinatesMeasurableEquiv m).symm.measurable.comp
      (measurable_fst.prodMk measurable_const)).prodMk measurable_snd
  refine ((fhpab4_integrable_indicator hA (testKernelControl θ)).mul_prod
    integrable_cancellationWeight).mono'
    ((stronglyMeasurable_testKernelIntegrand θ).comp_measurable hmeas).aestronglyMeasurable ?_
  refine Eventually.of_forall fun p => ?_
  by_cases hp : p.1 ∈ A
  · rw [indicator_of_mem hp]
    exact norm_testKernelIntegrand_le θ _ p.2
  · rw [indicator_of_notMem hp, zero_mul, fhpbb1m_integrand_eq_zero hθ hp, norm_zero]

theorem fhpbb1m_integral_inner (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A)
    (t h : ℝ) :
    ∫ u : Spatial m, testKernelIntegrand θ (WithLp.toLp 2 (u, t)) h =
      ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (fhpab4_marginal θ t - fhpab4_marginal θ (t - h)) := by
  simp_rw [fhpab4_integrand_eq]
  rw [integral_const_mul, integral_sub (fhpbb1m_integrable_slice hA hθ t)
    (fhpbb1m_integrable_slice hA hθ (t - h))]
  rfl

/-- **Checkpoint 2.** `∫ testKernel θ (u,t) du = D F (t)` for every `t`. -/
theorem fhpbb1m_kernel_eq (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A)
    (t : ℝ) :
    ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t)) =
      fhpbc_halfDeriv1D (fhpab4_marginal θ) t := by
  have hswap : (∫ u : Spatial m, ∫ h : ℝ, testKernelIntegrand θ (WithLp.toLp 2 (u, t)) h) =
      ∫ h : ℝ, ∫ u : Spatial m, testKernelIntegrand θ (WithLp.toLp 2 (u, t)) h :=
    integral_integral_swap (fhpbb1m_integrable_prod hA hθ t)
  calc ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t))
      = ∫ u : Spatial m, (FractionalKernel.kappa : ℂ) *
          ∫ h : ℝ, testKernelIntegrand θ (WithLp.toLp 2 (u, t)) h := rfl
    _ = (FractionalKernel.kappa : ℂ) *
          ∫ u : Spatial m, ∫ h : ℝ, testKernelIntegrand θ (WithLp.toLp 2 (u, t)) h :=
        integral_const_mul _ _
    _ = (FractionalKernel.kappa : ℂ) *
          ∫ h : ℝ, ∫ u : Spatial m, testKernelIntegrand θ (WithLp.toLp 2 (u, t)) h := by
        rw [hswap]
    _ = fhpbc_halfDeriv1D (fhpab4_marginal θ) t := by
        unfold fhpbc_halfDeriv1D
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun h => fhpbb1m_integral_inner hA hθ t h)

end Kernel

/-! ## The statement -/

/-- **The spatial marginal of a test** (`fhpbc_b1_marginal`, of type
`FhpbcMarginalStatement`): the marginal `F(s) = ∫ θ(u,s) du` of a Schwartz test supported
spatially in a compact set is `C¹` and integrable, `∫ F = ∫ θ`,
`∫⁻ (1 + |s|) (‖F‖ₑ + ‖F'‖ₑ) ≤ N(θ)`, and `∫ testKernel θ (u,t) du = D F (t)` for every `t`. -/
theorem fhpbc_b1_marginal_proof : FhpbcMarginalStatement := by
  intro m A hA θ hθ
  exact ⟨fhpbb1m_contDiff_marginal hA hθ, fhpbb1m_integrable_marginal θ,
    fhpbb1m_integral_marginal θ, fhpbb1m_weighted_le hA hθ, fun t => fhpbb1m_kernel_eq hA hθ t⟩

end ParabolicRectifiability.Foundations
