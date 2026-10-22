import ParabolicRectifiability.Foundations.Statements.CompactBridge
import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel

/-! # Proof of the compact-bridge representative identification

The representative part of the compact bridge.

Fix a normal component `i` and a real compact smooth test `φ`, and write `Dφ` for
`|D_t|^{1/2}φ`. The argument has three steps.

* **Mean zero of the test derivative.**
  `Dφ` agrees a.e. with the absolutely convergent `testKernel`, and
  `∫ testKernel ψ = 0` for every compactly supported Schwartz `ψ`. The difference
  integrand `|h|^{-3/2}(ψ(x) - ψ(x - h e_t))` is absolutely integrable on the product of
  `FourierSpace m` and `ℝ`: for `|h| ≤ 1` its `x`-integral is at most
  `|h|^{-1/2}` times a constant (first-order cancellation on a fixed compact thickening of
  the support), and for `|h| > 1` at most `2‖ψ‖₁ |h|^{-3/2}`. Fubini and translation
  invariance of `∫ x, ψ(x - h e_t)` then give zero.
* **Ordered Fubini for an absolutely integrable function.** If `F ∈ L¹(FourierSpace m)`, then
  in the coordinates `ℝ^m × ℝ` the spatial integrand is integrable for a.e. time, the spatial
  bracket is integrable on `ℝ`, and its integrals over `[-R, R]` converge to `∫ F`.
* **Assembly.** `(a + H) Dφ = a Dφ + H Dφ` is integrable (`Dφ ∈ L¹`, and `H, Dφ ∈ L²`), and
  `∫ (a + H) Dφ = a · 0 + ∫ H Dφ = ∫ g φ` by `RepHalf`. Neither the zero-mean condition on
  `φ`, nor compact support of `H`, nor a Lipschitz bound is used.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology SchwartzMap ContDiff

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

section KernelMean

variable {m : ℕ}

/-- For `|h| ≤ 1` the first-order difference of a test vanishes off the closed
`‖e_t‖`-thickening of its support, and is bounded there by the first-order seminorm. -/
theorem fcond_norm_test_difference_le_indicator (ψ : 𝓢(FourierSpace m, ℂ)) {h : ℝ}
    (hh : |h| ≤ 1) (x : FourierSpace m) :
    ‖ψ x - ψ (x - h • timeVector m)‖ ≤
      (Metric.cthickening ‖timeVector m‖ (tsupport ψ)).indicator
        (fun _ => (SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) * |h|) x := by
  by_cases hx : x ∈ Metric.cthickening ‖timeVector m‖ (tsupport ψ)
  · rw [indicator_of_mem hx]
    exact norm_test_difference_le_time ψ x h
  · rw [indicator_of_notMem hx]
    have h1 : x ∉ tsupport ψ := fun h' => hx (Metric.self_subset_cthickening _ h')
    have h2 : x - h • timeVector m ∉ tsupport ψ := by
      intro h'
      apply hx
      apply Metric.mem_cthickening_of_dist_le x _ _ _ h'
      rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hh
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2, sub_zero,
      norm_zero]

/-- Small shifts: the `L¹` norm of the difference is `O(|h|)`. -/
theorem fcond_integral_norm_test_difference_le_small (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) {h : ℝ} (hh : |h| ≤ 1) :
    ∫ x, ‖ψ x - ψ (x - h • timeVector m)‖ ≤
      (SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) * |h| *
        (volume : Measure (FourierSpace m)).real
          (Metric.cthickening ‖timeVector m‖ (tsupport ψ)) := by
  have hK : IsCompact (Metric.cthickening ‖timeVector m‖ (tsupport ψ)) :=
    IsCompact.cthickening hc
  calc ∫ x, ‖ψ x - ψ (x - h • timeVector m)‖
      ≤ ∫ x, (Metric.cthickening ‖timeVector m‖ (tsupport ψ)).indicator
          (fun _ => (SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) * |h|) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          ((integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet)
          (Eventually.of_forall (fcond_norm_test_difference_le_indicator ψ hh))
    _ = _ := by
        rw [integral_indicator_const _ hK.measurableSet, smul_eq_mul, mul_comm]

/-- All shifts: the `L¹` norm of the difference is at most `2‖ψ‖₁`. -/
theorem fcond_integral_norm_test_difference_le_two (ψ : 𝓢(FourierSpace m, ℂ)) (h : ℝ) :
    ∫ x, ‖ψ x - ψ (x - h • timeVector m)‖ ≤ 2 * ∫ x, ‖ψ x‖ := by
  have hi : Integrable (fun x => ‖ψ x‖) volume := ψ.integrable.norm
  have hi' : Integrable (fun x => ‖ψ (x - h • timeVector m)‖) volume :=
    (ψ.integrable.comp_sub_right (h • timeVector m)).norm
  have htr : ∫ x, ‖ψ (x - h • timeVector m)‖ = ∫ x, ‖ψ x‖ :=
    integral_sub_right_eq_self (fun x => ‖ψ x‖) (h • timeVector m)
  calc ∫ x, ‖ψ x - ψ (x - h • timeVector m)‖
      ≤ ∫ x, (‖ψ x‖ + ‖ψ (x - h • timeVector m)‖) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) (hi.add hi')
          (Eventually.of_forall fun x => norm_sub_le _ _)
    _ = 2 * ∫ x, ‖ψ x‖ := by
        rw [integral_add hi hi', htr]
        ring

/-- Each `h`-fiber of the difference integrand is integrable in `x`. -/
theorem fcond_integrable_testKernelIntegrand_fiber (ψ : 𝓢(FourierSpace m, ℂ)) (h : ℝ) :
    Integrable (fun x => testKernelIntegrand ψ x h) volume :=
  (ψ.integrable.sub (ψ.integrable.comp_sub_right (h • timeVector m))).const_mul _

theorem fcond_integral_norm_testKernelIntegrand (ψ : 𝓢(FourierSpace m, ℂ)) (h : ℝ) :
    ∫ x, ‖testKernelIntegrand ψ x h‖ =
      |h| ^ (-3 / 2 : ℝ) * ∫ x, ‖ψ x - ψ (x - h • timeVector m)‖ := by
  have he : (fun x => ‖testKernelIntegrand ψ x h‖) =
      fun x => |h| ^ (-3 / 2 : ℝ) * ‖ψ x - ψ (x - h • timeVector m)‖ := by
    funext x
    rw [testKernelIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
  rw [he, integral_const_mul]

/-- The `x`-integral of the absolute difference integrand is dominated by the integrable
`cancellationWeight`, with a constant depending only on `ψ`. -/
theorem fcond_integral_norm_testKernelIntegrand_le (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) (h : ℝ) :
    ∫ x, ‖testKernelIntegrand ψ x h‖ ≤
      ((SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) *
          (volume : Measure (FourierSpace m)).real
            (Metric.cthickening ‖timeVector m‖ (tsupport ψ)) +
        2 * ∫ x, ‖ψ x‖) * cancellationWeight h := by
  rw [fcond_integral_norm_testKernelIntegrand]
  have hLc0 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖ := by positivity
  have hV0 : 0 ≤ (volume : Measure (FourierSpace m)).real
      (Metric.cthickening ‖timeVector m‖ (tsupport ψ)) := measureReal_nonneg
  have hA0 : 0 ≤ ∫ x, ‖ψ x‖ := integral_nonneg fun x => norm_nonneg _
  have hw0 : 0 ≤ |h| ^ (-3 / 2 : ℝ) := Real.rpow_nonneg (abs_nonneg h) _
  unfold cancellationWeight
  split_ifs with hh
  · have hp : |h| ^ (-3 / 2 : ℝ) * |h| = |h| ^ (-1 / 2 : ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one |h|]
      rw [← Real.rpow_add' (abs_nonneg h) (by norm_num : (-3 / 2 : ℝ) + 1 ≠ 0)]
      norm_num
    calc |h| ^ (-3 / 2 : ℝ) * ∫ x, ‖ψ x - ψ (x - h • timeVector m)‖
        ≤ |h| ^ (-3 / 2 : ℝ) * ((SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) * |h| *
            (volume : Measure (FourierSpace m)).real
              (Metric.cthickening ‖timeVector m‖ (tsupport ψ))) :=
          mul_le_mul_of_nonneg_left (fcond_integral_norm_test_difference_le_small ψ hc hh) hw0
      _ = (SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) *
            (volume : Measure (FourierSpace m)).real
              (Metric.cthickening ‖timeVector m‖ (tsupport ψ)) * |h| ^ (-1 / 2 : ℝ) := by
          rw [← hp]
          ring
      _ ≤ _ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
            (Real.rpow_nonneg (abs_nonneg h) _)
  · calc |h| ^ (-3 / 2 : ℝ) * ∫ x, ‖ψ x - ψ (x - h • timeVector m)‖
        ≤ |h| ^ (-3 / 2 : ℝ) * (2 * ∫ x, ‖ψ x‖) :=
          mul_le_mul_of_nonneg_left (fcond_integral_norm_test_difference_le_two ψ h) hw0
      _ ≤ _ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left (mul_nonneg hLc0 hV0)) hw0

/-- The difference integrand of a compact test is absolutely integrable on the product of
the Euclidean space and the shift line. -/
theorem fcond_integrable_testKernelIntegrand_prod (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) :
    Integrable (Function.uncurry (testKernelIntegrand ψ))
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) := by
  have hm : StronglyMeasurable (Function.uncurry (testKernelIntegrand ψ)) :=
    stronglyMeasurable_testKernelIntegrand ψ
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun h => fcond_integrable_testKernelIntegrand_fiber ψ h, ?_⟩
  exact (integrable_cancellationWeight.const_mul
      ((SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) *
          (volume : Measure (FourierSpace m)).real
            (Metric.cthickening ‖timeVector m‖ (tsupport ψ)) +
        2 * ∫ x, ‖ψ x‖)).mono'
    hm.norm.integral_prod_left'.aestronglyMeasurable
    (Eventually.of_forall fun h =>
      (Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)).trans_le
        (fcond_integral_norm_testKernelIntegrand_le ψ hc h))

/-- `∫ |D_t|^{1/2}ψ = 0` for every compactly supported Schwartz test, through the
absolutely convergent pointwise kernel. -/
theorem fcond_integral_testKernel_eq_zero (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) : ∫ x, testKernel ψ x = 0 := by
  have hint := fcond_integrable_testKernelIntegrand_prod ψ hc
  have hfiber : ∀ h : ℝ, ∫ x, testKernelIntegrand ψ x h = 0 := by
    intro h
    have h1 : ∫ x, ψ (x - h • timeVector m) = ∫ x, ψ x :=
      integral_sub_right_eq_self (⇑ψ) (h • timeVector m)
    have h2 : ∫ x, (ψ x - ψ (x - h • timeVector m)) =
        (∫ x, ψ x) - ∫ x, ψ (x - h • timeVector m) :=
      integral_sub ψ.integrable (ψ.integrable.comp_sub_right _)
    have h3 : ∫ x, testKernelIntegrand ψ x h =
        ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * ∫ x, (ψ x - ψ (x - h • timeVector m)) :=
      integral_const_mul _ _
    rw [h3, h2, h1, sub_self, mul_zero]
  have hk : ∫ x, testKernel ψ x =
      (ParabolicRectifiability.FractionalKernel.kappa : ℂ) *
        ∫ x, ∫ h, testKernelIntegrand ψ x h :=
    integral_const_mul _ _
  rw [hk, integral_integral_swap hint]
  simp only [hfiber, integral_zero, mul_zero]

end KernelMean

section OrderedFubini

variable {m : ℕ}

/-- Ordered windowed Fubini: an absolutely integrable function on `FourierSpace m` has a.e.
integrable spatial slices, an integrable spatial bracket, and window integrals over
`[-R, R]` converging to its total integral. -/
theorem fcond_ordered_of_integrable {F : FourierSpace m → ℂ} (hF : Integrable F volume) :
    (∀ᵐ t : ℝ, Integrable (fun u : Spatial m => F (WithLp.toLp 2 (u, t)))) ∧
    Integrable (fun t : ℝ => ∫ u : Spatial m, F (WithLp.toLp 2 (u, t))) ∧
    Tendsto (fun R : ℝ => ∫ t in Icc (-R) R, ∫ u : Spatial m, F (WithLp.toLp 2 (u, t)))
      atTop (𝓝 (∫ x, F x)) := by
  have hFp : Integrable (fun p : Spatial m × ℝ => F (WithLp.toLp 2 p))
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
    rw [← volume_coordinates_eq_prod]
    exact (integrable_fourierCoordinates_symm_iff F).mpr hF
  have hB : Integrable (fun t : ℝ => ∫ u : Spatial m, F (WithLp.toLp 2 (u, t))) :=
    hFp.integral_prod_right
  refine ⟨hFp.prod_left_ae, hB, ?_⟩
  have hval : ∫ t : ℝ, ∫ u : Spatial m, F (WithLp.toLp 2 (u, t)) = ∫ x, F x := by
    rw [← integral_fourierCoordinates_symm F, volume_coordinates_eq_prod]
    exact (integral_prod_symm _ hFp).symm
  rw [← hval]
  refine (intervalIntegral_tendsto_integral hB tendsto_neg_atTop_atBot tendsto_id).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  show ∫ t in (-R)..R, (∫ u : Spatial m, F (WithLp.toLp 2 (u, t))) =
    ∫ t in Icc (-R) R, ∫ u : Spatial m, F (WithLp.toLp 2 (u, t))
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

end OrderedFubini

section Representative

variable {m : ℕ}

/-- Scalar compact bridge: if `g` represents the `L²` half derivative of `H` on all real
compact smooth tests, then `g` represents the general homogeneous half derivative of
`a + H`, including both ordered-integrability clauses. -/
theorem fcond_representsHomogeneous_const_add {H g : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (hrep : RepHalf hH g Set.univ) (a : ℝ) :
    RepresentsHomogeneousHalfTimeDerivative (fun x => a + H x) g := by
  refine ⟨locallyIntegrableOn_univ.mp hrep.2.1, ?_⟩
  intro φ hφ hc _
  have hcψ : HasCompactSupport (realCompactTest φ hφ hc) := by
    change IsCompact (tsupport (realCompactTest φ hφ hc))
    rw [tsupport_realCompactTest]
    exact hc
  have hD : Integrable (fun x => halfTimeDeriv m (realCompactTest φ hφ hc) x) volume :=
    (integrable_testKernel_of_hasCompactSupport _ hcψ).congr
      (testKernel_ae_halfTimeDeriv (realCompactTest φ hφ hc))
  have hHD : Integrable
      (fun x => (H x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) volume :=
    hH.ofReal.integrable_mul (Lp.memLp _)
  have hsplit : (fun x => ((a + H x : ℝ) : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) =
      fun x => (a : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x +
        (H x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x := by
    funext x
    push_cast
    ring
  have hF : Integrable
      (fun x => ((a + H x : ℝ) : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x) volume := by
    rw [hsplit]
    exact (hD.const_mul _).add hHD
  obtain ⟨h1, h2, h3⟩ := fcond_ordered_of_integrable hF
  refine ⟨h1, fun R => h2.integrableOn, ?_⟩
  have h0 : ∫ x, halfTimeDeriv m (realCompactTest φ hφ hc) x = 0 := by
    rw [← integral_congr_ae (testKernel_ae_halfTimeDeriv (realCompactTest φ hφ hc))]
    exact fcond_integral_testKernel_eq_zero _ hcψ
  have hval : ∫ x, ((a + H x : ℝ) : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x =
      ∫ x, (g x : ℂ) * (φ x : ℂ) := by
    rw [hsplit, integral_add (hD.const_mul _) hHD, integral_const_mul, h0, mul_zero, zero_add]
    exact hrep.2.2 φ hφ hc (subset_univ _)
  rw [← hval]
  exact h3

/-- The normal components of `c + H` are the constants `c_i` plus the components of `H`. -/
theorem fcond_normalFourierComponent_const_add {n : ℕ} (W : Submodule ℝ (Spatial n))
    (c : W.orthogonal) (H : SubspaceSpace W → W.orthogonal)
    (i : Fin (Module.finrank ℝ W.orthogonal)) :
    normalFourierComponent W (fun p => c + H p) i =
      fun x => normalCoordinates W c i + normalFourierComponent W H i x := by
  funext x
  simp only [normalFourierComponent, map_add, PiLp.add_apply]

end Representative

/-- Representative identification for the compact bridge:
`CompactBridgeRepresentativeStatement`. -/
theorem compactBridgeRepresentative_proof : CompactBridgeRepresentativeStatement := by
  intro n W c H g hrep i
  obtain ⟨hH, hR⟩ := hrep i
  rw [fcond_normalFourierComponent_const_add]
  exact fcond_representsHomogeneous_const_add hH hR _

end ParabolicRectifiability.Foundations
