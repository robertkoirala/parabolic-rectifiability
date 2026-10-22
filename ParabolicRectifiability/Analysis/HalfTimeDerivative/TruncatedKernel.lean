import ParabolicRectifiability.Analysis.HalfTimeDerivative.SpectralApproximation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Physical symmetric truncations

The kernels use ordinary Lebesgue measure and the scalar annuli `symmetricAnnulus`.
The physical operator is defined by an absolutely convergent time integral.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology SchwartzMap FourierTransform ENNReal

namespace ParabolicRectifiability.HalfTimeDerivative
open FractionalKernel

-- Select the normed-space continuity instance directly, avoiding a module-topology search.
local instance (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-- The integrable kernel on the exact symmetric annulus, including the empty initial annulus. -/
def truncatedKernel (j : ℕ) (h : ℝ) : ℝ :=
  (symmetricAnnulus j).indicator (fun h : ℝ => |h| ^ (-3 / 2 : ℝ)) h

@[simp] theorem truncatedKernel_zero_index (h : ℝ) : truncatedKernel 0 h = 0 := by
  simp [truncatedKernel]

@[simp] theorem truncatedKernel_zero (j : ℕ) : truncatedKernel j 0 = 0 := by
  simp [truncatedKernel]

theorem truncatedKernel_nonneg (j : ℕ) (h : ℝ) : 0 ≤ truncatedKernel j h := by
  exact indicator_nonneg (fun h _ => Real.rpow_nonneg (abs_nonneg h) _) h

theorem measurable_truncatedKernel (j : ℕ) : Measurable (truncatedKernel j) := by
  exact (measurable_abs.pow_const _).indicator (measurableSet_symmetricAnnulus j)

@[simp] theorem truncatedKernel_neg (j : ℕ) (h : ℝ) :
    truncatedKernel j (-h) = truncatedKernel j h := by
  classical
  by_cases hh : h ∈ symmetricAnnulus j <;> simp [truncatedKernel, hh]

theorem integrable_truncatedKernel (j : ℕ) : Integrable (truncatedKernel j) volume := by
  have hs : volume (symmetricAnnulus j) < ∞ := by
    apply lt_of_le_of_lt (measure_mono (t := Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1)) ?_)
      (measure_Ioo_lt_top)
    intro h hh
    exact abs_lt.mp hh.2
  apply IntegrableOn.integrable_indicator _ (measurableSet_symmetricAnnulus j)
  apply IntegrableOn.of_bound hs ((measurable_abs.pow_const _).aestronglyMeasurable) ((1 / ((j : ℝ) + 1)) ^ (-3 / 2 : ℝ))
  filter_upwards [ae_restrict_mem (measurableSet_symmetricAnnulus j)] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hh.1.le (by norm_num)

theorem integral_truncatedKernel_nonneg (j : ℕ) : 0 ≤ ∫ h, truncatedKernel j h :=
  integral_nonneg (truncatedKernel_nonneg j)

theorem integral_truncatedKernel_eq_integral_norm (j : ℕ) :
    (∫ h, truncatedKernel j h) = ∫ h, ‖truncatedKernel j h‖ := by
  simp only [Real.norm_eq_abs, abs_of_nonneg (truncatedKernel_nonneg j _)]

/-- A time translate of a Schwartz test, with the physical shift `x - h e_t`. -/
def timeTranslate {m : ℕ} (h : ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) : 𝓢(FourierSpace m, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (h • timeVector m) ψ

@[simp] theorem timeTranslate_apply {m : ℕ} (h : ℝ) (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) : timeTranslate h ψ x = ψ (x - h • timeVector m) := rfl

theorem norm_timeTranslate_toLp {m : ℕ} (h : ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖(timeTranslate h ψ).toLp 2 volume‖ = ‖ψ.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  congr 1
  exact eLpNorm_comp_measurePreserving ψ.continuous.aestronglyMeasurable
    (measurePreserving_sub_right volume (h • timeVector m))

theorem norm_sub_timeTranslate_toLp_le {m : ℕ} (h : ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖(ψ - timeTranslate h ψ).toLp 2 volume‖ ≤ 2 * ‖ψ.toLp 2 volume‖ := by
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume (ψ - timeTranslate h ψ)‖ ≤ _
  rw [map_sub]
  apply (norm_sub_le _ _).trans
  simp only [SchwartzMap.toLpCLM_apply, norm_timeTranslate_toLp]
  linarith

/-- The genuine physical time integral. Its integrability is proved independently below. -/
def physicalTruncation {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) : ℂ :=
  (kappa : ℂ) * ∫ h : ℝ, (truncatedKernel j h : ℂ) * (ψ x - ψ (x - h • timeVector m))

theorem stronglyMeasurable_kernel_difference {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable (fun p : FourierSpace m × ℝ =>
      (truncatedKernel j p.2 : ℂ) * (ψ p.1 - ψ (p.1 - p.2 • timeVector m))) := by
  apply Measurable.stronglyMeasurable
  exact (Complex.continuous_ofReal.measurable.comp
    ((measurable_truncatedKernel j).comp measurable_snd)).mul
      (ψ.continuous.measurable.comp measurable_fst |>.sub
        (ψ.continuous.measurable.comp
          (continuous_fst.sub ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
            (timeVector m)).continuous.comp continuous_snd)).measurable))

theorem norm_test_difference_le {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) (h : ℝ) :
    ‖ψ x - ψ (x - h • timeVector m)‖ ≤ 2 * SchwartzMap.seminorm ℝ 0 0 ψ := by
  calc
    _ ≤ ‖ψ x‖ + ‖ψ (x - h • timeVector m)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith [ψ.norm_le_seminorm ℝ x,
      ψ.norm_le_seminorm ℝ (x - h • timeVector m)]

theorem integrable_kernel_difference {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    Integrable (fun h : ℝ => (truncatedKernel j h : ℂ) *
      (ψ x - ψ (x - h • timeVector m))) volume := by
  have hi := (integrable_truncatedKernel j).smul_bdd (2 * SchwartzMap.seminorm ℝ 0 0 ψ)
    (f := fun h : ℝ => ψ x - ψ (x - h • timeVector m))
    ((continuous_const.sub (ψ.continuous.comp (continuous_const.sub
      (continuous_id.smul continuous_const)))).aestronglyMeasurable)
    (Eventually.of_forall (norm_test_difference_le ψ x))
  change Integrable (fun h : ℝ => truncatedKernel j h • (ψ x - ψ (x - h • timeVector m))) volume at hi
  exact hi

theorem stronglyMeasurable_physicalTruncation {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) : StronglyMeasurable (physicalTruncation j ψ) :=
  stronglyMeasurable_const.mul ((stronglyMeasurable_kernel_difference j ψ).integral_prod_right')

@[simp] theorem physicalTruncation_zero_index {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) : physicalTruncation 0 ψ x = 0 := by
  simp [physicalTruncation]

theorem physicalTruncation_add {m : ℕ} (j : ℕ) (ψ χ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) :
    physicalTruncation j (ψ + χ) x = physicalTruncation j ψ x + physicalTruncation j χ x := by
  simp only [physicalTruncation, add_apply]
  simp_rw [show ∀ a b c d k : ℂ, k * ((a + b) - (c + d)) = k * (a - c) + k * (b - d)
    from fun _ _ _ _ _ => by ring]
  rw [integral_add (integrable_kernel_difference j ψ x) (integrable_kernel_difference j χ x)]
  ring

theorem physicalTruncation_smul {m : ℕ} (j : ℕ) (c : ℂ)
    (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    physicalTruncation j (c • ψ) x = c * physicalTruncation j ψ x := by
  simp only [physicalTruncation, smul_apply, smul_eq_mul]
  simp_rw [show ∀ a b k : ℂ, k * (c * a - c * b) = c * (k * (a - b)) from
    fun _ _ _ => by ring]
  rw [integral_const_mul]
  ring

/-- The squared L² norm is the integral of the squared pointwise norm. -/
theorem integral_sq_norm_eq_norm_toLp_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp) hf]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [← one_div (2 : ℝ)]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]

private theorem integrable_kernel_difference_sq {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    Integrable (fun h : ℝ => truncatedKernel j h * ‖ψ x - ψ (x - h • timeVector m)‖ ^ 2)
      volume := by
  apply (integrable_truncatedKernel j).mul_bdd
    (c := (2 * SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2)
  · exact ((continuous_const.sub (ψ.continuous.comp (continuous_const.sub
      (continuous_id.smul continuous_const)))).norm.pow 2).aestronglyMeasurable
  · exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_test_difference_le ψ x h) 2

/-- Weighted Cauchy–Schwarz, without division by the possibly zero kernel mass. -/
theorem norm_integral_kernel_difference_sq_le {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    ‖∫ h : ℝ, (truncatedKernel j h : ℂ) * (ψ x - ψ (x - h • timeVector m))‖ ^ 2 ≤
      (∫ h, truncatedKernel j h) *
        ∫ h, truncatedKernel j h * ‖ψ x - ψ (x - h • timeVector m)‖ ^ 2 := by
  let d : ℝ → ℂ := fun h => ψ x - ψ (x - h • timeVector m)
  have hd : Continuous d := continuous_const.sub (ψ.continuous.comp
    (continuous_const.sub (continuous_id.smul continuous_const)))
  have hs : MemLp (fun h => Real.sqrt (truncatedKernel j h)) 2 volume := by
    apply (memLp_two_iff_integrable_sq (by
      exact (measurable_truncatedKernel j).sqrt.aestronglyMeasurable)).2
    simpa only [Real.sq_sqrt (truncatedKernel_nonneg j _)] using integrable_truncatedKernel j
  have ht : MemLp (fun h => Real.sqrt (truncatedKernel j h) * ‖d h‖) 2 volume := by
    apply (memLp_two_iff_integrable_sq (by
      exact ((measurable_truncatedKernel j).sqrt.mul hd.norm.measurable).aestronglyMeasurable)).2
    simpa only [mul_pow, Real.sq_sqrt (truncatedKernel_nonneg j _)] using
      integrable_kernel_difference_sq j ψ x
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hs) (by simpa using ht)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)), Real.rpow_two,
    mul_pow, Real.sq_sqrt (truncatedKernel_nonneg j _)] at hc
  simp_rw [← mul_assoc, Real.mul_self_sqrt (truncatedKernel_nonneg j _)] at hc
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hc
  have hn : ‖∫ h, (truncatedKernel j h : ℂ) * d h‖ ≤
      Real.sqrt (∫ h, truncatedKernel j h) *
        Real.sqrt (∫ h, truncatedKernel j h * ‖d h‖ ^ 2) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (truncatedKernel_nonneg j _)] using hc
  calc
    _ ≤ (Real.sqrt (∫ h, truncatedKernel j h) *
        Real.sqrt (∫ h, truncatedKernel j h * ‖d h‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_truncatedKernel_nonneg j),
        Real.sq_sqrt (integral_nonneg (fun h => mul_nonneg
          (truncatedKernel_nonneg j h) (sq_nonneg _)))]


theorem integral_sq_test_difference_le {m : ℕ} (h : ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, ‖ψ x - ψ (x - h • timeVector m)‖ ^ 2) ≤ (2 * ‖ψ.toLp 2 volume‖) ^ 2 := by
  change (∫ x, ‖(ψ - timeTranslate h ψ) x‖ ^ 2) ≤ _
  rw [integral_sq_norm_eq_norm_toLp_sq ((ψ - timeTranslate h ψ).memLp 2 volume)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_timeTranslate_toLp_le h ψ) 2

private theorem stronglyMeasurable_kernel_difference_sq {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable (fun p : FourierSpace m × ℝ =>
      truncatedKernel j p.2 * ‖ψ p.1 - ψ (p.1 - p.2 • timeVector m)‖ ^ 2) := by
  have hd : Continuous (fun p : FourierSpace m × ℝ =>
      ‖ψ p.1 - ψ (p.1 - p.2 • timeVector m)‖ ^ 2) :=
    ((ψ.continuous.comp continuous_fst).sub
      (ψ.continuous.comp (continuous_fst.sub (continuous_snd.smul continuous_const)))).norm.pow 2
  exact (((measurable_truncatedKernel j).comp measurable_snd).mul hd.measurable).stronglyMeasurable

/-- Absolute product integrability of the squared translated difference against the kernel. -/
theorem integrable_kernel_difference_sq_prod {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun p : FourierSpace m × ℝ =>
      truncatedKernel j p.2 * ‖ψ p.1 - ψ (p.1 - p.2 • timeVector m)‖ ^ 2)
      (volume.prod volume) := by
  have hm := stronglyMeasurable_kernel_difference_sq j ψ
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · apply Eventually.of_forall
    intro h
    simpa only [sub_apply, timeTranslate_apply] using
      (((ψ - timeTranslate h ψ).memLp 2 volume).norm.integrable_sq).const_mul (truncatedKernel j h)
  · apply ((integrable_truncatedKernel j).mul_const ((2 * ‖ψ.toLp 2 volume‖) ^ 2)).mono'
      hm.norm.integral_prod_left.aestronglyMeasurable
    apply Eventually.of_forall
    intro h
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (truncatedKernel_nonneg j _) (sq_nonneg _)),
      integral_const_mul]
    rw [abs_of_nonneg (mul_nonneg (truncatedKernel_nonneg j h)
      (integral_nonneg (fun x => sq_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (integral_sq_test_difference_le h ψ) (truncatedKernel_nonneg j h)

/-- Tonelli/Fubini and translation invariance give the global square majorant. -/
theorem integral_kernel_difference_sq_le {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, ∫ h, truncatedKernel j h * ‖ψ x - ψ (x - h • timeVector m)‖ ^ 2) ≤
      (∫ h, truncatedKernel j h) * (2 * ‖ψ.toLp 2 volume‖) ^ 2 := by
  rw [integral_integral_swap (integrable_kernel_difference_sq_prod j ψ)]
  simp_rw [integral_const_mul]
  rw [← integral_mul_const]
  apply integral_mono
  · simpa only [integral_const_mul] using
      (integrable_kernel_difference_sq_prod j ψ).integral_prod_right
  · exact (integrable_truncatedKernel j).mul_const _
  · exact fun h => mul_le_mul_of_nonneg_left (integral_sq_test_difference_le h ψ)
      (truncatedKernel_nonneg j h)

private theorem norm_physicalTruncation_sq_le {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    ‖physicalTruncation j ψ x‖ ^ 2 ≤
      kappa ^ 2 * (∫ h, truncatedKernel j h) *
        ∫ h, truncatedKernel j h * ‖ψ x - ψ (x - h • timeVector m)‖ ^ 2 := by
  rw [physicalTruncation, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos kappa_pos, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_integral_kernel_difference_sq_le j ψ x) (sq_nonneg _)

/-- Genuine L² membership of the physical integral, on possibly infinite Euclidean volume. -/
theorem memLp_physicalTruncation {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    MemLp (physicalTruncation j ψ) 2 (volume : Measure (FourierSpace m)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_physicalTruncation j ψ).aestronglyMeasurable).2
  apply ((integrable_kernel_difference_sq_prod j ψ).integral_prod_left.const_mul
    (kappa ^ 2 * ∫ h, truncatedKernel j h)).mono'
    ((stronglyMeasurable_physicalTruncation j ψ).norm.pow 2).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_physicalTruncation_sq_le j ψ x

/-- The L² class of the actual physical integral. -/
def physicalTruncationLp {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  (memLp_physicalTruncation j ψ).toLp (physicalTruncation j ψ)

theorem coeFn_physicalTruncationLp {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    physicalTruncationLp j ψ =ᵐ[volume] physicalTruncation j ψ :=
  (memLp_physicalTruncation j ψ).coeFn_toLp

/-- The finite-kernel L² bound, with no finite-volume assumption and no mass division. -/
theorem norm_physicalTruncationLp_le {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖physicalTruncationLp j ψ‖ ≤
      2 * kappa * (∫ h, ‖truncatedKernel j h‖) * ‖ψ.toLp 2 volume‖ := by
  have hs : ‖physicalTruncationLp j ψ‖ ^ 2 ≤
      kappa ^ 2 * (∫ h, truncatedKernel j h) ^ 2 * (2 * ‖ψ.toLp 2 volume‖) ^ 2 := by
    rw [physicalTruncationLp, ← integral_sq_norm_eq_norm_toLp_sq (memLp_physicalTruncation j ψ)]
    calc
      _ ≤ ∫ x, kappa ^ 2 * (∫ h, truncatedKernel j h) *
          ∫ h, truncatedKernel j h * ‖ψ x - ψ (x - h • timeVector m)‖ ^ 2 := by
        apply integral_mono
          ((memLp_two_iff_integrable_sq_norm
            (stronglyMeasurable_physicalTruncation j ψ).aestronglyMeasurable).1
              (memLp_physicalTruncation j ψ))
          ((integrable_kernel_difference_sq_prod j ψ).integral_prod_left.const_mul _)
        exact norm_physicalTruncation_sq_le j ψ
      _ ≤ _ := by
        rw [integral_const_mul]
        have := mul_le_mul_of_nonneg_left (integral_kernel_difference_sq_le j ψ)
          (mul_nonneg (sq_nonneg kappa) (integral_truncatedKernel_nonneg j))
        nlinarith [this]
  rw [← integral_truncatedKernel_eq_integral_norm]
  have hn := integral_truncatedKernel_nonneg j
  have hp := kappa_pos
  have hb : 0 ≤ 2 * kappa * (∫ h, truncatedKernel j h) * ‖ψ.toLp 2 volume‖ := by positivity
  nlinarith [sq_nonneg (‖physicalTruncationLp j ψ‖ -
    2 * kappa * (∫ h, truncatedKernel j h) * ‖ψ.toLp 2 volume‖)]

@[simp] theorem physicalTruncationLp_zero_index {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    physicalTruncationLp 0 ψ = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_physicalTruncationLp 0 ψ,
    Lp.coeFn_zero ℂ 2 (volume : Measure (FourierSpace m))] with x hx hz
  simp [hx]

theorem physicalTruncationLp_add {m : ℕ} (j : ℕ) (ψ χ : 𝓢(FourierSpace m, ℂ)) :
    physicalTruncationLp j (ψ + χ) = physicalTruncationLp j ψ + physicalTruncationLp j χ := by
  apply Lp.ext
  filter_upwards [coeFn_physicalTruncationLp j (ψ + χ), coeFn_physicalTruncationLp j ψ,
    coeFn_physicalTruncationLp j χ, Lp.coeFn_add (physicalTruncationLp j ψ)
      (physicalTruncationLp j χ)] with x ha hb hc hd
  simp only [ha, hd, Pi.add_apply, hb, hc, physicalTruncation_add]

theorem physicalTruncationLp_smul {m : ℕ} (j : ℕ) (c : ℂ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    physicalTruncationLp j (c • ψ) = c • physicalTruncationLp j ψ := by
  apply Lp.ext
  filter_upwards [coeFn_physicalTruncationLp j (c • ψ), coeFn_physicalTruncationLp j ψ,
    Lp.coeFn_smul c (physicalTruncationLp j ψ)] with x ha hb hc
  simp [ha, hc, hb, physicalTruncation_smul, smul_eq_mul]


end ParabolicRectifiability.HalfTimeDerivative
