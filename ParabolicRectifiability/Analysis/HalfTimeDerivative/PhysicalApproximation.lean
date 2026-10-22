import ParabolicRectifiability.Analysis.HalfTimeDerivative.TruncatedKernel

/-!
# Physical and spectral approximations

Fourier translation uses the negative phase for `x - h e_t`. The identification
of physical and spectral classes uses absolutely integrable Schwartz pairings.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology SchwartzMap FourierTransform ENNReal ComplexConjugate

namespace ParabolicRectifiability.HalfTimeDerivative
open FractionalKernel

local instance (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-- The phase of the physical translation `x - h e_t`, in the `2π` Fourier convention. -/
def timePhase {m : ℕ} (h : ℝ) (z : FourierSpace m) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (timeCoordinate m z : ℂ) * (h : ℂ))

theorem norm_timePhase {m : ℕ} (h : ℝ) (z : FourierSpace m) : ‖timePhase h z‖ = 1 := by
  simp [timePhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem fourier_timeTranslate {m : ℕ} (h : ℝ) (ψ : 𝓢(FourierSpace m, ℂ))
    (z : FourierSpace m) : (𝓕 (timeTranslate h ψ)) z = timePhase h z * (𝓕 ψ) z := by
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ (FourierSpace m)) (ψ : FourierSpace m → ℂ) (-(h • timeVector m))) z
  change (∫ x, Real.fourierChar (-inner ℝ x z) • ψ (x - h • timeVector m)) = _
  change (∫ x, Real.fourierChar (-inner ℝ x z) • ψ (x + -(h • timeVector m))) =
    Real.fourierChar (inner ℝ (-(h • timeVector m)) z) • (𝓕 ψ) z at ht
  simp_rw [sub_eq_add_neg]
  rw [ht, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  rw [inner_neg_left, real_inner_smul_left, real_inner_comm, inner_timeVector]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

theorem fourier_test_difference {m : ℕ} (h : ℝ) (ψ : 𝓢(FourierSpace m, ℂ))
    (z : FourierSpace m) :
    (𝓕 (ψ - timeTranslate h ψ)) z = (1 - timePhase h z) * (𝓕 ψ) z := by
  rw [show 𝓕 (ψ - timeTranslate h ψ) = 𝓕 ψ - 𝓕 (timeTranslate h ψ) from
    (FourierTransform.fourierCLM ℂ 𝓢(FourierSpace m, ℂ)).map_sub ψ (timeTranslate h ψ)]
  simp only [sub_apply, fourier_timeTranslate]
  ring

/-- Absolute convergence of the finite complex phase integral follows from the scalar theorem. -/
theorem integrable_kernel_phase {m : ℕ} (j : ℕ) (z : FourierSpace m) :
    Integrable (fun h => (truncatedKernel j h : ℂ) * (1 - timePhase h z)) volume := by
  have hi := (integrableOn_complexFrequencyIntegrand_symmetricAnnulus j (timeCoordinate m z)).integrable_indicator
    (measurableSet_symmetricAnnulus j)
  convert hi using 1
  funext h
  by_cases hh : h ∈ symmetricAnnulus j <;>
    simp [truncatedKernel, timePhase, complexFrequencyIntegrand, hh, mul_comm]

/-- The finite complex scalar identity, expressed using the actual physical kernel. -/
theorem integral_kernel_phase {m : ℕ} (j : ℕ) (z : FourierSpace m) :
    (kappa : ℂ) * (∫ h, (truncatedKernel j h : ℂ) * (1 - timePhase h z)) =
      (truncatedMultiplier j (timeCoordinate m z) : ℂ) := by
  rw [← kappa_mul_integral_complexFrequencyIntegrand_symmetricAnnulus j (timeCoordinate m z)]
  congr 1
  rw [← integral_indicator (measurableSet_symmetricAnnulus j)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  by_cases hh : h ∈ symmetricAnnulus j <;>
    simp [truncatedKernel, timePhase, complexFrequencyIntegrand, hh, mul_comm]

/-- Cauchy–Schwarz for actual Schwartz representatives in ordinary Euclidean volume. -/
theorem integral_norm_test_mul_le {m : ℕ} (ψ χ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, ‖ψ x‖ * ‖χ x‖) ≤ ‖ψ.toLp 2 volume‖ * ‖χ.toLp 2 volume‖ := by
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using ψ.memLp 2 volume) (by simpa using χ.memLp 2 volume)
  simpa only [SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat, Real.rpow_two, one_div] using hc

/-- Joint integrability follows from a uniform L² bound on a measurable family of Schwartz tests. -/
theorem integrable_kernel_test_pair_norm {m : ℕ} (j : ℕ)
    (u : ℝ → 𝓢(FourierSpace m, ℂ)) (χ : 𝓢(FourierSpace m, ℂ))
    (hu : StronglyMeasurable (fun p : ℝ × FourierSpace m => u p.1 p.2))
    (C : ℝ) (hC : ∀ h, ‖(u h).toLp 2 volume‖ ≤ C) :
    Integrable (fun p : ℝ × FourierSpace m =>
      truncatedKernel j p.1 * (‖u p.1 p.2‖ * ‖χ p.2‖)) (volume.prod volume) := by
  have hm : StronglyMeasurable (fun p : ℝ × FourierSpace m =>
      truncatedKernel j p.1 * (‖u p.1 p.2‖ * ‖χ p.2‖)) :=
    ((measurable_truncatedKernel j).comp measurable_fst).stronglyMeasurable.mul
      (hu.norm.mul (χ.continuous.comp continuous_snd).stronglyMeasurable.norm)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · apply Eventually.of_forall
    intro h
    exact ((u h).memLp 2 volume |>.norm.integrable_mul (χ.memLp 2 volume).norm).const_mul
      (truncatedKernel j h)
  · apply ((integrable_truncatedKernel j).mul_const (C * ‖χ.toLp 2 volume‖)).mono'
      hm.norm.integral_prod_right'.aestronglyMeasurable
    apply Eventually.of_forall
    intro h
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (truncatedKernel_nonneg j _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))), integral_const_mul]
    rw [abs_of_nonneg (mul_nonneg (truncatedKernel_nonneg j h)
      (integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))))]
    exact mul_le_mul_of_nonneg_left ((integral_norm_test_mul_le (u h) χ).trans
      (mul_le_mul_of_nonneg_right (hC h) (norm_nonneg _))) (truncatedKernel_nonneg j h)

/-- The absolute translated-pairing estimate used before Fubini; ambient volume may be infinite. -/
theorem integral_kernel_translated_pair_norm_le {m : ℕ} (j : ℕ)
    (ψ χ : 𝓢(FourierSpace m, ℂ)) :
    (∫ h, ‖truncatedKernel j h‖ * ∫ x, ‖ψ (x - h • timeVector m)‖ * ‖χ x‖) ≤
      (∫ h, ‖truncatedKernel j h‖) * ‖ψ.toLp 2 volume‖ * ‖χ.toLp 2 volume‖ := by
  have hu : StronglyMeasurable (fun p : ℝ × FourierSpace m => timeTranslate p.1 ψ p.2) :=
    (ψ.continuous.comp (continuous_snd.sub (continuous_fst.smul continuous_const))).stronglyMeasurable
  have hi := integrable_kernel_test_pair_norm j (fun h => timeTranslate h ψ) χ hu
    ‖ψ.toLp 2 volume‖ (fun h => (norm_timeTranslate_toLp h ψ).le)
  simp only [Real.norm_eq_abs, abs_of_nonneg (truncatedKernel_nonneg j _)]
  rw [mul_assoc, ← integral_mul_const]
  apply integral_mono
  · simpa only [timeTranslate_apply, integral_const_mul] using hi.integral_prod_left
  · exact (integrable_truncatedKernel j).mul_const _
  · intro h
    apply mul_le_mul_of_nonneg_left _ (truncatedKernel_nonneg j h)
    simpa only [timeTranslate_apply, norm_timeTranslate_toLp] using
      integral_norm_test_mul_le (timeTranslate h ψ) χ

private theorem integrable_kernel_test_pair {m : ℕ} (j : ℕ)
    (u : ℝ → 𝓢(FourierSpace m, ℂ)) (χ : 𝓢(FourierSpace m, ℂ))
    (hu : StronglyMeasurable (fun p : ℝ × FourierSpace m => u p.1 p.2))
    (C : ℝ) (hC : ∀ h, ‖(u h).toLp 2 volume‖ ≤ C) :
    Integrable (fun p : ℝ × FourierSpace m =>
      (truncatedKernel j p.1 : ℂ) * inner ℂ (χ p.2) (u p.1 p.2)) (volume.prod volume) := by
  apply (integrable_kernel_test_pair_norm j u χ hu C hC).mono'
  · exact (((Complex.continuous_ofReal.measurable.comp (measurable_truncatedKernel j)).comp
      measurable_fst).stronglyMeasurable.mul
        ((χ.continuous.comp continuous_snd).stronglyMeasurable.inner hu)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (truncatedKernel_nonneg j _)]
    apply mul_le_mul_of_nonneg_left _ (truncatedKernel_nonneg j _)
    simpa only [mul_comm] using norm_inner_le_norm (χ p.2) (u p.1 p.2)

private theorem measurable_test_difference {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable (fun p : ℝ × FourierSpace m => (ψ - timeTranslate p.1 ψ) p.2) :=
  ((ψ.continuous.comp continuous_snd).sub
    (ψ.continuous.comp (continuous_snd.sub (continuous_fst.smul continuous_const)))).stronglyMeasurable

private theorem measurable_fourier_test_difference {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable (fun p : ℝ × FourierSpace m => (𝓕 (ψ - timeTranslate p.1 ψ)) p.2) := by
  simp_rw [fourier_test_difference]
  apply Continuous.stronglyMeasurable
  unfold timePhase
  fun_prop

private theorem integral_inner_physicalTruncation {m : ℕ} (j : ℕ)
    (ψ χ : 𝓢(FourierSpace m, ℂ)) :
    (∫ x, inner ℂ (χ x) (physicalTruncation j ψ x)) =
      (kappa : ℂ) * ∫ h, (truncatedKernel j h : ℂ) *
        ∫ x, inner ℂ (χ x) ((ψ - timeTranslate h ψ) x) := by
  have hi := integrable_kernel_test_pair j (fun h => ψ - timeTranslate h ψ) χ
    (measurable_test_difference ψ) (2 * ‖ψ.toLp 2 volume‖)
      (fun h => norm_sub_timeTranslate_toLp_le h ψ)
  have heq (x : FourierSpace m) : inner ℂ (χ x) (physicalTruncation j ψ x) =
      (kappa : ℂ) * ∫ h, (truncatedKernel j h : ℂ) *
        inner ℂ (χ x) ((ψ - timeTranslate h ψ) x) := by
    rw [physicalTruncation, ← smul_eq_mul, inner_smul_right,
      ← integral_inner (integrable_kernel_difference j ψ x)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun h => by
      change inner ℂ (χ x) ((truncatedKernel j h : ℂ) •
        (ψ x - ψ (x - h • timeVector m))) = _
      rw [inner_smul_right]
      rfl
  simp_rw [heq]
  rw [integral_const_mul, integral_integral_swap (f := fun (x : FourierSpace m) (h : ℝ) =>
    (truncatedKernel j h : ℂ) * inner ℂ (χ x) ((ψ - timeTranslate h ψ) x)) hi.swap]
  simp_rw [integral_const_mul]

private theorem inner_toLp_eq_integral {m : ℕ} {f g : FourierSpace m → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℂ (f x) (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Parseval and absolutely integrable product pairings identify the two approximations. -/
theorem physicalTruncationLp_eq_spectralApproximation {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) : physicalTruncationLp j ψ = spectralApproximation j ψ := by
  have hp (χ : 𝓢(FourierSpace m, ℂ)) :
      inner ℂ (χ.toLp 2 volume) (physicalTruncationLp j ψ) =
        inner ℂ (χ.toLp 2 volume) (spectralApproximation j ψ) := by
    have hif := integrable_kernel_test_pair j (fun h => 𝓕 (ψ - timeTranslate h ψ)) (𝓕 χ)
      (measurable_fourier_test_difference ψ) (2 * ‖ψ.toLp 2 volume‖)
      (fun h => by simpa only [SchwartzMap.norm_fourier_toL2_eq] using
        norm_sub_timeTranslate_toLp_le h ψ)
    have hphase (z : FourierSpace m) :
        (kappa : ℂ) * ∫ h, (truncatedKernel j h : ℂ) *
          inner ℂ ((𝓕 χ) z) ((𝓕 (ψ - timeTranslate h ψ)) z) =
        inner ℂ ((𝓕 χ) z) ((truncatedMultiplier j (timeCoordinate m z) : ℂ) * (𝓕 ψ) z) := by
      simp_rw [fourier_test_difference, ← smul_eq_mul, inner_smul_right, smul_eq_mul]
      simp_rw [← mul_assoc]
      rw [integral_mul_const, ← mul_assoc, integral_kernel_phase]
    calc
      _ = ∫ x, inner ℂ (χ x) (physicalTruncation j ψ x) :=
        inner_toLp_eq_integral (χ.memLp 2 volume) (memLp_physicalTruncation j ψ)
      _ = (kappa : ℂ) * ∫ h, (truncatedKernel j h : ℂ) *
          ∫ x, inner ℂ (χ x) ((ψ - timeTranslate h ψ) x) :=
        integral_inner_physicalTruncation j ψ χ
      _ = (kappa : ℂ) * ∫ h, (truncatedKernel j h : ℂ) *
          ∫ z, inner ℂ ((𝓕 χ) z) ((𝓕 (ψ - timeTranslate h ψ)) z) := by
        simp only [SchwartzMap.integral_inner_fourier_fourier]
      _ = ∫ z, (kappa : ℂ) * ∫ h, (truncatedKernel j h : ℂ) *
          inner ℂ ((𝓕 χ) z) ((𝓕 (ψ - timeTranslate h ψ)) z) := by
        simp_rw [← integral_const_mul]
        rw [integral_integral_swap (hif.const_mul (kappa : ℂ))]
      _ = ∫ z, inner ℂ ((𝓕 χ) z)
          ((truncatedMultiplier j (timeCoordinate m z) : ℂ) * (𝓕 ψ) z) := by
        simp_rw [hphase]
      _ = inner ℂ ((𝓕 χ).toLp 2 volume) (truncatedWeightedLp j (𝓕 ψ)) :=
        (inner_toLp_eq_integral ((𝓕 χ).memLp 2 volume) (memLp_truncated_mul j (𝓕 ψ))).symm
      _ = _ := by
        rw [← fourier_spectralApproximation j ψ, ← SchwartzMap.toLp_fourier_eq]
        exact Lp.inner_fourier_eq _ _
  apply ext_inner_left ℂ
  intro v
  refine (SchwartzMap.denseRange_toLpCLM (E := FourierSpace m) (F := ℂ)
    (p := 2) (μ := volume) (by simp)).induction_on
      (p := fun v => inner ℂ v (physicalTruncationLp j ψ) = inner ℂ v (spectralApproximation j ψ))
      v ?_ hp
  exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)

/-- The Fourier image of the genuine physical L² class is the truncated weighted frequency class. -/
theorem fourier_physicalTruncationLp {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ)) :
    𝓕 (physicalTruncationLp j ψ) = truncatedWeightedLp j (𝓕 ψ) := by
  rw [physicalTruncationLp_eq_spectralApproximation, fourier_spectralApproximation]

/-- The physical classes converge in L² by their proved equality with the spectral classes. -/
theorem tendsto_physicalTruncationLp {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    Tendsto (fun j => physicalTruncationLp j ψ) atTop (𝓝 (halfTimeDeriv m ψ)) := by
  simp_rw [physicalTruncationLp_eq_spectralApproximation]
  exact tendsto_spectralApproximation ψ


/-- Real-valued complex tests have real physical truncations at every point. -/
theorem physicalTruncation_im_eq_zero {m : ℕ} (j : ℕ) (ψ : 𝓢(FourierSpace m, ℂ))
    (hψ : ∀ x, (ψ x).im = 0) (x : FourierSpace m) : (physicalTruncation j ψ x).im = 0 := by
  unfold physicalTruncation
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hi := integral_im (integrable_kernel_difference j ψ x)
  change (∫ h, ((truncatedKernel j h : ℂ) * (ψ x - ψ (x - h • timeVector m))).im) =
    (∫ h, (truncatedKernel j h : ℂ) * (ψ x - ψ (x - h • timeVector m))).im at hi
  rw [← hi]
  simp [Complex.mul_im, Complex.sub_im, hψ]

/-- Reality of the L² limit follows from an almost-everywhere convergent subsequence. -/
theorem halfTimeDeriv_ae_im_eq_zero {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hψ : ∀ x, (ψ x).im = 0) :
    ∀ᵐ x ∂(volume : Measure (FourierSpace m)), (halfTimeDeriv m ψ x).im = 0 := by
  obtain ⟨ns, _, hns⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (tendsto_physicalTruncationLp ψ)).exists_seq_tendsto_ae
  have hr : ∀ᵐ x ∂(volume : Measure (FourierSpace m)),
      ∀ j : ℕ, (physicalTruncationLp j ψ x).im = 0 := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [coeFn_physicalTruncationLp j ψ] with x hx
    rw [hx]
    exact physicalTruncation_im_eq_zero j ψ hψ x
  filter_upwards [hns, hr] with x hx hrx
  have ht := Complex.continuous_im.continuousAt.tendsto.comp hx
  have ht0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 ((halfTimeDeriv m ψ x).im)) := by
    convert ht using 1
    funext i
    exact (hrx (ns i)).symm
  exact tendsto_nhds_unique ht0 tendsto_const_nhds


end ParabolicRectifiability.HalfTimeDerivative
