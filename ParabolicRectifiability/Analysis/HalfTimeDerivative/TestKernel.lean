import ParabolicRectifiability.Analysis.HalfTimeDerivative.InverseRepresentative
import Mathlib.Analysis.Calculus.MeanValue

/-! # The pointwise half-time test kernel

The singular integral uses cancellation at zero and the normalization `kappa`.
Its equality with the L2 derivative is only an almost-everywhere equality.
-/

noncomputable section
open MeasureTheory Filter Set SchwartzMap FourierTransform
open scoped Topology SchwartzMap ContDiff

namespace ParabolicRectifiability.HalfTimeDerivative
open FractionalKernel

local instance (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-- The full time-kernel integrand, with the physical shift `x - h e_t`. -/
def testKernelIntegrand {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) (h : ℝ) : ℂ :=
  ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (ψ x - ψ (x - h • timeVector m))

@[simp] theorem testKernelIntegrand_zero {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) : testKernelIntegrand ψ x 0 = 0 := by
  simp [testKernelIntegrand]

/-- An integrable scalar weight displaying both cancellation and decay. -/
def cancellationWeight (h : ℝ) : ℝ :=
  if |h| ≤ 1 then |h| ^ (-1 / 2 : ℝ) else |h| ^ (-3 / 2 : ℝ)

theorem measurable_cancellationWeight : Measurable cancellationWeight := by
  unfold cancellationWeight
  exact Measurable.ite (measurableSet_le measurable_abs measurable_const)
    (measurable_abs.pow_const _) (measurable_abs.pow_const _)

theorem cancellationWeight_nonneg (h : ℝ) : 0 ≤ cancellationWeight h := by
  unfold cancellationWeight
  split_ifs <;> positivity

private theorem integrable_of_even_pos {f : ℝ → ℝ} (he : ∀ h, f (-h) = f h)
    (hf : IntegrableOn f (Ioi 0) volume) : Integrable f volume := by
  have hn : IntegrableOn f (Iic 0) volume := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let e : MeasurableEmbedding (fun h : ℝ => -h) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    simpa only [Function.comp_def, he, neg_preimage, neg_Iic, neg_zero] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf)
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hf

theorem integrable_cancellationWeight : Integrable cancellationWeight volume := by
  apply integrable_of_even_pos (fun h => by simp [cancellationWeight])
  have hn : IntegrableOn cancellationWeight (Ioc (0 : ℝ) 1) volume := by
    apply ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1 / 2)
      (a := 0) (b := 1)).1).congr_fun (fun h hh => ?_) measurableSet_Ioc
    simp [cancellationWeight, abs_of_pos hh.1, hh.2]
  have ht : IntegrableOn cancellationWeight (Ioi (1 : ℝ)) volume := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).congr_fun (fun h hh => ?_) measurableSet_Ioi
    change 1 < h at hh
    simp [cancellationWeight, abs_of_pos (lt_trans zero_lt_one hh), not_le.mpr hh]
  apply (hn.union ht).mono_set
  intro h hh
  by_cases hle : h ≤ 1
  · exact Or.inl ⟨hh, hle⟩
  · exact Or.inr (lt_of_not_ge hle)

/-- A finite seminorm control for the full kernel. -/
def testKernelControl {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖ + 2 * SchwartzMap.seminorm ℝ 0 0 ψ

theorem testKernelControl_nonneg {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    0 ≤ testKernelControl ψ := by unfold testKernelControl; positivity

/-- First-order cancellation suffices for absolute convergence at zero. -/
theorem norm_test_difference_le_time {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) (h : ℝ) :
    ‖ψ x - ψ (x - h • timeVector m)‖ ≤
      (SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) * |h| := by
  have hb : ∀ y ∈ (univ : Set (FourierSpace m)),
      ‖fderiv ℝ ψ y‖ ≤ SchwartzMap.seminorm ℝ 0 1 ψ := by
    intro y _
    simpa only [norm_iteratedFDeriv_one] using ψ.norm_iteratedFDeriv_le_seminorm ℝ 1 y
  have hd := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y (_ : y ∈ (univ : Set (FourierSpace m))) => ψ.differentiableAt (x := y)) hb
    convex_univ (mem_univ (x - h • timeVector m)) (mem_univ x)
  simpa only [sub_sub_cancel, norm_smul, Real.norm_eq_abs, mul_comm |h|, mul_assoc] using hd

theorem stronglyMeasurable_testKernelIntegrand {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable (fun p : FourierSpace m × ℝ => testKernelIntegrand ψ p.1 p.2) := by
  unfold testKernelIntegrand
  apply Measurable.stronglyMeasurable
  exact (Complex.measurable_ofReal.comp (measurable_snd.abs.pow_const _)).mul
    ((ψ.continuous.measurable.comp measurable_fst).sub
      (ψ.continuous.measurable.comp
        (continuous_fst.sub (continuous_snd.smul continuous_const)).measurable))

theorem norm_testKernelIntegrand_le {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) (h : ℝ) :
    ‖testKernelIntegrand ψ x h‖ ≤ testKernelControl ψ * cancellationWeight h := by
  have hp : |h| ^ (-3 / 2 : ℝ) * |h| = |h| ^ (-1 / 2 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one |h|]
    rw [← Real.rpow_add' (abs_nonneg h) (by norm_num : (-3 / 2 : ℝ) + 1 ≠ 0)]
    norm_num
  rw [testKernelIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
  unfold cancellationWeight
  split_ifs with hh
  · calc
      _ ≤ |h| ^ (-3 / 2 : ℝ) *
          ((SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) * |h|) :=
        mul_le_mul_of_nonneg_left (norm_test_difference_le_time ψ x h) (by positivity)
      _ = (SchwartzMap.seminorm ℝ 0 1 ψ * ‖timeVector m‖) * |h| ^ (-1 / 2 : ℝ) := by
        rw [mul_left_comm, hp]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold testKernelControl; exact le_add_of_nonneg_right (by positivity)) (by positivity)
  · apply (mul_le_mul_of_nonneg_left (norm_test_difference_le ψ x h) (by positivity)).trans
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by unfold testKernelControl; exact le_add_of_nonneg_left (by positivity)) (by positivity)

theorem integrable_testKernelIntegrand {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) : Integrable (testKernelIntegrand ψ x) volume := by
  apply (integrable_cancellationWeight.const_mul (testKernelControl ψ)).mono'
    (((stronglyMeasurable_testKernelIntegrand ψ).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall (norm_testKernelIntegrand_le ψ x)

/-- The normalized, everywhere absolutely convergent test kernel. -/
def testKernel {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) : ℂ :=
  (kappa : ℂ) * ∫ h, testKernelIntegrand ψ x h

theorem stronglyMeasurable_testKernel {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    StronglyMeasurable (testKernel ψ) :=
  stronglyMeasurable_const.mul (stronglyMeasurable_testKernelIntegrand ψ).integral_prod_right'

theorem norm_testKernel_le {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    ‖testKernel ψ x‖ ≤ kappa * testKernelControl ψ * ∫ h, cancellationWeight h := by
  rw [testKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos kappa_pos, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ kappa_pos.le
  rw [← integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_testKernelIntegrand ψ x).norm
      (integrable_cancellationWeight.const_mul _) (norm_testKernelIntegrand_le ψ x))

theorem physicalTruncation_eq_setIntegral {m : ℕ} (j : ℕ)
    (ψ : 𝓢(FourierSpace m, ℂ)) (x : FourierSpace m) :
    physicalTruncation j ψ x = (kappa : ℂ) * ∫ h in symmetricAnnulus j, testKernelIntegrand ψ x h := by
  rw [physicalTruncation, ← integral_indicator (measurableSet_symmetricAnnulus j)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun h => by
    by_cases hh : h ∈ symmetricAnnulus j <;> simp [truncatedKernel, testKernelIntegrand, hh]

/-- The physical cutoffs converge at every point to the absolutely convergent kernel. -/
theorem tendsto_physicalTruncation_testKernel {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) : Tendsto (fun j => physicalTruncation j ψ x) atTop (𝓝 (testKernel ψ x)) := by
  have ht := tendsto_setIntegral_of_monotone measurableSet_symmetricAnnulus
    monotone_symmetricAnnulus (integrable_testKernelIntegrand ψ x).integrableOn
  have hi : (∫ h in ⋃ j, symmetricAnnulus j, testKernelIntegrand ψ x h) =
      ∫ h, testKernelIntegrand ψ x h := by
    rw [← integral_indicator (MeasurableSet.iUnion measurableSet_symmetricAnnulus)]
    apply integral_congr_ae
    exact Eventually.of_forall fun h => by
      rw [iUnion_symmetricAnnulus]
      by_cases hh : h = 0 <;> simp [hh]
  rw [hi] at ht
  simpa only [physicalTruncation_eq_setIntegral, testKernel] using ht.const_mul (kappa : ℂ)

/-- Equality with the L2 representative is asserted only almost everywhere. -/
theorem testKernel_ae_halfTimeDeriv {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    testKernel ψ =ᵐ[volume] (halfTimeDeriv m ψ : FourierSpace m → ℂ) := by
  obtain ⟨ns, hmono, hns⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (tendsto_physicalTruncationLp ψ)).exists_seq_tendsto_ae
  have he := ae_all_iff.mpr (fun j => coeFn_physicalTruncationLp j ψ)
  filter_upwards [hns, he] with x hx hex
  have ht := (tendsto_physicalTruncation_testKernel ψ x).comp hmono.tendsto_atTop
  have hx' : Tendsto (fun i => physicalTruncation (ns i) ψ x) atTop
      (𝓝 (halfTimeDeriv m ψ x)) := by simpa only [hex] using hx
  exact tendsto_nhds_unique ht hx'

theorem memLp_testKernel {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    MemLp (testKernel ψ) 2 volume :=
  (Lp.memLp _).ae_eq (testKernel_ae_halfTimeDeriv ψ).symm

theorem testKernel_im_eq_zero {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hψ : ∀ x, (ψ x).im = 0) (x : FourierSpace m) : (testKernel ψ x).im = 0 := by
  unfold testKernel
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hi := integral_im (integrable_testKernelIntegrand ψ x)
  change (∫ h, (testKernelIntegrand ψ x h).im) = (∫ h, testKernelIntegrand ψ x h).im at hi
  rw [← hi]
  simp [testKernelIntegrand, Complex.mul_im, Complex.sub_im, hψ]

/-- Coordinate transport of the negative time shift. -/
theorem timeShift_toLp {m : ℕ} (u : Spatial m) (t h : ℝ) :
    WithLp.toLp 2 (u, t) - h • timeVector m = WithLp.toLp 2 (u, t - h) := by
  apply WithLp.ofLp_injective 2
  exact coordinates_sub_timeVector (WithLp.toLp 2 (u, t)) h

/-- The spatial projection of the test's topological support. -/
def spatialTestSupport {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) : Set (Spatial m) :=
  (fun x => (WithLp.ofLp x).1) '' tsupport ψ

theorem isCompact_spatialTestSupport {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) : IsCompact (spatialTestSupport ψ) :=
  hc.image (fourierCoordinatesHomeomorph m).continuous.fst

theorem testKernel_eq_zero_of_notMem_spatialTestSupport {m : ℕ}
    (ψ : 𝓢(FourierSpace m, ℂ)) {u : Spatial m} (hu : u ∉ spatialTestSupport ψ) (t : ℝ) :
    testKernel ψ (WithLp.toLp 2 (u, t)) = 0 := by
  have hz (s : ℝ) : ψ (WithLp.toLp 2 (u, s)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hu ⟨WithLp.toLp 2 (u, s), hs, rfl⟩
  simp [testKernel, testKernelIntegrand, timeShift_toLp, hz]

private theorem test_eq_zero_of_time_support {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    {S : ℝ} (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S)
    {x : FourierSpace m} (hx : S < |timeCoordinate m x|) : ψ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => (not_le.mpr hx) (hs x h))

/-- A fixed finite constant for the temporal tail, chosen before the spatial and time points. -/
def testTailConstant {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) (S : ℝ) : ℝ :=
  kappa * SchwartzMap.seminorm ℝ 0 0 ψ * (2 * S) / (2 : ℝ) ^ (-3 / 2 : ℝ)

theorem testTailConstant_nonneg {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    {S : ℝ} (hS : 0 ≤ S) : 0 ≤ testTailConstant ψ S := by
  unfold testTailConstant
  have := kappa_pos
  positivity

/-- Compact time support gives the exact `|t| > 2 S` tail range. -/
theorem norm_testKernel_temporal_tail {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    {S : ℝ} (hS : 0 < S) (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S)
    (u : Spatial m) {t : ℝ} (ht : 2 * S < |t|) :
    ‖testKernel ψ (WithLp.toLp 2 (u, t))‖ ≤ testTailConstant ψ S * |t| ^ (-3 / 2 : ℝ) := by
  let x : FourierSpace m := WithLp.toLp 2 (u, t)
  have hx : ψ x = 0 := test_eq_zero_of_time_support ψ hs (by
    change S < |t|
    linarith)
  have hi : (∫ h, testKernelIntegrand ψ x h) =
      ∫ h in Icc (t - S) (t + S), testKernelIntegrand ψ x h := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro h
    by_cases hh : h ∈ Icc (t - S) (t + S)
    · simp [hh]
    · have hn : S < |t - h| := by
        by_contra hn
        have he := abs_le.mp (le_of_not_gt hn)
        exact hh ⟨by linarith [he.2], by linarith [he.1]⟩
      have hz : ψ (x - h • timeVector m) = 0 :=
        test_eq_zero_of_time_support ψ hs (by
          rw [timeCoordinate_sub_timeVector]
          exact hn)
      simp [hh, testKernelIntegrand, hx, hz]
  have hb : ‖∫ h in Icc (t - S) (t + S), testKernelIntegrand ψ x h‖ ≤
      ((|t| / 2) ^ (-3 / 2 : ℝ) * SchwartzMap.seminorm ℝ 0 0 ψ) * (2 * S) := by
    have H := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (f := testKernelIntegrand ψ x) (s := Icc (t - S) (t + S))
      (C := (|t| / 2) ^ (-3 / 2 : ℝ) * SchwartzMap.seminorm ℝ 0 0 ψ)
      isCompact_Icc.measure_lt_top (fun h hh => ?_)
    · have hv : volume.real (Icc (t - S) (t + S)) = 2 * S := by
        rw [Real.volume_real_Icc, max_eq_left (by linarith)]
        ring
      simpa only [hv] using H
    have hth : |t - h| ≤ S := abs_le.mpr ⟨by linarith [hh.2], by linarith [hh.1]⟩
    have htri : |t| ≤ |t - h| + |h| := by simpa using abs_add_le (t - h) h
    have hhhalf : |t| / 2 ≤ |h| := by linarith
    have hpow := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < |t| / 2) hhhalf
      (by norm_num : (-3 / 2 : ℝ) ≤ 0)
    simp only [testKernelIntegrand, hx, zero_sub, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
    exact mul_le_mul hpow (ψ.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)
  calc
    ‖testKernel ψ x‖ = kappa * ‖∫ h in Icc (t - S) (t + S), testKernelIntegrand ψ x h‖ := by
      rw [testKernel, hi, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos kappa_pos]
    _ ≤ kappa * (((|t| / 2) ^ (-3 / 2 : ℝ) * SchwartzMap.seminorm ℝ 0 0 ψ) * (2 * S)) :=
      mul_le_mul_of_nonneg_left hb kappa_pos.le
    _ = _ := by rw [Real.div_rpow (abs_nonneg t) (by norm_num)]; unfold testTailConstant; ring

/-- A bounded central interval joined to an integrable power tail. -/
def temporalWeight (R t : ℝ) : ℝ := if |t| ≤ R then 1 else |t| ^ (-3 / 2 : ℝ)

theorem measurable_temporalWeight (R : ℝ) : Measurable (temporalWeight R) := by
  unfold temporalWeight
  exact Measurable.ite (measurableSet_le measurable_abs measurable_const)
    measurable_const (measurable_abs.pow_const _)

theorem temporalWeight_nonneg (R t : ℝ) : 0 ≤ temporalWeight R t := by
  unfold temporalWeight
  split_ifs <;> positivity

theorem integrable_temporalWeight {R : ℝ} (hR : 0 < R) : Integrable (temporalWeight R) volume := by
  apply integrable_of_even_pos (fun h => by simp [temporalWeight])
  have hn : IntegrableOn (temporalWeight R) (Ioc (0 : ℝ) R) volume := by
    apply (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    simp [temporalWeight, abs_of_pos ht.1, ht.2]
  have ht : IntegrableOn (temporalWeight R) (Ioi R) volume := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hR).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    change R < t at ht
    simp [temporalWeight, abs_of_pos (hR.trans ht), not_le.mpr ht]
  apply (hn.union ht).mono_set
  intro t ht
  by_cases hle : t ≤ R
  · exact Or.inl ⟨ht, hle⟩
  · exact Or.inr (lt_of_not_ge hle)

/-- Uniform domination, retaining a finite constant chosen before both coordinates. -/
theorem exists_temporal_majorant {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    {S : ℝ} (hS : 0 < S) (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Spatial m, ∀ t : ℝ,
      ‖testKernel ψ (WithLp.toLp 2 (u, t))‖ ≤ C * temporalWeight (2 * S) t := by
  let B := kappa * testKernelControl ψ * ∫ h, cancellationWeight h
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg kappa_pos.le (testKernelControl_nonneg ψ))
    (integral_nonneg cancellationWeight_nonneg)
  have hC := testTailConstant_nonneg ψ hS.le
  refine ⟨B + testTailConstant ψ S, add_nonneg hB hC, ?_⟩
  intro u t
  unfold temporalWeight
  split_ifs with ht
  · simpa only [mul_one] using (norm_testKernel_le ψ _).trans (le_add_of_nonneg_right hC)
  · exact (norm_testKernel_temporal_tail ψ hS hs u (lt_of_not_ge ht)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (by positivity))

/-- Every time fiber has an absolutely integrable kernel, including its two tails. -/
theorem integrable_testKernel_time {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    {S : ℝ} (hS : 0 < S) (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S)
    (u : Spatial m) : Integrable (fun t : ℝ => testKernel ψ (WithLp.toLp 2 (u, t))) volume := by
  obtain ⟨C, _, hC⟩ := exists_temporal_majorant ψ hS hs
  apply ((integrable_temporalWeight (by positivity : 0 < 2 * S)).const_mul C).mono'
  · exact ((stronglyMeasurable_testKernel ψ).comp_measurable
      ((fourierCoordinatesMeasurableEquiv m).symm.measurable.comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · exact Eventually.of_forall (hC u)

/-- Absolute product integrability supplies Fubini on ordinary spatial and time volume. -/
theorem integrable_testKernel_coordinates {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) {S : ℝ} (hS : 0 < S)
    (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S) :
    Integrable (fun p : Coordinates m => testKernel ψ (WithLp.toLp 2 p))
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exists_temporal_majorant ψ hS hs
  have hA := isCompact_spatialTestSupport ψ hc
  have hi : Integrable ((spatialTestSupport ψ).indicator (fun _ : Spatial m => C)) volume :=
    (integrableOn_const hA.measure_ne_top).integrable_indicator hA.measurableSet
  apply (hi.mul_prod (integrable_temporalWeight (by positivity : 0 < 2 * S))).mono'
    (((stronglyMeasurable_testKernel ψ).comp_measurable
      (fourierCoordinatesMeasurableEquiv m).symm.measurable).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  by_cases hp : p.1 ∈ spatialTestSupport ψ
  · simpa [hp] using hb p.1 p.2
  · simp [hp, testKernel_eq_zero_of_notMem_spatialTestSupport ψ hp]

/-- Compact tests have a globally integrable pointwise derivative. -/
theorem integrable_testKernel {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) {S : ℝ} (hS : 0 < S)
    (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S) :
    Integrable (testKernel ψ) volume := by
  rw [← integrable_fourierCoordinates_symm_iff]
  rw [volume_coordinates_eq_prod]
  exact integrable_testKernel_coordinates ψ hc hS hs

/-- The time and space integrals can be interchanged after the proved L1 estimate. -/
theorem integral_testKernel_fubini {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) {S : ℝ} (hS : 0 < S)
    (hs : ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S) :
    (∫ u : Spatial m, ∫ t : ℝ, testKernel ψ (WithLp.toLp 2 (u, t))) =
      ∫ t : ℝ, ∫ u : Spatial m, testKernel ψ (WithLp.toLp 2 (u, t)) :=
  integral_integral_swap (integrable_testKernel_coordinates ψ hc hS hs)

/-- The actual pointwise formula gives the bilinear distribution pairing. -/
theorem testKernel_pairing {m : ℕ} {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun x => (H x : ℂ) * testKernel ψ x) volume ∧
    (∫ x, (H x : ℂ) * testKernel ψ x) = halfTimeFunctional (realLp hH) ψ := by
  refine ⟨hH.ofReal.integrable_mul (memLp_testKernel ψ), ?_⟩
  rw [halfTimeFunctional_real_apply]
  exact integral_congr_ae ((Filter.EventuallyEq.refl _ _).mul (testKernel_ae_halfTimeDeriv ψ))

@[simp] theorem testKernel_zero (m : ℕ) (x : FourierSpace m) :
    testKernel (0 : 𝓢(FourierSpace m, ℂ)) x = 0 := by
  simp [testKernel, testKernelIntegrand]

/-- The pointwise integral respects complex scalar multiplication. -/
theorem testKernel_smul {m : ℕ} (c : ℂ) (ψ : 𝓢(FourierSpace m, ℂ))
    (x : FourierSpace m) : testKernel (c • ψ) x = c * testKernel ψ x := by
  have he : testKernelIntegrand (c • ψ) x = fun h => c * testKernelIntegrand ψ x h := by
    funext h
    simp only [testKernelIntegrand, smul_apply, smul_eq_mul]
    ring
  rw [testKernel, he, integral_const_mul, testKernel]
  ring

/-- Every compact test admits a positive, finite time-support bound. -/
theorem exists_time_support_bound {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) : ∃ S > 0, ∀ x ∈ tsupport ψ, |timeCoordinate m x| ≤ S := by
  obtain ⟨S, hS, hb⟩ := (hc.image (timeCoordinate m).continuous).isBounded.exists_pos_norm_le
  exact ⟨S, hS, fun x hx => by simpa only [Real.norm_eq_abs] using hb _ ⟨x, hx, rfl⟩⟩

/-- Boundedness on the central strip and integrable temporal tails give full L1 membership. -/
theorem integrable_testKernel_of_hasCompactSupport {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) : Integrable (testKernel ψ) volume := by
  obtain ⟨S, hS, hs⟩ := exists_time_support_bound ψ hc
  exact integrable_testKernel ψ hc hS hs

/-- Compact-test kernels pair absolutely with bounded measurable data, without finite ambient volume. -/
theorem integrable_bounded_mul_testKernel {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ))
    (hc : HasCompactSupport ψ) {H : FourierSpace m → ℂ} {B : ℝ}
    (hH : AEStronglyMeasurable H volume) (hb : ∀ᵐ x ∂volume, ‖H x‖ ≤ B) :
    Integrable (fun x => H x * testKernel ψ x) volume :=
  (integrable_testKernel_of_hasCompactSupport ψ hc).bdd_mul hH hb

/-- The real compact-test embedding preserves support and gives a real, integrable kernel. -/
theorem realCompactTest_kernel {m : ℕ} (φ : FourierSpace m → ℝ)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (testKernel (realCompactTest φ hs hc)) volume ∧
    ∀ x, (testKernel (realCompactTest φ hs hc) x).im = 0 := by
  refine ⟨integrable_testKernel_of_hasCompactSupport _ ?_,
    testKernel_im_eq_zero _ (fun x => by simp)⟩
  change IsCompact (tsupport (realCompactTest φ hs hc))
  rw [tsupport_realCompactTest]
  exact hc

end ParabolicRectifiability.HalfTimeDerivative
