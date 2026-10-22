import ParabolicRectifiability.Analysis.FourierAffine.Pointwise
import ParabolicRectifiability.Analysis.FourierAffine.Symbol
import ParabolicRectifiability.Analysis.HalfTimeDerivative.InverseRepresentative
import ParabolicRectifiability.Measure.ScaleEnergy
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # The Fourier-affine square-integral bound

For every real `f ∈ L²(ℝ^m × ℝ)`,
`∫ |τ| |f̂(ξ,τ)|² ≤ C_m ∫_V ∫_0^∞ a_f(p,r)² dr/r dp` in `ℝ≥0∞`.

Plancherel for `ψ_r ⋆ f` is proved for `f ∈ L²` only: the smoothed function is
identified with the inverse L² Fourier transform of `ψ̂_r · f̂` by testing against
compactly supported smooth functions. The test computation uses the
bilinear L² pairing, the Schwartz convolution theorem for the two Schwartz tests,
and Fubini for a compactly supported test against the locally integrable `f`.
No L¹·L¹ convolution theorem is applied to `f`. Tonelli then integrates the
symbol lower bound and the pointwise affine bound. All integrals are extended
nonnegative, so no derivative integrability is assumed. If the right side is
finite, the inverse construction of `HalfTimeDerivative` supplies a real L² representative of
`D_t^{1/2} f` with `∫ g² ≤ C_m · E(f)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology FourierTransform ContDiff SchwartzMap Convolution

namespace ParabolicRectifiability.FourierAffine

open HalfTimeDerivative FourierTransform

variable {m : ℕ}

attribute [local instance] continuousSMul_fourierSpace

/-- The affine Carleson energy `E(f) = ∫_V ∫_0^∞ a_f(p,r)² dr/r dp`. -/
def affineCarlesonEnergy (f : FourierSpace m → ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ r, affineEnergy f p r ∂scaleMeasure

/-! ### Auxiliary facts -/

theorem lintegral_enorm_sq_eq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {g : α → E} (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = eLpNorm g 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hg,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem enorm_complex_ofReal (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

theorem scaleKernelHat_neg (r : ℝ) (ζ : FourierSpace m) :
    scaleKernelHat r (-ζ) = scaleKernelHat r ζ := by
  rw [scaleKernelHat, ← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg]
  simp only [scaleKernel_neg]

/-- The Schwartz test carrying `ψ_r`. -/
def scaleKernelTest (r : ℝ) : 𝓢(FourierSpace m, ℂ) :=
  realCompactTest (scaleKernel r) (contDiff_scaleKernel r) (hasCompactSupport_scaleKernel r)

theorem fourier_scaleKernelTest (r : ℝ) :
    ⇑(𝓕 (scaleKernelTest (m := m) r) : 𝓢(FourierSpace m, ℂ)) = scaleKernelHat r :=
  SchwartzMap.fourier_coe _

theorem continuous_scaleKernelHat (r : ℝ) : Continuous (scaleKernelHat (m := m) r) := by
  rw [← fourier_scaleKernelTest]
  exact (𝓕 (scaleKernelTest r) : 𝓢(FourierSpace m, ℂ)).continuous

theorem smoothing_eq_convolution (r : ℝ) (f : FourierSpace m → ℝ) (p : FourierSpace m) :
    smoothing r f p = (scaleKernel r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) p := by
  rw [convolution_eq_swap]
  rfl

theorem continuous_smoothing (r : ℝ) {f : FourierSpace m → ℝ} (hf : LocallyIntegrable f volume) :
    Continuous (smoothing r f) := by
  have h := (hasCompactSupport_scaleKernel (m := m) r).continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (continuous_scaleKernel r) hf
  convert h using 1
  funext p
  exact smoothing_eq_convolution r f p

theorem measurable_scaleKernel₂ :
    Measurable fun x : ℝ × FourierSpace m => scaleKernel x.1 x.2 := by
  have hd : Measurable fun x : ℝ × FourierSpace m => dilate x.1⁻¹ x.2 :=
    continuous_dilate₂.measurable.comp ((measurable_fst.inv).prodMk measurable_snd)
  exact ((measurable_fst.pow_const _).inv).mul (contDiff_scaleKernelOne.continuous.measurable.comp hd)

/-! ### Plancherel for the smoothed function -/

/-- Testing identity: `ψ_r ⋆ f` pairs with a compact smooth test like `ψ̂_r f̂` with its
inverse-transformed test. Fubini uses only local integrability of `f`. -/
theorem integral_test_smoothing {r : ℝ} {f : FourierSpace m → ℝ} (hf : MemLp f 2 volume)
    (g : FourierSpace m → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, (g x : ℂ) * (smoothing r f x : ℂ) =
      ∫ ζ, (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
        (scaleKernelHat r ζ * (𝓕⁻ (realCompactTest g hg hgc)) ζ) := by
  obtain ⟨S, hSdef⟩ : ∃ S : 𝓢(FourierSpace m, ℂ), S = SchwartzMap.convolution
      (ContinuousLinearMap.mul ℂ ℂ) (scaleKernelTest r) (realCompactTest g hg hgc) := ⟨_, rfl⟩
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  -- `S q = ∫ ψ_r(x - q) g(x) dx`.
  have hS : ∀ q, S q = ∫ x, (scaleKernel r (x - q) : ℂ) * (g x : ℂ) := by
    intro q
    have hs := integral_sub_left_eq_self (μ := volume)
      (fun t => (scaleKernel r t : ℂ) * (g (q - t) : ℂ)) q
    simp only [sub_sub_cancel] at hs
    rw [hSdef, SchwartzMap.convolution_apply, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', scaleKernelTest, realCompactTest_apply]
    rw [← hs]
    congr 1
    funext x
    rw [← neg_sub x q, scaleKernel_neg]
  -- Fubini for a compact test against the locally integrable `f`.
  obtain ⟨Rg, hRg⟩ : ∃ R, ∀ x, R < ‖x‖ → g x = 0 := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
    have := hR hmem
    rw [mem_closedBall_zero_iff] at this
    linarith
  obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨Mψ, hMψ⟩ := (continuous_scaleKernel (m := m) r).bounded_above_of_compact_support
    (hasCompactSupport_scaleKernel r)
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ 0)
  have hfK : Integrable ((closedBall (0 : FourierSpace m) (Rg + (|r| + r ^ 2))).indicator
      fun q => ‖f q‖) volume :=
    IntegrableOn.integrable_indicator
      (hfl.integrableOn_isCompact (isCompact_closedBall (0 : FourierSpace m) _)).norm
      measurableSet_closedBall
  have hgK : Integrable ((closedBall (0 : FourierSpace m) Rg).indicator fun _ => Mg * Mψ)
      volume :=
    (integrableOn_const (MeasureTheory.measure_closedBall_lt_top
      (μ := (volume : Measure (FourierSpace m))) (x := (0 : FourierSpace m)) (r := Rg)).ne).integrable_indicator
      measurableSet_closedBall
  have hint : Integrable (Function.uncurry fun x q =>
      (g x : ℂ) * ((scaleKernel r (x - q) : ℂ) * (f q : ℂ))) (volume.prod volume) := by
    refine (hgK.mul_prod hfK).mono' ?_ (Eventually.of_forall fun xq => ?_)
    · exact (Complex.continuous_ofReal.comp (hg.continuous.comp continuous_fst)).aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.comp ((continuous_scaleKernel r).comp
          (continuous_fst.sub continuous_snd))).aestronglyMeasurable.mul
          (Complex.continuous_ofReal.comp_aestronglyMeasurable
            (hfl.aestronglyMeasurable.comp_snd)))
    · obtain ⟨x, q⟩ := xq
      have hb1 : 0 ≤ (closedBall (0 : FourierSpace m) Rg).indicator (fun _ => Mg * Mψ) x :=
        indicator_nonneg (fun _ _ => mul_nonneg hMg0 hMψ0) _
      have hb2 : 0 ≤ (closedBall (0 : FourierSpace m) (Rg + (|r| + r ^ 2))).indicator
          (fun q => ‖f q‖) q := indicator_nonneg (fun _ _ => norm_nonneg _) _
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real]
      by_cases hx : ‖x‖ ≤ Rg
      · by_cases hq : ‖q‖ ≤ Rg + (|r| + r ^ 2)
        · rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hx),
            indicator_of_mem (mem_closedBall_zero_iff.mpr hq)]
          calc ‖g x‖ * (‖scaleKernel r (x - q)‖ * ‖f q‖)
              = (‖g x‖ * ‖scaleKernel r (x - q)‖) * ‖f q‖ := by ring
            _ ≤ (Mg * Mψ) * ‖f q‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul (hMg x) (hMψ (x - q)) (norm_nonneg _) hMg0)
                (norm_nonneg _)
        · have hz : |r| + r ^ 2 < ‖x - q‖ := by
            have := norm_sub_norm_le q x
            rw [norm_sub_rev] at this
            linarith [not_le.mp hq]
          rw [scaleKernel_eq_zero hz, norm_zero, zero_mul, mul_zero]
          exact mul_nonneg hb1 hb2
      · rw [hRg x (not_le.mp hx), norm_zero, zero_mul]
        exact mul_nonneg hb1 hb2
  -- Left side through Fubini.
  have hL : ∫ x, (g x : ℂ) * (smoothing r f x : ℂ) = ∫ q, (f q : ℂ) * S q := by
    have hsw := integral_integral_swap hint
    calc ∫ x, (g x : ℂ) * (smoothing r f x : ℂ)
        = ∫ x, ∫ q, (g x : ℂ) * ((scaleKernel r (x - q) : ℂ) * (f q : ℂ)) := by
          congr 1
          funext x
          rw [smoothing, ← integral_complex_ofReal, ← integral_const_mul]
          simp only [Complex.ofReal_mul]
      _ = ∫ q, ∫ x, (g x : ℂ) * ((scaleKernel r (x - q) : ℂ) * (f q : ℂ)) := hsw
      _ = ∫ q, (f q : ℂ) * S q := by
          congr 1
          funext q
          rw [hS, ← integral_const_mul]
          congr 1
          funext x
          ring
  -- Right side through the L² pairing.
  have hR : ∫ q, (f q : ℂ) * S q = ∫ ζ, (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ S) ζ := by
    have h1 : ∫ q, (f q : ℂ) * S q = l2Pairing m (realLp hf) (S.toLp 2 volume) := by
      rw [l2Pairing_apply]
      apply integral_congr_ae
      filter_upwards [coeFn_realLp hf, S.coeFn_toLp 2 volume] with q h1 h2
      rw [h1, h2]
    have h2 : l2Pairing m (realLp hf) (S.toLp 2 volume) =
        l2Pairing m (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ((𝓕⁻ S).toLp 2 volume) := by
      have hFF : 𝓕⁻ (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) = realLp hf :=
        (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm_apply_apply _
      conv_lhs => rw [← hFF]
      rw [l2Pairing_fourierInv_left, SchwartzMap.toLp_fourierInv_eq]
    rw [h1, h2, l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [(𝓕⁻ S).coeFn_toLp 2 volume] with ζ hζ
    rw [hζ]
  have hFS : ∀ ζ, (𝓕⁻ S) ζ = scaleKernelHat r ζ * (𝓕⁻ (realCompactTest g hg hgc)) ζ := by
    intro ζ
    rw [schwartz_fourierInv_apply, schwartz_fourierInv_apply, hSdef,
      SchwartzMap.fourier_convolution]
    simp only [SchwartzMap.pairing_apply, ContinuousLinearMap.mul_apply']
    rw [fourier_scaleKernelTest, scaleKernelHat_neg]
  rw [hL, hR]
  congr 1
  funext ζ
  rw [hFS]

/-- Plancherel for the smoothed function, for arbitrary real `f ∈ L²`. -/
theorem lintegral_enorm_smoothing_sq {r : ℝ} (_hr : 0 < r) {f : FourierSpace m → ℝ}
    (hf : MemLp f 2 volume) :
    ∫⁻ p, ‖smoothing r f p‖ₑ ^ 2 =
      ∫⁻ ζ, ‖scaleKernelHat r ζ‖ₑ ^ 2 * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  have hbound : ∀ ζ : FourierSpace m, ‖scaleKernelHat r ζ‖ ≤
      ∫ z : FourierSpace m, ‖(scaleKernel r z : ℂ)‖ := fun ζ =>
    Real.norm_fourier_le_integral_norm (fun z : FourierSpace m => (scaleKernel r z : ℂ)) ζ
  have hGm : MemLp (fun ζ => scaleKernelHat r ζ * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ) 2 volume :=
    (Lp.memLp (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m)))).of_le_mul (c := ∫ z : FourierSpace m, ‖(scaleKernel r z : ℂ)‖)
      ((continuous_scaleKernelHat r).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun ζ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound ζ) (norm_nonneg _))
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hH : ∀ᵐ p ∂volume, (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) p =
      (smoothing r f p : ℂ) := by
    apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
      ((Complex.continuous_ofReal.comp (continuous_smoothing r hfl)).locallyIntegrable)
    intro g hg hgc
    simp only [Complex.real_smul, Function.comp_apply]
    rw [integral_test_smoothing hf g hg hgc]
    have h1 : ∫ x, (g x : ℂ) * (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x =
        l2Pairing m (𝓕⁻ (hGm.toLp _)) ((realCompactTest g hg hgc).toLp 2 volume) := by
      rw [l2Pairing_apply]
      apply integral_congr_ae
      filter_upwards [(realCompactTest g hg hgc).coeFn_toLp 2 volume] with x hx
      rw [hx, realCompactTest_apply, mul_comm]
    rw [h1, l2Pairing_fourierInv_left, SchwartzMap.toLp_fourierInv_eq, l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [hGm.coeFn_toLp, (𝓕⁻ (realCompactTest g hg hgc)).coeFn_toLp 2 volume]
      with ζ h1 h2
    rw [h1, h2]
    ring
  have hHn : ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ =
      ‖hGm.toLp _‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact congrArg _ ((Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.nnnorm_map _)
  calc ∫⁻ p, ‖smoothing r f p‖ₑ ^ 2
      = ∫⁻ p, ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) p‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [hH] with p hp
        rw [hp, enorm_complex_ofReal]
    _ = ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ ^ 2 := by
        rw [lintegral_enorm_sq_eq (Lp.aestronglyMeasurable _), Lp.enorm_def]
    _ = ‖hGm.toLp _‖ₑ ^ 2 := by rw [hHn]
    _ = ∫⁻ ζ, ‖scaleKernelHat r ζ * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
        rw [Lp.enorm_def, eLpNorm_congr_ae hGm.coeFn_toLp,
          ← lintegral_enorm_sq_eq hGm.aestronglyMeasurable]
    _ = _ := by simp only [enorm_mul, mul_pow]

/-! ### Assembly -/

/-- The constant `C_m = ‖ψ_1‖₂² / c_m`. -/
def fourierAffineConstant (m : ℕ) : ℝ≥0 :=
  Real.toNNReal (scaleKernelEnergy m / Classical.choose (exists_symbol_lower_bound m))

theorem measurable_smoothing_sq {f : FourierSpace m → ℝ} (hf : MemLp f 2 volume) :
    AEMeasurable (Function.uncurry fun (r : ℝ) (p : FourierSpace m) =>
      (ENNReal.ofReal r)⁻¹ ^ 3 * ‖smoothing r f p‖ₑ ^ 2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hk : AEStronglyMeasurable (fun x : (ℝ × FourierSpace m) × FourierSpace m =>
      scaleKernel x.1.1 (x.1.2 - x.2) * f x.2)
      (((volume.restrict (Ioi (0 : ℝ))).prod volume).prod volume) :=
    (measurable_scaleKernel₂.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.sub measurable_snd))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd
  have hs := hk.integral_prod_right'
  exact ((ENNReal.measurable_ofReal.comp measurable_fst).inv.pow_const 3).aemeasurable.mul
    (hs.enorm.pow_const 2)

theorem lintegral_time_fourier_le {f : FourierSpace m → ℝ} (hf : MemLp f 2 volume) :
    ∫⁻ z, ENNReal.ofReal |(WithLp.ofLp z).2| * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 ≤
      fourierAffineConstant m * affineCarlesonEnergy f := by
  obtain ⟨hc, hlow⟩ := Classical.choose_spec (exists_symbol_lower_bound m)
  rw [fourierAffineConstant]
  generalize Classical.choose (exists_symbol_lower_bound m) = c at hc hlow ⊢
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  -- Step 1: the symbol lower bound, frequency by frequency.
  have h1 : ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal |(WithLp.ofLp z).2| * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 ≤
      ∫⁻ ζ, (∫⁻ r in Ioi (0 : ℝ), ‖scaleKernelHat r ζ‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹ ^ 3) *
        ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ζ => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le]
    gcongr
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hlow ζ)
    exact mul_le_mul_of_nonneg_left (by linarith [sq_nonneg ‖(WithLp.ofLp ζ).1‖]) hc.le
  -- Step 2: Tonelli in `(ζ, r)`.
  have hXm : AEMeasurable (Function.uncurry fun (ζ : FourierSpace m) (r : ℝ) =>
      ‖scaleKernelHat r ζ‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹ ^ 3 * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hcont : Measurable fun x : FourierSpace m × ℝ =>
        ‖symbolGenerator (dilate x.2 x.1)‖ₑ ^ 2 * (ENNReal.ofReal x.2)⁻¹ ^ 3 :=
      ((continuous_symbolGenerator.comp (continuous_dilate₂.comp
        continuous_swap)).measurable.enorm.pow_const 2).mul
        ((ENNReal.measurable_ofReal.comp measurable_snd).inv.pow_const 3)
    have hae : ∀ᵐ x ∂(volume.prod (volume.restrict (Ioi (0 : ℝ)))),
        (x : FourierSpace m × ℝ).2 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
    refine (hcont.aemeasurable.congr ?_).mul
      ((Lp.aestronglyMeasurable (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m)))).enorm.pow_const 2).comp_fst
    filter_upwards [hae] with x hx
    rw [scaleKernelHat_eq hx]
  have h2 : ∫⁻ ζ, (∫⁻ r in Ioi (0 : ℝ), ‖scaleKernelHat r ζ‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹ ^ 3) *
        ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 ≤
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ ζ, ‖scaleKernelHat r ζ‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹ ^ 3 *
        ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
    rw [← lintegral_lintegral_swap hXm]
    exact lintegral_mono fun ζ => lintegral_mul_const_le _ _
  -- Step 3: Plancherel at each scale.
  have h3 : ∫⁻ r in Ioi (0 : ℝ), ∫⁻ ζ, ‖scaleKernelHat r ζ‖ₑ ^ 2 * (ENNReal.ofReal r)⁻¹ ^ 3 *
        ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 =
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ p, (ENNReal.ofReal r)⁻¹ ^ 3 * ‖smoothing r f p‖ₑ ^ 2 := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hk : (ENNReal.ofReal r)⁻¹ ^ 3 ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne')
    rw [lintegral_const_mul' _ _ hk, lintegral_enorm_smoothing_sq hr hf,
      ← lintegral_const_mul' _ _ hk]
    congr 1
    funext ζ
    ring
  -- Step 4: Tonelli in `(r, p)` and the pointwise affine bound.
  have h4 : ∫⁻ r in Ioi (0 : ℝ), ∫⁻ p, (ENNReal.ofReal r)⁻¹ ^ 3 * ‖smoothing r f p‖ₑ ^ 2 ≤
      ENNReal.ofReal (scaleKernelEnergy m) * affineCarlesonEnergy f := by
    rw [lintegral_lintegral_swap (measurable_smoothing_sq hf), affineCarlesonEnergy,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun p => ?_
    rw [scaleMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_scaleDensity (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
    have hr' : 0 < r := hr
    have hx0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr').ne'
    have hxt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    have hx : (ENNReal.ofReal r)⁻¹ ^ 3 * ENNReal.ofReal r ^ 2 = (ENNReal.ofReal r)⁻¹ := by
      rw [show 3 = 1 + 2 by rfl, pow_add, pow_one, mul_assoc, ← mul_pow,
        ENNReal.inv_mul_cancel hx0 hxt, one_pow, mul_one]
    calc (ENNReal.ofReal r)⁻¹ ^ 3 * ‖smoothing r f p‖ₑ ^ 2
        ≤ (ENNReal.ofReal r)⁻¹ ^ 3 * (ENNReal.ofReal (scaleKernelEnergy m) *
            ENNReal.ofReal r ^ 2 * affineEnergy f p r) := by
          gcongr
          exact enorm_smoothing_sq_le_affineEnergy hr' hfl p
      _ = ENNReal.ofReal (scaleKernelEnergy m) *
            (((ENNReal.ofReal r)⁻¹ ^ 3 * ENNReal.ofReal r ^ 2) * affineEnergy f p r) := by ring
      _ = ENNReal.ofReal (scaleKernelEnergy m) *
            (ENNReal.ofReal (1 / r) * affineEnergy f p r) := by
          rw [hx, one_div, ENNReal.ofReal_inv_of_pos hr']
  -- Conclude.
  have hall : ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal |(WithLp.ofLp z).2| * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 ≤
      ENNReal.ofReal (scaleKernelEnergy m) * affineCarlesonEnergy f :=
    h1.trans (h2.trans (h3.le.trans h4))
  have hcinv : ENNReal.ofReal (1 / c) * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hc.le), one_div_mul_cancel hc.ne',
      ENNReal.ofReal_one]
  calc ∫⁻ z, ENNReal.ofReal |(WithLp.ofLp z).2| * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2
      = ENNReal.ofReal (1 / c) * (ENNReal.ofReal c *
          ∫⁻ z, ENNReal.ofReal |(WithLp.ofLp z).2| * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2) := by
        rw [← mul_assoc, hcinv, one_mul]
    _ ≤ ENNReal.ofReal (1 / c) * (ENNReal.ofReal (scaleKernelEnergy m) *
          affineCarlesonEnergy f) := by gcongr
    _ = ENNReal.ofReal (scaleKernelEnergy m / c) * affineCarlesonEnergy f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (one_div_nonneg.mpr hc.le), one_div_mul_eq_div]

/-- **Fourier-affine bound.** There is `C_m < ∞` such that every real `f ∈ L²(ℝ^m × ℝ)`
satisfies `∫ |τ| |f̂(ξ,τ)|² dξ dτ ≤ C_m ∫_V ∫_0^∞ a_f(p,r)² dr/r dp`, where
`a_f(p,r)² = r^(-k-2) inf_{a,b} ∫_{P_b(p,r)} |f - a - b·u|²`, `k = m + 2`.
Both sides are extended nonnegative and may be infinite. -/
theorem fourierAffine_bound (m : ℕ) :
    ∃ C : ℝ≥0, ∀ (f : FourierSpace m → ℝ) (hf : MemLp f 2 volume),
      ∫⁻ z, ENNReal.ofReal |(WithLp.ofLp z).2| *
          ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 ≤
        C * ∫⁻ p : FourierSpace m, ∫⁻ r : ℝ, ((ENNReal.ofReal r)⁻¹ ^ (m + 4) *
          ⨅ (a : ℝ) (B : Spatial m →L[ℝ] ℝ),
            ∫⁻ q in {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
                |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2},
              ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ ^ 2) ∂scaleMeasure :=
  ⟨fourierAffineConstant m, fun _ hf => lintegral_time_fourier_le hf⟩

/-- **Corollary.** If the affine energy `E(f)` is finite, the half-time derivative of `f`
(in the distributional sense of `HalfTimeDerivative`) has a real L² representative `g`,
namely the inverse Fourier transform of `|τ|^(1/2) f̂`, and `∫ g² ≤ C_m · E(f)`. -/
theorem exists_halfTime_representative (m : ℕ) :
    ∃ C : ℝ≥0, ∀ (f : FourierSpace m → ℝ) (hf : MemLp f 2 volume),
      (∫⁻ p : FourierSpace m, ∫⁻ r : ℝ, ((ENNReal.ofReal r)⁻¹ ^ (m + 4) *
          ⨅ (a : ℝ) (B : Spatial m →L[ℝ] ℝ),
            ∫⁻ q in {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
                |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2},
              ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ ^ 2) ∂scaleMeasure) < ⊤ →
      ∃ (hA : MemLp (fun z => (symbol z : ℂ) *
            (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume)
        (g : FourierSpace m → ℝ) (hg : MemLp g 2 volume),
        Measurable g ∧ realLp hg = inverseHalf hA ∧ RepHalf hf g Set.univ ∧
          ∫⁻ x, ‖g x‖ₑ ^ 2 ≤
            C * ∫⁻ p : FourierSpace m, ∫⁻ r : ℝ, ((ENNReal.ofReal r)⁻¹ ^ (m + 4) *
              ⨅ (a : ℝ) (B : Spatial m →L[ℝ] ℝ),
                ∫⁻ q in {q : FourierSpace m | ‖(WithLp.ofLp q).1 - (WithLp.ofLp p).1‖ < r ∧
                    |(WithLp.ofLp q).2 - (WithLp.ofLp p).2| < r ^ 2},
                  ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ ^ 2) ∂scaleMeasure := by
  refine ⟨fourierAffineConstant m, fun f hf hfin => ?_⟩
  have hle := lintegral_time_fourier_le hf
  have hsym : ∀ z : FourierSpace m, ‖(symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 =
      ENNReal.ofReal |(WithLp.ofLp z).2| * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 := by
    intro z
    rw [enorm_mul, mul_pow, enorm_complex_ofReal, enorm_sq_eq_ofReal, symbol,
      timeCoordinate_apply, ← Real.sqrt_eq_rpow, Real.sq_sqrt (abs_nonneg _)]
  have hmeas : AEStronglyMeasurable (fun z => (symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) volume :=
    (Complex.continuous_ofReal.comp (continuous_symbol m)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)
  have hL : ∫⁻ z, ‖(symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 =
      ∫⁻ z, ENNReal.ofReal |(WithLp.ofLp z).2| * ‖(𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 := by simp only [hsym]
  have hfinL : ∫⁻ z, ‖(symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 < ⊤ := by
    rw [hL]
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin)
  have hA : MemLp (fun z => (symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume := by
    rw [memLp_iff]
    rw [lintegral_enorm_sq_eq hmeas] at hfinL
    by_contra h
    rw [not_lt, top_le_iff] at h
    simp [h] at hfinL
  obtain ⟨w₀, g, hg, -, -, hgm, -, hreal, hrep, hn1, hn2⟩ := exists_real_inverse hf hA
  refine ⟨hA, g, hg, hgm, hreal, hrep, ?_⟩
  have hgn : eLpNorm g 2 volume = eLpNorm (fun z => (symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume := by
    have e1 : eLpNorm g 2 volume = ‖hg.toLp g‖ₑ := by
      rw [Lp.enorm_def, eLpNorm_congr_ae hg.coeFn_toLp]
    have e2 : eLpNorm (fun z => (symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z) 2 volume = ‖inverseFrequency hA‖ₑ := by
      rw [Lp.enorm_def, eLpNorm_congr_ae (coeFn_inverseFrequency hA)]
    rw [e1, e2, ← ofReal_norm, ← ofReal_norm, hn1, hn2]
  calc ∫⁻ x, ‖g x‖ₑ ^ 2 = eLpNorm g 2 volume ^ 2 := lintegral_enorm_sq_eq hg.aestronglyMeasurable
    _ = ∫⁻ z, ‖(symbol z : ℂ) * (𝓕 (realLp hf) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2 := by rw [hgn, lintegral_enorm_sq_eq hmeas]
    _ = _ := hL
    _ ≤ _ := hle

end ParabolicRectifiability.FourierAffine
