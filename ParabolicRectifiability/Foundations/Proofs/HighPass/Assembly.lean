import ParabolicRectifiability.Foundations.Proofs.HighPass.Estimates
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.FibreKernel

/-! # The high-pass chain: assembly

The four public statements of the high-pass chain are proved here from the intermediate
statements (`FhpbcOneDimUnweightedStatement`, and so on); the a.e. fibre transfer
`fhpa_ae_fibre_halfTimeDeriv_proof` is imported, not re-proved.

* `fhp_weightedPairing : HighPassWeightedPairingStatement` (b1). First
  `fhpbc_bracketL1 : FhpbcBracketL1Statement`, the quantitative `L¹(dt)` estimate: the fibre
  transfer replaces `|D_t|^{1/2}θ` by the pointwise `testKernel θ` on a.e. time fibre; the
  spatial integrability of `c · testKernel θ (·,t)` (proved here) gives the a.e. inner clause and
  the split at the spatial base point `0`; the difference term uses
  `FhpbcOneDimUnweightedStatement`, the mean term `FhpbcOneDimWeightedStatement` and
  `FhpbcMarginalStatement`, and `FhpbcSchwartzNormFiniteStatement` makes the bound finite. Then
  the window limit (dominated convergence of the symmetric windows) and `|∫ ·| ≤ ∫ |·|`.
* `fhp_highPassKernel_facts : HighPassKernelStatement` (b2): the kernel facts
  (`fhpbc_kernelFacts`, from `FhpbcKernelBasicStatement`, `FhpbcKernelTailsStatement` and
  `FhpbcKernelFactsStatement`) and the test clause (`fhpbc_kernelTest`, from
  `FhpbcTimeConvolutionStatement` and the Schwartz and identity statements for the high-pass
  test).
* `fhp_bmoLog : HighPassBMOLogStatement` (c1): `FhpbcBMOLogGrowthStatement` and the convolution
  statement for BMO functions.
* `fhp_highPassIdentity : HighPassIdentityStatement` (c2): convergence clauses from
  `FhpbcLowPassStatement` and (c1); the identity by uniqueness of `L¹_loc` distributions
  (`ae_eq_of_integral_contDiff_smul_eq`): for compact smooth `φ`, with `θ = K *_t φ` and its
  Schwartz complexification `Θ` from (b2),
  `∫ φ ((1 - η *_t) G) = ∫ G (φ - η *_t φ) = T_G(Θ) = ∫ g θ = ∫ φ (K *_t g)`
  by `FhpbcLowPassStatement`, `FhpbcBracketOfAeEqStatement` with the kernel identity,
  `FhpbcSchwartzExtensionStatement` and `FhpbcHighPassPairingStatement`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-! ## (b1) -/

/-- The pointwise test kernel vanishes off the spatial support of the test. -/
theorem fhpbc_testKernel_eq_zero_of_notMem {m : ℕ} (θ : 𝓢(FourierSpace m, ℂ))
    {A : Set (Spatial m)} (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A) {u : Spatial m}
    (hu : u ∉ A) (t : ℝ) : testKernel θ (WithLp.toLp 2 (u, t)) = 0 := by
  have hz (s : ℝ) : θ (WithLp.toLp 2 (u, s)) = 0 := hθ _ (by simpa using hu)
  simp [testKernel, testKernelIntegrand, timeShift_toLp, hz]

/-- Spatial integrability against the test kernel of a Schwartz test supported spatially in a
compact set (the spatially compact analogue of `fhpa_integrable_mul_testKernel`): `u ↦ c(u) testKernel θ (u,t)` is
integrable for every continuous `c` and every time `t`. -/
theorem fhpbc_integrable_mul_testKernel {m : ℕ} (θ : 𝓢(FourierSpace m, ℂ))
    {A : Set (Spatial m)} (hA : IsCompact A) (hθ : fhp_IsSpatiallySupportedIn (⇑θ) A)
    (c : Spatial m → ℂ) (hcont : Continuous c) (t : ℝ) :
    Integrable (fun u : Spatial m => c u * testKernel θ (WithLp.toLp 2 (u, t))) := by
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hcont.continuousOn
  set B := FractionalKernel.kappa * testKernelControl θ * ∫ h, cancellationWeight h
  have hmeas : AEStronglyMeasurable (fun u : Spatial m => c u * testKernel θ
      (WithLp.toLp 2 (u, t))) volume :=
    hcont.aestronglyMeasurable.mul
      ((stronglyMeasurable_testKernel θ).comp_measurable
        (fhpab12_measurable_section m t)).aestronglyMeasurable
  have hg : Integrable (A.indicator fun _ => C * B) (volume : Measure (Spatial m)) :=
    (integrable_indicator_iff hA.measurableSet).2
      (integrableOn_const hA.measure_lt_top.ne)
  refine hg.mono' hmeas (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ A
  · rw [Set.indicator_of_mem hu, norm_mul]
    exact mul_le_mul (hC u hu) (norm_testKernel_le θ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC u hu))
  · rw [Set.indicator_of_notMem hu, fhpbc_testKernel_eq_zero_of_notMem θ hθ hu t, mul_zero,
      norm_zero]

/-- Subadditivity of the `L¹` lower integral along an a.e. split with one measurable term. -/
theorem fhpbc_lintegral_enorm_le_of_ae_eq_add {f T₁ T₂ : ℝ → ℂ}
    (h : f =ᵐ[volume] fun t => T₁ t + T₂ t) (hm : AEStronglyMeasurable T₁)
    {a b : ℝ≥0∞} (ha : ∫⁻ t, ‖T₁ t‖ₑ ≤ a) (hb : ∫⁻ t, ‖T₂ t‖ₑ ≤ b) :
    ∫⁻ t, ‖f t‖ₑ ≤ a + b := by
  have h' : (fun t => ‖f t‖ₑ) =ᵐ[volume] fun t => ‖T₁ t + T₂ t‖ₑ := by
    filter_upwards [h] with t ht
    simp only [ht]
  calc ∫⁻ t, ‖f t‖ₑ = ∫⁻ t, ‖T₁ t + T₂ t‖ₑ := lintegral_congr_ae h'
    _ ≤ ∫⁻ t, (‖T₁ t‖ₑ + ‖T₂ t‖ₑ) := lintegral_mono fun t => enorm_add_le _ _
    _ = (∫⁻ t, ‖T₁ t‖ₑ) + ∫⁻ t, ‖T₂ t‖ₑ := lintegral_add_left' hm.enorm _
    _ ≤ a + b := add_le_add ha hb

/-- **The quantitative bracket estimate** (`FhpbcBracketL1Statement`): the a.e. fibre transfer,
the split at the spatial base point `0`, the difference and mean term estimates and the finite
weighted norm. -/
theorem fhpbc_bracketL1 : FhpbcBracketL1Statement := by
  intro m G hG A hA
  obtain ⟨C₁, hC₁, h₁⟩ := fhpbc_b1_differenceBracket fhpbc_b1_oneDimUnweighted m G hG A hA
  obtain ⟨C₂, hC₂, h₂⟩ :=
    fhpbc_b1_meanBracket fhpbc_b1_oneDimWeighted fhpbc_b1_marginal m G hG A hA
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun θ hθ h0 => ?_⟩
  obtain ⟨L, hL⟩ := hG
  have hsec : ∀ t : ℝ, Continuous fun u : Spatial m => (G (WithLp.toLp 2 (u, t)) : ℂ) :=
    fun t => Complex.continuous_ofReal.comp (hL.continuous.comp
      (continuous_id.prodMk continuous_const : Continuous fun u : Spatial m => point u t))
  have hK : ∀ t : ℝ, Integrable fun u : Spatial m =>
      (G (WithLp.toLp 2 (u, t)) : ℂ) * testKernel θ (WithLp.toLp 2 (u, t)) :=
    fun t => fhpbc_integrable_mul_testKernel θ hA hθ _ (hsec t) t
  have hae : ∀ᵐ t : ℝ, halfTimeSpatialIntegrand G θ t =ᵐ[volume]
      fun u => (G (WithLp.toLp 2 (u, t)) : ℂ) * testKernel θ (WithLp.toLp 2 (u, t)) := by
    filter_upwards [fhpa_ae_fibre_halfTimeDeriv_proof θ] with t ht
    filter_upwards [ht] with u hu
    exact congrArg (fun z => (G (WithLp.toLp 2 (u, t)) : ℂ) * z) hu
  have hbr : halfTimeSpatialBracket G θ =ᵐ[volume] fun t =>
      ∫ u : Spatial m, (G (WithLp.toLp 2 (u, t)) : ℂ) * testKernel θ (WithLp.toLp 2 (u, t)) :=
    hae.mono fun t ht => integral_congr_ae ht
  have hsplit : (fun t : ℝ => ∫ u : Spatial m, (G (WithLp.toLp 2 (u, t)) : ℂ) *
      testKernel θ (WithLp.toLp 2 (u, t))) =
      fun t : ℝ => (∫ u : Spatial m,
          ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
            testKernel θ (WithLp.toLp 2 (u, t))) +
        (G (WithLp.toLp 2 (0, t)) : ℂ) *
          ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t)) := by
    funext t
    have i₁ : Integrable fun u : Spatial m =>
        ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
          testKernel θ (WithLp.toLp 2 (u, t)) :=
      fhpbc_integrable_mul_testKernel θ hA hθ
        (fun u => (G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ))
        ((hsec t).sub continuous_const) t
    have i₂ : Integrable fun u : Spatial m =>
        (G (WithLp.toLp 2 (0, t)) : ℂ) * testKernel θ (WithLp.toLp 2 (u, t)) :=
      fhpbc_integrable_mul_testKernel θ hA hθ (fun _ => (G (WithLp.toLp 2 (0, t)) : ℂ))
        continuous_const t
    rw [← integral_const_mul, ← integral_add i₁ i₂]
    congr 1
    funext u
    ring
  obtain ⟨hm₁, hb₁⟩ := h₁ θ hθ
  obtain ⟨hm₂, hb₂⟩ := h₂ θ hθ h0
  have hbr' : halfTimeSpatialBracket G θ =ᵐ[volume] fun t =>
      (∫ u : Spatial m,
          ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
            testKernel θ (WithLp.toLp 2 (u, t))) +
        (G (WithLp.toLp 2 (0, t)) : ℂ) *
          ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t)) := by
    rw [← hsplit]
    exact hbr
  have hbound : ∫⁻ t, ‖halfTimeSpatialBracket G θ t‖ₑ ≤
      ENNReal.ofReal (C₁ + C₂) * fhp_weightedTestNorm (⇑θ) := by
    rw [ENNReal.ofReal_add hC₁ hC₂, add_mul]
    exact fhpbc_lintegral_enorm_le_of_ae_eq_add hbr' hm₁ hb₁ hb₂
  refine ⟨hae.mono fun t ht => (hK t).congr ht.symm,
    ⟨(hm₁.add hm₂).congr hbr'.symm, ?_⟩, hbound⟩
  exact hbound.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (fhpbc_b1_schwartzNormFinite m θ))

/-- The symmetric windows of an integrable function converge to its integral. -/
theorem fhpbc_tendsto_window {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ t in Set.Icc (-R) R, f t) atTop (𝓝 (∫ t, f t)) := by
  have h := intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  show ∫ x in -R..R, f x = ∫ t in Set.Icc (-R) R, f t
  rw [intervalIntegral.integral_of_le (neg_le_self hR), integral_Icc_eq_integral_Ioc]

/-- **The weighted pairing estimate (b1)**: exactly `HighPassWeightedPairingStatement`. -/
theorem fhp_weightedPairing : HighPassWeightedPairingStatement := by
  intro m G hG A hA
  obtain ⟨C, hC, h⟩ := fhpbc_bracketL1 m G hG A hA
  refine ⟨C, hC, fun θ hθ h0 => ?_⟩
  obtain ⟨hae, hint, hbd⟩ := h θ hθ h0
  exact ⟨hae, hint, fhpbc_tendsto_window hint, (enorm_integral_le_lintegral_enorm _).trans hbd⟩

/-! ## (b2) -/

/-- The rapid tails (`FhpbcKernelTailsStatement` applied to the basic kernel facts and the
asymptotic expansion). -/
theorem fhpbc_kernelTails : FhpbcKernelTailsStatement :=
  fhpbc_b2_kernelTails fhpbc_b2_kernelBasic fhpbc_b2_inverseHalfAsymptotic

/-- The kernel facts of (b2) (basic facts, rapid tails, integrability and Fourier transform). -/
theorem fhpbc_kernelFacts : FhpbcKernelFactsStatement := by
  intro η hη
  obtain ⟨hev, hsm, hnear, -⟩ := fhpbc_b2_kernelBasic η hη
  obtain ⟨hint, hzero, hfour⟩ :=
    fhpbc_b2_kernelFourier fhpbc_b2_kernelBasic fhpbc_kernelTails fhpbc_b2_inverseHalfFourier
      η hη
  exact ⟨hev, hint, hzero, hsm, hnear, fhpbc_kernelTails η hη, hfour⟩

/-- The test clause of (b2) (time convolution, Schwartz membership, the half-derivative
identity, and `∫ K = 0`). -/
theorem fhpbc_kernelTest : FhpbcKernelTestStatement := by
  intro η hη m φ hφ hc
  obtain ⟨hsm, hsupp, hint, hmean, -⟩ :=
    fhpbc_b2_timeConvolution (fhp_highPassKernel η) (fhpbc_kernelFacts η hη).2.1 m φ hφ hc
  obtain ⟨⟨Θ, hΘ⟩, hN⟩ := fhpbc_b2_testSchwartz fhpbc_kernelFacts fhpbc_b2_timeConvolution
    fhpbc_b1_schwartzNormFinite η hη m φ hφ hc
  refine ⟨hsm, hsupp, hint, ?_, hN, Θ, hΘ,
    fhpbc_b2_testIdentity fhpbc_kernelFacts fhpbc_b2_timeConvolution η hη m φ hφ hc Θ hΘ⟩
  rw [hmean, (fhpbc_kernelFacts η hη).2.2.1, zero_mul]

/-- **The high-pass kernel (b2)**: exactly `HighPassKernelStatement`. -/
theorem fhp_highPassKernel_facts : HighPassKernelStatement := by
  intro η hη
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := fhpbc_kernelFacts η hη
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, fhpbc_kernelTest η hη⟩

/-! ## (c1) -/

/-- **Logarithmic growth of BMO functions (c1)**: exactly `HighPassBMOLogStatement`. -/
theorem fhp_bmoLog : HighPassBMOLogStatement := by
  intro m g hg
  exact ⟨fhpbc_c1_logGrowth m g hg,
    fhpbc_c1_convolution fhpbc_c1_logGrowth fhpbc_kernelFacts m g hg⟩

/-! ## (c2) -/

/-- **The high-pass identity (c2)**: exactly `HighPassIdentityStatement`. -/
theorem fhp_highPassIdentity : HighPassIdentityStatement := by
  intro m G g hG hg hrep η hη
  obtain ⟨-, -, -, -, -, -, -, hTest⟩ := fhp_highPassKernel_facts η hη
  obtain ⟨-, hae, hloc, -⟩ := (fhp_bmoLog m g hg).2 η hη
  obtain ⟨hlow, hcont, hφlow⟩ := fhpbc_c2_lowPass m G hG η hη.1
  refine ⟨hlow, hae, ?_⟩
  obtain ⟨L, hL⟩ := hG
  have hGc : Continuous G := by
    have h := hL.continuous.comp (fourierToParabolic m).continuous
    convert h using 1
    funext x
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  refine ae_eq_of_integral_contDiff_smul_eq (hGc.sub hcont).locallyIntegrable hloc ?_
  intro φ hφ hc
  obtain ⟨-, ⟨A, hA, hsupp⟩, -, hmean, -, Θ, hΘ, hid⟩ := hTest m φ hφ hc
  obtain ⟨hGηφ, hfub⟩ := hφlow φ hφ hc
  obtain ⟨-, hfubK⟩ :=
    fhpbc_c2_highPassPairing fhp_bmoLog fhpbc_kernelFacts m g hg η hη φ hφ hc
  have hGφ : Integrable (fun x => G x * φ x) :=
    (hGc.mul hφ.continuous).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hc)
  have hηGφ : Integrable (fun x => fhp_timeConvolution η G x * φ x) :=
    (hcont.mul hφ.continuous).integrable_of_hasCompactSupport (HasCompactSupport.mul_left hc)
  have hGψ : Integrable (fun x => G x * (φ x - fhp_timeConvolution η φ x)) := by
    refine (hGφ.sub hGηφ).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hKS := fhpbc_c2_bracketOfAeEq m G Θ (fun x => φ x - fhp_timeConvolution η φ x) hid hGψ
  have hSE := (fhpbc_c2_schwartzExtension fhp_weightedPairing fhpbc_c1_logGrowth
    (fhpbc_c2_correctedTest fhpbc_b1_schwartzNormFinite) m G g ⟨L, hL⟩ hg hrep _ Θ hΘ A hA
    hsupp hmean).2
  have heq : ∫ x, G x * (φ x - fhp_timeConvolution η φ x) =
      ∫ x, g x * fhp_timeConvolution (fhp_highPassKernel η) φ x :=
    Complex.ofReal_injective (hKS.symm.trans hSE)
  calc ∫ x, φ x • (G x - fhp_timeConvolution η G x)
      = ∫ x, (G x * φ x - fhp_timeConvolution η G x * φ x) := by
        congr 1
        funext x
        rw [smul_eq_mul]
        ring
    _ = (∫ x, G x * φ x) - ∫ x, fhp_timeConvolution η G x * φ x := integral_sub hGφ hηGφ
    _ = (∫ x, G x * φ x) - ∫ x, G x * fhp_timeConvolution η φ x := by rw [hfub]
    _ = ∫ x, (G x * φ x - G x * fhp_timeConvolution η φ x) := (integral_sub hGφ hGηφ).symm
    _ = ∫ x, G x * (φ x - fhp_timeConvolution η φ x) := by
        congr 1
        funext x
        ring
    _ = ∫ x, g x * fhp_timeConvolution (fhp_highPassKernel η) φ x := heq
    _ = ∫ x, fhp_timeConvolution (fhp_highPassKernel η) g x * φ x := hfubK
    _ = ∫ x, φ x • fhp_timeConvolution (fhp_highPassKernel η) g x := by
        congr 1
        funext x
        rw [smul_eq_mul, mul_comm]

end ParabolicRectifiability.Foundations
