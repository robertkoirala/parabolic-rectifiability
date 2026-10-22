import ParabolicRectifiability.Analysis.HalfTimeDerivative.PhysicalApproximation

/-! # The bilinear half-time distribution

The pairings here are complex bilinear: no complex conjugation is inserted.
The square-root symbol acts only through the Schwartz-to-L2 map of the half-time derivative.
-/

noncomputable section

open MeasureTheory SchwartzMap FourierTransform ContinuousLinearMap
open scoped SchwartzMap

namespace ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-- Continuous bilinear integration on complex L2. -/
def l2Pairing (m : ℕ) :
    Lp ℂ 2 (volume : Measure (FourierSpace m)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (FourierSpace m)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2

theorem l2Pairing_apply (f g : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    l2Pairing m f g = ∫ x, f x * g x :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral f g

theorem integrable_l2Pairing (f g : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    Integrable (fun x => f x * g x) volume :=
  (Lp.memLp f).integrable_mul (Lp.memLp g)

theorem norm_l2Pairing_le (f g : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    ‖l2Pairing m f g‖ ≤ ‖f‖ * ‖g‖ := by
  have he : l2Pairing m f g = L1.integral (f • g : Lp ℂ 1 volume) := by
    rw [l2Pairing_apply, L1.integral_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (f := f) (g := g) (r := 1)] with x hx
    exact hx.symm
  rw [he]
  exact (L1.norm_integral_le _).trans (Lp.norm_smul_le f g)

/-- Complexification of an actual real L2 function. -/
def realLp {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) : Lp ℂ 2 (volume : Measure (FourierSpace m)) :=
  hH.ofReal.toLp (fun x => (H x : ℂ))

theorem coeFn_realLp {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    realLp hH =ᵐ[volume] fun x => (H x : ℂ) :=
  MemLp.coeFn_toLp _

theorem norm_realLp {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    ‖realLp hH‖ = ‖hH.toLp H‖ := by
  simp only [realLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_congr_norm_ae hH.ofReal.aestronglyMeasurable hH.aestronglyMeasurable
    (.of_forall fun x => Complex.norm_real (H x))

/-- The continuous complex-linear half-time functional for complex L2 data. -/
def halfTimeFunctional (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    𝓢(FourierSpace m, ℂ) →L[ℂ] ℂ :=
  l2Pairing m f ∘L halfTimeDeriv m

theorem halfTimeFunctional_apply (f : Lp ℂ 2 (volume : Measure (FourierSpace m)))
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    halfTimeFunctional f ψ = ∫ x, f x * halfTimeDeriv m ψ x :=
  l2Pairing_apply _ _

/-- The same functional in the library's pointwise-convergence distribution topology. -/
def halfTimeDistribution (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    𝓢'(FourierSpace m, ℂ) :=
  toPointwiseConvergenceCLM ℂ _ _ _ (halfTimeFunctional f)

@[simp] theorem halfTimeDistribution_apply
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (ψ : 𝓢(FourierSpace m, ℂ)) :
    halfTimeDistribution f ψ = halfTimeFunctional f ψ := rfl

theorem integrable_real_halfTime {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun x => (H x : ℂ) * halfTimeDeriv m ψ x) volume :=
  hH.ofReal.integrable_mul (Lp.memLp _)

theorem halfTimeFunctional_real_apply {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    halfTimeFunctional (realLp hH) ψ = ∫ x, (H x : ℂ) * halfTimeDeriv m ψ x := by
  rw [halfTimeFunctional_apply]
  exact integral_congr_ae ((coeFn_realLp hH).mul (.refl _ _))

theorem norm_halfTimeFunctional_le (f : Lp ℂ 2 (volume : Measure (FourierSpace m)))
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖halfTimeFunctional f ψ‖ ≤ ‖f‖ * ‖weightedLp (𝓕 ψ)‖ := by
  exact (norm_l2Pairing_le f (halfTimeDeriv m ψ)).trans_eq
    (congrArg (‖f‖ * ·) (norm_halfTimeDeriv ψ))

theorem norm_halfTimeFunctional_le_polynomial
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖halfTimeFunctional f ψ‖ ≤ ‖f‖ * ‖(polynomialMul m (𝓕 ψ)).toLp 2 volume‖ :=
  (norm_halfTimeFunctional_le f ψ).trans
    (mul_le_mul_of_nonneg_left (norm_weightedLp_le _) (norm_nonneg _))

/-- Continuous frequency pairing, with the nonsmooth symbol handled in L2. -/
def frequencyFunctional (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    𝓢(FourierSpace m, ℂ) →L[ℂ] ℂ :=
  l2Pairing m (𝓕 f) ∘L weightedLpCLM m

theorem integrable_frequencyFunctional
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (η : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun z => (𝓕 f) z * (symbol z : ℂ) * η z) volume := by
  exact ((Lp.memLp (𝓕 f)).integrable_mul (memLp_symbol_mul η)).congr
    (.of_forall fun z => (mul_assoc _ _ _).symm)

theorem frequencyFunctional_apply
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (η : 𝓢(FourierSpace m, ℂ)) :
    frequencyFunctional f η = ∫ z, (𝓕 f) z * (symbol z : ℂ) * η z := by
  change l2Pairing m (𝓕 f) (weightedLp η) = _
  rw [l2Pairing_apply]
  apply integral_congr_ae
  filter_upwards [coeFn_weightedLp η] with z hz
  simp only [hz, mul_assoc]

/-- Frequency functional as a tempered distribution. -/
def frequencyDistribution (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    𝓢'(FourierSpace m, ℂ) :=
  toPointwiseConvergenceCLM ℂ _ _ _ (frequencyFunctional f)

theorem l2Pairing_toLp (f : Lp ℂ 2 (volume : Measure (FourierSpace m)))
    (η : 𝓢(FourierSpace m, ℂ)) :
    l2Pairing m f (η.toLp 2 volume) = (f : 𝓢'(FourierSpace m, ℂ)) η := by
  rw [l2Pairing_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [η.coeFn_toLp 2 volume] with x hx
  simp [hx, mul_comm]

/-- The inverse Fourier transform is symmetric for the bilinear L2 pairing.
This follows from library distribution compatibility and density, not from
sesquilinear Plancherel with a suppressed conjugation. -/
theorem l2Pairing_fourierInv_left
    (f g : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    l2Pairing m (𝓕⁻ f) g = l2Pairing m f (𝓕⁻ g) := by
  apply DenseRange.induction_on (p := fun g =>
    l2Pairing m (𝓕⁻ f) g = l2Pairing m f (𝓕⁻ g))
    (SchwartzMap.denseRange_toLpCLM (E := FourierSpace m) (F := ℂ)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) g
  · exact isClosed_eq (l2Pairing m (𝓕⁻ f)).continuous
      ((l2Pairing m f).continuous.comp continuous_fourierInv)
  intro η
  change l2Pairing m (𝓕⁻ f) (η.toLp 2 volume) =
    l2Pairing m f (𝓕⁻ (η.toLp 2 volume))
  rw [SchwartzMap.toLp_fourierInv_eq, l2Pairing_toLp, l2Pairing_toLp]
  exact congrArg (fun T : 𝓢'(FourierSpace m, ℂ) => T η)
    (Lp.fourierInv_toTemperedDistribution_eq f).symm

theorem schwartz_fourierInv_apply (ψ : 𝓢(FourierSpace m, ℂ)) (z : FourierSpace m) :
    (𝓕⁻ ψ) z = (𝓕 ψ) (-z) := rfl

/-- The even symbol and reflection identify the two continuous functionals. -/
theorem halfTimeFunctional_eq_frequencyFunctional_fourierInv
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (ψ : 𝓢(FourierSpace m, ℂ)) :
    halfTimeFunctional f ψ = frequencyFunctional f (𝓕⁻ ψ) := by
  apply DenseRange.induction_on (p := fun f =>
    halfTimeFunctional f ψ = frequencyFunctional f (𝓕⁻ ψ))
    (SchwartzMap.denseRange_toLpCLM (E := FourierSpace m) (F := ℂ)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq ((l2Pairing m).flip (halfTimeDeriv m ψ)).continuous
      (((l2Pairing m).flip (weightedLp (𝓕⁻ ψ))).continuous.comp continuous_fourier)
  intro χ
  change l2Pairing m (χ.toLp 2 volume) (halfTimeDeriv m ψ) =
    frequencyFunctional (χ.toLp 2 volume) (𝓕⁻ ψ)
  rw [halfTimeDeriv_apply]
  change l2Pairing m (χ.toLp 2 volume) (𝓕⁻ (weightedLp (𝓕 ψ))) = _
  rw [← l2Pairing_fourierInv_left,
    SchwartzMap.toLp_fourierInv_eq, l2Pairing_apply, frequencyFunctional_apply,
    SchwartzMap.toLp_fourier_eq]
  calc
    _ = ∫ z, (𝓕⁻ χ) z * (symbol z : ℂ) * (𝓕 ψ) z := by
      apply integral_congr_ae
      filter_upwards [(𝓕⁻ χ).coeFn_toLp 2 volume, coeFn_weightedLp (𝓕 ψ)] with z hz hw
      simp only [hz, hw, mul_assoc]
    _ = ∫ z, (𝓕 χ) z * (symbol z : ℂ) * (𝓕⁻ ψ) z := by
      have hn := integral_neg_eq_self (fun z : FourierSpace m =>
        (𝓕⁻ χ : 𝓢(FourierSpace m, ℂ)) z * (symbol z : ℂ) *
          (𝓕 ψ : 𝓢(FourierSpace m, ℂ)) z) volume
      exact hn.symm.trans (integral_congr_ae (.of_forall fun z => by
        simp only [schwartz_fourierInv_apply, neg_neg, symbol_neg]))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(𝓕 χ).coeFn_toLp 2 volume] with z hz
      rw [hz]

/-- Distributional Fourier identity in the library's pointwise-convergence topology. -/
theorem halfTimeDistribution_eq_fourierInv
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    halfTimeDistribution f = 𝓕⁻ (frequencyDistribution f) := by
  ext ψ
  exact halfTimeFunctional_eq_frequencyFunctional_fourierInv f ψ

/-- Bilinear frequency formula: the Fourier test is evaluated at the reflected frequency. -/
theorem halfTimeFunctional_fourier_formula
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (ψ : 𝓢(FourierSpace m, ℂ)) :
    halfTimeFunctional f ψ = ∫ z, (𝓕 f) z * (symbol z : ℂ) * (𝓕 ψ) (-z) := by
  rw [halfTimeFunctional_eq_frequencyFunctional_fourierInv, frequencyFunctional_apply]
  rfl

theorem norm_frequencyFunctional_le
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (η : 𝓢(FourierSpace m, ℂ)) :
    ‖frequencyFunctional f η‖ ≤ ‖f‖ * ‖weightedLp η‖ := by
  change ‖l2Pairing m (𝓕 f) (weightedLp η)‖ ≤ _
  simpa only [Lp.norm_fourier_eq] using norm_l2Pairing_le (𝓕 f) (weightedLp η)

theorem norm_frequencyFunctional_le_polynomial
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (η : 𝓢(FourierSpace m, ℂ)) :
    ‖frequencyFunctional f η‖ ≤ ‖f‖ * ‖(polynomialMul m η).toLp 2 volume‖ :=
  (norm_frequencyFunctional_le f η).trans
    (mul_le_mul_of_nonneg_left (norm_weightedLp_le η) (norm_nonneg f))

theorem norm_real_halfTimeFunctional_le {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (ψ : 𝓢(FourierSpace m, ℂ)) :
    ‖halfTimeFunctional (realLp hH) ψ‖ ≤ ‖hH.toLp H‖ * ‖weightedLp (𝓕 ψ)‖ := by
  simpa only [norm_realLp] using norm_halfTimeFunctional_le (realLp hH) ψ

theorem realLp_congr {H H' : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (hH' : MemLp H' 2 volume) (h : H =ᵐ[volume] H') :
    realLp hH = realLp hH' := by
  apply Lp.ext
  filter_upwards [coeFn_realLp hH, coeFn_realLp hH', h] with x hx hx' hh
  rw [hx, hx', hh]

/-- Changing the L2 representative of the derivative leaves the actual pairing unchanged. -/
theorem halfTimeFunctional_real_representative {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (ψ : 𝓢(FourierSpace m, ℂ)) {v : FourierSpace m → ℂ}
    (hv : v =ᵐ[volume] halfTimeDeriv m ψ) :
    Integrable (fun x => (H x : ℂ) * v x) volume ∧
      halfTimeFunctional (realLp hH) ψ = ∫ x, (H x : ℂ) * v x := by
  refine ⟨(integrable_real_halfTime hH ψ).congr ?_, ?_⟩
  · exact Filter.EventuallyEq.mul (.refl _ _) hv.symm
  · rw [halfTimeFunctional_real_apply]
    exact integral_congr_ae (Filter.EventuallyEq.mul (.refl _ _) hv.symm)

theorem integrable_reflected_frequency
    (f : Lp ℂ 2 (volume : Measure (FourierSpace m))) (ψ : 𝓢(FourierSpace m, ℂ)) :
    Integrable (fun z => (𝓕 f) z * (symbol z : ℂ) * (𝓕 ψ) (-z)) volume :=
  integrable_frequencyFunctional f (𝓕⁻ ψ)

/-- A bridge to the sesquilinear inner product, with the conjugation displayed explicitly. -/
theorem l2Pairing_star_left (f g : Lp ℂ 2 (volume : Measure (FourierSpace m))) :
    l2Pairing m (star f) g = inner ℂ f g := by
  rw [l2Pairing_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with x hx
  simp only [hx, Pi.star_apply, RCLike.inner_apply, mul_comm]
  rfl

/-- Reality of the distribution on real tests uses reality of `halfTimeDeriv` on real tests. -/
theorem halfTimeFunctional_real_im_eq_zero {H : FourierSpace m → ℝ}
    (hH : MemLp H 2 volume) (ψ : 𝓢(FourierSpace m, ℂ)) (hψ : ∀ x, (ψ x).im = 0) :
    (halfTimeFunctional (realLp hH) ψ).im = 0 := by
  rw [halfTimeFunctional_real_apply]
  have hi := integral_im (integrable_real_halfTime hH ψ)
  change (∫ x, ((H x : ℂ) * halfTimeDeriv m ψ x).im) =
    (∫ x, (H x : ℂ) * halfTimeDeriv m ψ x).im at hi
  rw [← hi]
  apply integral_eq_zero_of_ae
  filter_upwards [halfTimeDeriv_ae_im_eq_zero ψ hψ] with x hx
  simp [Complex.mul_im, hx]

end ParabolicRectifiability.HalfTimeDerivative



