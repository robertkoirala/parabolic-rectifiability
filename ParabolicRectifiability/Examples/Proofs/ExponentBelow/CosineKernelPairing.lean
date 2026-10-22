import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements
import ParabolicRectifiability.Foundations.Proofs.CompactBridge
import ParabolicRectifiability.Analysis.FractionalKernel.Multiplier

/-! # Cosine multipliers against the half-time test kernel

In the zero-dimensional spatial case, the pairing of the pointwise half-time derivative kernel
of a compact smooth test function with a cosine equals `(|ω|/(2π))^{1/2}` times the pairing of
the cosine with the test function itself.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.HalfTimeDerivative
open ParabolicRectifiability.FractionalKernel

/-- The cosine multiplier identity for the pointwise half-time test kernel.

The product integrability of the difference kernel gives Fubini in space and shift. Translation
turns the shifted cosine into its cosine and sine parts; the sine multiplier is odd and integrates
to zero, while the cosine multiplier is `frequencyIntegrand`. -/
theorem e2_cosine_kernelPairing_proof : E2CosineKernelPairingStatement := by
  intro φ hφ hc freq
  let ψ := realCompactTest φ hφ hc
  let c : FourierSpace 0 → ℂ := fun x => (Real.cos (freq * timeCoordinate 0 x) : ℂ)
  let s : FourierSpace 0 → ℂ := fun x => (Real.sin (freq * timeCoordinate 0 x) : ℂ)
  let J : ℂ := ∫ x, c x * ψ x
  let K : ℂ := ∫ x, s x * ψ x
  have hcψ : HasCompactSupport ψ := by
    change IsCompact (tsupport (realCompactTest φ hφ hc))
    rw [tsupport_realCompactTest]
    exact hc
  have hψI : Integrable ψ volume := ψ.integrable
  have hcmeas : AEStronglyMeasurable c volume := by
    dsimp [c]
    fun_prop
  have hsmeas : AEStronglyMeasurable s volume := by
    dsimp [s]
    fun_prop
  have hcbd : ∀ᵐ x ∂(volume : Measure (FourierSpace 0)), ‖c x‖ ≤ 1 := by
    filter_upwards [ae_of_all _ fun x => Real.abs_cos_le_one (freq * timeCoordinate 0 x)] with x hx
    change ‖(Real.cos (freq * timeCoordinate 0 x) : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact hx
  have hsbd : ∀ᵐ x ∂(volume : Measure (FourierSpace 0)), ‖s x‖ ≤ 1 := by
    filter_upwards [ae_of_all _ fun x => Real.abs_sin_le_one (freq * timeCoordinate 0 x)] with x hx
    change ‖(Real.sin (freq * timeCoordinate 0 x) : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact hx
  have hJI : Integrable (fun x => c x * ψ x) volume := hψI.bdd_mul hcmeas hcbd
  have hKI : Integrable (fun x => s x * ψ x) volume := hψI.bdd_mul hsmeas hsbd
  have hshiftI (h : ℝ) : Integrable (fun x => ψ (x - h • timeVector 0)) volume := by
    simpa [sub_eq_add_neg, Function.comp_def, neg_smul] using
      hψI.comp_add_right (-h • timeVector 0)
  have hshiftCosI (h : ℝ) :
      Integrable (fun x => c x * ψ (x - h • timeVector 0)) volume :=
    (hshiftI h).bdd_mul hcmeas hcbd
  have hshift (h : ℝ) :
      (∫ x, c x * ψ (x - h • timeVector 0)) =
        (Real.cos (freq * h) : ℂ) * J - (Real.sin (freq * h) : ℂ) * K := by
    have htime (x : FourierSpace 0) :
        timeCoordinate 0 (x + h • timeVector 0) = timeCoordinate 0 x + h := by
      rw [map_add, map_smul, timeCoordinate_timeVector, smul_eq_mul, mul_one]
    have hpoint (x : FourierSpace 0) :
        c (x + h • timeVector 0) * ψ x =
          (Real.cos (freq * h) : ℂ) * (c x * ψ x) -
            (Real.sin (freq * h) : ℂ) * (s x * ψ x) := by
      change (Real.cos (freq * timeCoordinate 0 (x + h • timeVector 0)) : ℂ) * ψ x =
        (Real.cos (freq * h) : ℂ) *
          ((Real.cos (freq * timeCoordinate 0 x) : ℂ) * ψ x) -
        (Real.sin (freq * h) : ℂ) *
          ((Real.sin (freq * timeCoordinate 0 x) : ℂ) * ψ x)
      rw [htime]
      have he : freq * (timeCoordinate 0 x + h) =
          freq * timeCoordinate 0 x + freq * h := by ring
      rw [he, Real.cos_add]
      push_cast
      ring
    calc
      _ = ∫ x, c (x + h • timeVector 0) * ψ x := by
        rw [← integral_add_right_eq_self
          (fun x : FourierSpace 0 => c x * ψ (x - h • timeVector 0))
          (h • timeVector 0)]
        congr 1 with x
        simp
      _ = ∫ x, ((Real.cos (freq * h) : ℂ) * (c x * ψ x) -
          (Real.sin (freq * h) : ℂ) * (s x * ψ x)) := by
        apply integral_congr_ae
        exact ae_of_all _ hpoint
      _ = _ := by
        rw [integral_sub (hJI.const_mul (Real.cos (freq * h) : ℂ))
          (hKI.const_mul (Real.sin (freq * h) : ℂ)), integral_const_mul, integral_const_mul]
  have hkernelProd := fcond_integrable_testKernelIntegrand_prod ψ hcψ
  have hcmeasProd :
      AEStronglyMeasurable (fun p : FourierSpace 0 × ℝ => c p.1)
        ((volume : Measure (FourierSpace 0)).prod volume) := by
    fun_prop
  have hcbdProd : ∀ᵐ p ∂((volume : Measure (FourierSpace 0)).prod (volume : Measure ℝ)),
      ‖c p.1‖ ≤ 1 := by
    filter_upwards [ae_of_all _ fun p => Real.abs_cos_le_one (freq * timeCoordinate 0 p.1)] with p hp
    change ‖(Real.cos (freq * timeCoordinate 0 p.1) : ℂ)‖ ≤ 1
    rw [Complex.norm_real]
    exact hp
  have hprod :
      Integrable (Function.uncurry fun x h => c x * testKernelIntegrand ψ x h)
        ((volume : Measure (FourierSpace 0)).prod (volume : Measure ℝ)) :=
    hkernelProd.bdd_mul hcmeasProd hcbdProd
  have hpair :
      (∫ x, c x * testKernel ψ x) =
        (kappa : ℂ) * ∫ h, ∫ x, c x * testKernelIntegrand ψ x h := by
    change (∫ x, c x * ((kappa : ℂ) * ∫ h, testKernelIntegrand ψ x h)) = _
    calc
      _ = ∫ x, (kappa : ℂ) * (c x * ∫ h, testKernelIntegrand ψ x h) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring
      _ = (kappa : ℂ) * ∫ x, c x * ∫ h, testKernelIntegrand ψ x h := by
        rw [integral_const_mul]
      _ = (kappa : ℂ) * ∫ x, ∫ h, c x * testKernelIntegrand ψ x h := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ fun x =>
          (integral_const_mul (c x) (fun h => testKernelIntegrand ψ x h)).symm
      _ = (kappa : ℂ) * ∫ h, ∫ x, c x * testKernelIntegrand ψ x h := by
        rw [integral_integral_swap hprod]
  have hsection (h : ℝ) :
      (∫ x, c x * testKernelIntegrand ψ x h) =
        (((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
          (((1 - Real.cos (freq * h) : ℝ) : ℂ) * J +
            ((Real.sin (freq * h) : ℝ) : ℂ) * K)) := by
    have hdiff (x : FourierSpace 0) :
        c x * (ψ x - ψ (x - h • timeVector 0)) =
          c x * ψ x - c x * ψ (x - h • timeVector 0) := by ring
    have hbase :
        (∫ x, c x * (ψ x - ψ (x - h • timeVector 0))) =
          J - ((Real.cos (freq * h) : ℂ) * J - (Real.sin (freq * h) : ℂ) * K) := by
      rw [integral_congr_ae (ae_of_all _ hdiff), integral_sub hJI (hshiftCosI h), hshift h]
    calc
      _ = ∫ x, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
          (c x * (ψ x - ψ (x - h • timeVector 0))) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          simp [testKernelIntegrand]
          ring
      _ = ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
          ∫ x, c x * (ψ x - ψ (x - h • timeVector 0)) := by rw [integral_const_mul]
      _ = _ := by rw [hbase]; push_cast; ring
  let τ : ℝ := freq / (2 * Real.pi)
  have hfreq : 2 * Real.pi * τ = freq := by
    dsimp [τ]
    field_simp
  have hdecomp (h : ℝ) :
      (((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) *
          (((1 - Real.cos (freq * h) : ℝ) : ℂ) * J +
            ((Real.sin (freq * h) : ℝ) : ℂ) * K)) =
        (frequencyIntegrand τ h : ℂ) * J + (sineIntegrand τ h : ℂ) * K := by
    rw [frequencyIntegrand, sineIntegrand]
    have hangle : 2 * Real.pi * τ * h = freq * h := by rw [hfreq]
    rw [hangle]
    push_cast
    ring
  have hsectionIntegral :
      (∫ h, ∫ x, c x * testKernelIntegrand ψ x h) =
        ∫ h, (frequencyIntegrand τ h : ℂ) * J + (sineIntegrand τ h : ℂ) * K := by
    apply integral_congr_ae
    exact ae_of_all _ fun h => (hsection h).trans (hdecomp h)
  have hfreqI : Integrable (fun h => (frequencyIntegrand τ h : ℂ)) volume :=
    (integrable_frequencyIntegrand τ).ofReal
  have hsineI : Integrable (fun h => (sineIntegrand τ h : ℂ)) volume :=
    (integrable_sineIntegrand τ).ofReal
  have hsineC : (∫ h, (sineIntegrand τ h : ℂ)) = 0 := by
    rw [integral_complex_ofReal, integral_sineIntegrand]
    simp
  have houter :
      (∫ h, (frequencyIntegrand τ h : ℂ) * J + (sineIntegrand τ h : ℂ) * K) =
        (∫ h, (frequencyIntegrand τ h : ℂ)) * J := by
    rw [integral_add (hfreqI.mul_const J) (hsineI.mul_const K),
      integral_mul_const, integral_mul_const, hsineC, zero_mul, add_zero]
  have hmultiplier :
      (kappa : ℂ) * (∫ h, (frequencyIntegrand τ h : ℂ)) =
        ((|τ| ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal]
    simpa only [Complex.ofReal_mul] using
      congrArg Complex.ofReal (kappa_mul_integral_frequencyIntegrand τ)
  have hbase : |τ| = |freq| / (2 * Real.pi) := by
    dsimp [τ]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hroot : |τ| ^ (1 / 2 : ℝ) = Real.sqrt (|freq| / (2 * Real.pi)) := by
    rw [Real.sqrt_eq_rpow, ← hbase]
  calc
    (∫ x, c x * testKernel ψ x) =
        ((|τ| ^ (1 / 2 : ℝ) : ℝ) : ℂ) * J := by
      rw [hpair, hsectionIntegral, houter, ← mul_assoc, hmultiplier]
    _ = (Real.sqrt (|freq| / (2 * Real.pi)) : ℂ) *
        ∫ x, (Real.cos (freq * timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
      rw [hroot]
      congr 1

end ParabolicRectifiability.Examples
