import ParabolicRectifiability.Decomposition.Carrier.Transport

/-! # Local similarity covariance of the half-time representation

The theorem `repHalf_comp_fourierSimilarity` (in `Decomposition.Carrier.Transport`)
transports a representation of `D_t^{1/2} H` on the whole space along a parabolic
similarity `Θ = fourierSimilarity q a` written in ordinary Fourier coordinates. Here the
representation is only local, on an open set `Ω`: then `g ∘ Θ` represents
`D_t^{1/2} (a H ∘ Θ)` on the open set `Θ⁻¹ Ω`.

The proof is that of `repHalf_comp_fourierSimilarity`, with two additions:

* a smooth compact test `φ` with `tsupport φ ⊆ Θ⁻¹ Ω` gives the transported test
  `φ' = φ ∘ Θ⁻¹` with `tsupport φ' = Θ (tsupport φ) ⊆ Ω`, so the hypothesis applies to `φ'`;
* local integrability on `Θ⁻¹ Ω` is checked on compact subsets `k`: `Θ k ⊆ Ω` is compact,
  and `Θ` pushes the volume to the constant multiple `a^(m+2)` of the volume.

The kernel identity `K(ψ ∘ Θ) = a⁻¹ (Kψ) ∘ Θ` (`testKernel_comp_fourierSimilarity`)
and the change of variables are as in the global case. At `a = 1` the map `Θ` is the translation
`x ↦ x - (q_x, q_t)`, which is the case used for the local decomposition.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap

open scoped ContDiff in
/-- **Local similarity covariance of `RepHalf`.** If `g` represents `D_t^{1/2} H` on the open
set `Ω`, then `g ∘ Θ` represents `D_t^{1/2} (a H ∘ Θ)` on `Θ⁻¹ Ω`, for the parabolic
similarity `Θ = fourierSimilarity q a` in ordinary Fourier coordinates. -/
theorem rx5_repHalf_comp_fourierSimilarity_local {m : ℕ} (q : Space m) (a : ℝ) (ha : 0 < a)
    {H g : FourierSpace m → ℝ} (hH : MemLp H 2 volume) {Ω : Set (FourierSpace m)}
    (hrep : HalfTimeDerivative.RepHalf hH g Ω) :
    ∃ hH' : MemLp (fun x => a * H (fourierSimilarity q a ha x)) 2 volume,
      HalfTimeDerivative.RepHalf hH' (fun x => g (fourierSimilarity q a ha x))
        (fourierSimilarity q a ha ⁻¹' Ω) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hc : ENNReal.ofReal a ^ (m + 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hMP := measurePreserving_fourierSimilarity q a ha
  have hemb : MeasurableEmbedding (fourierSimilarity q a ha) :=
    (fourierSimilarity q a ha).measurableEmbedding
  have hHe : MemLp (fun x => H (fourierSimilarity q a ha x)) 2 volume :=
    (hH.smul_measure hc).comp_measurePreserving hMP
  have hopen : IsOpen (fourierSimilarity q a ha ⁻¹' Ω) :=
    hrep.1.preimage (fourierSimilarity q a ha).continuous
  refine ⟨hHe.const_mul a, hopen, ?_, ?_⟩
  · rw [locallyIntegrableOn_iff hopen.isLocallyClosed]
    intro k hk hkc
    have h1 : IntegrableOn g (fourierSimilarity q a ha '' k) volume :=
      hrep.2.1.integrableOn_compact_subset (image_subset_iff.mpr hk)
        (hkc.image (fourierSimilarity q a ha).continuous)
    have h2 : IntegrableOn g (fourierSimilarity q a ha '' k)
        (ENNReal.ofReal a ^ (m + 2) • volume) := by
      rw [IntegrableOn, Measure.restrict_smul]
      exact h1.smul_measure hc
    exact (hMP.integrableOn_image hemb).1 h2
  · intro φ hφ hcφ hsφ
    obtain ⟨φ', hφ'def⟩ : ∃ φ' : FourierSpace m → ℝ,
        φ' = fun y => φ ((fourierSimilarity q a ha).symm y) := ⟨_, rfl⟩
    have hφ' : ContDiff ℝ ∞ φ' := by
      rw [hφ'def]
      exact hφ.comp (contDiff_fourierSimilarity_symm q a ha)
    have hφ'c : HasCompactSupport φ' := by
      rw [hφ'def]
      exact hcφ.comp_homeomorph _
    have hφ'e : ∀ x, φ' (fourierSimilarity q a ha x) = φ x := by
      intro x
      simp only [hφ'def, Homeomorph.symm_apply_apply]
    have hφ's : tsupport φ' ⊆ Ω := by
      intro y hy
      rw [hφ'def] at hy
      have h1 : (fourierSimilarity q a ha).symm y ∈ tsupport φ :=
        (tsupport_comp_eq_preimage φ (fourierSimilarity q a ha).symm).subset hy
      have h2 := hsφ h1
      rwa [mem_preimage, Homeomorph.apply_symm_apply] at h2
    have hrep' := hrep.2.2 φ' hφ' hφ'c hφ's
    have hker : ∀ x, HalfTimeDerivative.testKernel
          (HalfTimeDerivative.realCompactTest φ hφ hcφ) x =
        (a : ℂ)⁻¹ * HalfTimeDerivative.testKernel
          (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) (fourierSimilarity q a ha x) := by
      refine testKernel_comp_fourierSimilarity q a ha _ _ fun x => ?_
      rw [HalfTimeDerivative.realCompactTest_apply, HalfTimeDerivative.realCompactTest_apply,
        hφ'e]
    calc (∫ x, (((a * H (fourierSimilarity q a ha x) : ℝ)) : ℂ) *
          HalfTimeDerivative.halfTimeDeriv m (HalfTimeDerivative.realCompactTest φ hφ hcφ) x)
        = ∫ x, ((H (fourierSimilarity q a ha x) : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c)
              (fourierSimilarity q a ha x) := by
          refine integral_congr_ae ?_
          filter_upwards [HalfTimeDerivative.testKernel_ae_halfTimeDeriv
            (HalfTimeDerivative.realCompactTest φ hφ hcφ)] with x hx
          rw [← hx, hker x, Complex.ofReal_mul, mul_mul_mul_comm, mul_inv_cancel₀ ha', one_mul]
      _ = ∫ y, ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y
              ∂(ENNReal.ofReal a ^ (m + 2) • volume) :=
          hMP.integral_comp hemb (fun y => ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y)
      _ = (ENNReal.ofReal a ^ (m + 2)).toReal • ∫ y, ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.testKernel (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y :=
          integral_smul_measure _ _
      _ = (ENNReal.ofReal a ^ (m + 2)).toReal • ∫ y, ((H y : ℝ) : ℂ) *
            HalfTimeDerivative.halfTimeDeriv m
              (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c) y := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [HalfTimeDerivative.testKernel_ae_halfTimeDeriv
            (HalfTimeDerivative.realCompactTest φ' hφ' hφ'c)] with y hy
          rw [hy]
      _ = (ENNReal.ofReal a ^ (m + 2)).toReal • ∫ y, ((g y : ℝ) : ℂ) * ((φ' y : ℝ) : ℂ) := by
          rw [hrep']
      _ = ∫ y, ((g y : ℝ) : ℂ) * ((φ' y : ℝ) : ℂ) ∂(ENNReal.ofReal a ^ (m + 2) • volume) :=
          (integral_smul_measure _ _).symm
      _ = ∫ x, ((g (fourierSimilarity q a ha x) : ℝ) : ℂ) *
            ((φ' (fourierSimilarity q a ha x) : ℝ) : ℂ) :=
          (hMP.integral_comp hemb (fun y => ((g y : ℝ) : ℂ) * ((φ' y : ℝ) : ℂ))).symm
      _ = ∫ x, ((g (fourierSimilarity q a ha x) : ℝ) : ℂ) * ((φ x : ℝ) : ℂ) := by
          simp only [hφ'e]

end ParabolicRectifiability
