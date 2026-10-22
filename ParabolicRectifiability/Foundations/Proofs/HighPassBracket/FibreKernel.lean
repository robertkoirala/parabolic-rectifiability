import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel

/-! # Fibres of the test kernel

Proofs of `fhpa_ae_fibre_halfTimeDeriv` and `fhpa_integrable_mul_testKernel`:

* `fhpa_ae_fibre_halfTimeDeriv_proof`: for every complex Schwartz test `ψ`, for almost
  every time `t`, the spatial fibre of the chosen `L²` representative `halfTimeDeriv m ψ` agrees
  a.e. with the spatial fibre of the pointwise kernel `testKernel ψ`. This is a null-set
  argument: the a.e. identity `testKernel_ae_halfTimeDeriv` on `FourierSpace m` is pulled back
  along the measure-preserving map `(t,u) ↦ toLp 2 (u,t)` from `volume.prod volume` on
  `ℝ × ℝ^m`, then sliced with time outside (`Measure.ae_ae_of_ae_prod`). No integral is
  interchanged.
* `fhpa_integrable_mul_testKernel_proof`: for a real compact smooth test `φ`, every
  continuous `c` and every time `t`, `u ↦ c u * testKernel φ (u,t)` is integrable: it is
  strongly measurable, and bounded by a constant times the indicator of the compact spatial
  projection `spatialTestSupport` of the test's support, off which the kernel vanishes.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- The coordinate map `(t,u) ↦ toLp 2 (u,t)`, time first, preserves volume from
`volume.prod volume` on `ℝ × ℝ^m` to `FourierSpace m`. -/
theorem fhpab12_timeFirst_measurePreserving (m : ℕ) :
    MeasurePreserving (fun p : ℝ × Spatial m => WithLp.toLp 2 (p.2, p.1))
      ((volume : Measure ℝ).prod (volume : Measure (Spatial m)))
      (volume : Measure (FourierSpace m)) :=
  (fourierCoordinates_symm_measurePreserving_prod m).comp Measure.measurePreserving_swap

/-- The a.e. fibre transfer (the type of `fhpa_ae_fibre_halfTimeDeriv`). -/
theorem fhpa_ae_fibre_halfTimeDeriv_proof {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    ∀ᵐ t : ℝ, (fun u : Spatial m => halfTimeDeriv m ψ (WithLp.toLp 2 (u, t))) =ᵐ[volume]
      fun u => testKernel ψ (WithLp.toLp 2 (u, t)) := by
  have h0 : (halfTimeDeriv m ψ : FourierSpace m → ℂ) =ᵐ[volume] testKernel ψ :=
    (testKernel_ae_halfTimeDeriv ψ).symm
  have h1 := (fhpab12_timeFirst_measurePreserving m).quasiMeasurePreserving.ae_eq_comp h0
  exact Measure.ae_ae_of_ae_prod h1

/-- The spatial section `u ↦ toLp 2 (u,t)` is measurable. -/
theorem fhpab12_measurable_section (m : ℕ) (t : ℝ) :
    Measurable fun u : Spatial m => (WithLp.toLp 2 (u, t) : FourierSpace m) :=
  (fourierCoordinatesMeasurableEquiv m).symm.measurable.comp (measurable_id.prodMk measurable_const)

/-- Spatial integrability against the test kernel (the type of
`fhpa_integrable_mul_testKernel`). -/
theorem fhpa_integrable_mul_testKernel_proof {m : ℕ} (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (c : Spatial m → ℂ) (hcont : Continuous c)
    (t : ℝ) :
    Integrable (fun u : Spatial m => c u * testKernel (realCompactTest φ hφ hc)
      (WithLp.toLp 2 (u, t))) := by
  set ψ := realCompactTest φ hφ hc
  have hψc : HasCompactSupport ψ := by
    change IsCompact (tsupport ψ)
    rw [tsupport_realCompactTest]
    exact hc
  set A := spatialTestSupport ψ
  have hA : IsCompact A := isCompact_spatialTestSupport ψ hψc
  obtain ⟨C, hC⟩ := hA.exists_bound_of_continuousOn hcont.continuousOn
  set B := FractionalKernel.kappa * testKernelControl ψ * ∫ h, cancellationWeight h
  have hmeas : AEStronglyMeasurable (fun u : Spatial m => c u * testKernel ψ
      (WithLp.toLp 2 (u, t))) volume :=
    hcont.aestronglyMeasurable.mul
      ((stronglyMeasurable_testKernel ψ).comp_measurable
        (fhpab12_measurable_section m t)).aestronglyMeasurable
  have hg : Integrable (A.indicator fun _ => C * B) (volume : Measure (Spatial m)) :=
    (integrable_indicator_iff hA.measurableSet).2
      (integrableOn_const hA.measure_lt_top.ne)
  refine hg.mono' hmeas (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ A
  · rw [Set.indicator_of_mem hu, norm_mul]
    exact mul_le_mul (hC u hu) (norm_testKernel_le ψ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC u hu))
  · rw [Set.indicator_of_notMem hu, testKernel_eq_zero_of_notMem_spatialTestSupport ψ hu t,
      mul_zero, norm_zero]

end ParabolicRectifiability.Foundations
