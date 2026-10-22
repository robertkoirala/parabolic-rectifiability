import ParabolicRectifiability.Examples.Proofs.ExponentBelow.Statements
import ParabolicRectifiability.Foundations.Statements.HighPassBracket

/-! # The zero-dimensional half-time representation adapter

The time coordinate identifies `FourierSpace 0` with `ℝ` and preserves volume.
The high-pass bracket is therefore the ordinary time integrand. Its symmetric
windows converge to the bracket integral, and the assumed pairing identity
identifies that integral with the target test pairing. -/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff NNReal Topology SchwartzMap

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability
open ParabolicRectifiability.Foundations
open ParabolicRectifiability.HalfTimeDerivative

private def e2_rep3_timeHomeomorph : FourierSpace 0 ≃ₜ ℝ where
  toFun := timeCoordinate 0
  invFun := fun t => WithLp.toLp 2 (0, t)
  left_inv := by
    intro x
    apply (fourierCoordinatesHomeomorph 0).injective
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv := by
    intro t
    simp
  continuous_toFun := continuous_timeCoordinate 0
  continuous_invFun := by
    change Continuous (fun t : ℝ => WithLp.toLp 2 ((0 : Spatial 0), t))
    exact (fourierCoordinatesHomeomorph 0).symm.continuous.comp
      (continuous_const.prodMk continuous_id)

private theorem e2_rep3_timeMeasurePreserving :
    MeasurePreserving e2_rep3_timeHomeomorph (volume : Measure (FourierSpace 0))
      (volume : Measure ℝ) := by
  have hprob : IsProbabilityMeasure (volume : Measure (Spatial 0)) := by
    rw [volume_euclideanSpace_eq_dirac (Fin 0)]
    infer_instance
  let := hprob
  have hcomp : MeasurePreserving
      (Prod.snd ∘ fourierCoordinatesMeasurableEquiv 0)
      (volume : Measure (FourierSpace 0)) (volume : Measure ℝ) :=
    measurePreserving_snd.comp (fourierCoordinates_measurePreserving_prod 0)
  have heq : (e2_rep3_timeHomeomorph : FourierSpace 0 → ℝ) =
      Prod.snd ∘ fourierCoordinatesMeasurableEquiv 0 := by
    funext x
    rfl
  refine ⟨e2_rep3_timeHomeomorph.measurable, ?_⟩
  rw [heq]
  exact hcomp.map_eq

private theorem e2_rep3_tendsto_window {f : ℝ → ℂ} (hf : Integrable f volume) :
    Tendsto (fun R : ℝ => ∫ t in Set.Icc (-R) R, f t) atTop
      (𝓝 (∫ t, f t)) := by
  have hmono : Monotone (fun R : ℝ => Set.Icc (-R) R) := by
    intro R S hRS
    exact Set.Icc_subset_Icc (by linarith) hRS
  have hU : (⋃ R : ℝ, Set.Icc (-R) R) = Set.univ := by
    refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.mpr ⟨|t|, ?_⟩
    exact ⟨neg_abs_le t, le_abs_self t⟩
  have hint : IntegrableOn f (⋃ R : ℝ, Set.Icc (-R) R) := by
    rw [hU]
    exact hf.integrableOn
  have h := tendsto_setIntegral_of_monotone (μ := volume)
    (fun R : ℝ => measurableSet_Icc) hmono hint
  rwa [hU, setIntegral_univ] at h

private theorem e2_rep3_bracket_eq (F : ℝ → ℝ) (ψ : 𝓢(FourierSpace 0, ℂ)) (t : ℝ) :
    halfTimeSpatialBracket (fun x : FourierSpace 0 => F (timeCoordinate 0 x)) ψ t =
      (F t : ℂ) * halfTimeDeriv 0 ψ (WithLp.toLp 2 (0, t)) := by
  rw [halfTimeSpatialBracket]
  rw [integral_unique]
  simp [halfTimeSpatialIntegrand, volume_euclideanSpace_eq_dirac (Fin 0)]
  apply Or.inl
  congr 1
  apply (fourierCoordinatesHomeomorph 0).injective
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

theorem e2_zeroDim_representation_proof :
    HalfTimeBracketIntegrableStatement → E2ZeroDimRepresentationStatement := by
  intro hhp F g C hmod hloc hpair
  have hC : 0 ≤ C := by
    have h := hmod 1 0
    have h' : |F 1 - F 0| ≤ C := by simpa using h
    exact (abs_nonneg _).trans h'
  have hG : ∃ L : ℝ≥0,
      LipschitzWith L ((fun x : FourierSpace 0 => F (timeCoordinate 0 x)) ∘
        (fourierToParabolic 0).symm) := by
    refine ⟨Real.toNNReal C, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
    have hp : timeCoordinate 0 ((fourierToParabolic 0).symm p) = p.2.val := by
      simp [fourierToParabolic_symm_apply]
    have hq : timeCoordinate 0 ((fourierToParabolic 0).symm q) = q.2.val := by
      simp [fourierToParabolic_symm_apply]
    have htime : Real.sqrt |p.2.val - q.2.val| ≤ dist p q := by
      have hp' : point p.1 p.2.val = p := by cases p; rfl
      have hq' : point q.1 q.2.val = q := by cases q; rfl
      rw [← hp', ← hq', dist_point]
      exact le_max_right _ _
    have hmod' := hmod p.2.val q.2.val
    change dist (F (timeCoordinate 0 ((fourierToParabolic 0).symm p)))
        (F (timeCoordinate 0 ((fourierToParabolic 0).symm q))) ≤ _
    rw [Real.dist_eq, hp, hq]
    calc
      |F p.2.val - F q.2.val| ≤ C * Real.sqrt |p.2.val - q.2.val| := hmod'
      _ ≤ C * dist p q := mul_le_mul_of_nonneg_left htime hC
      _ = (Real.toNNReal C : ℝ) * dist p q := by rw [Real.coe_toNNReal C hC]
  have hgloc : LocallyIntegrable
      (fun x : FourierSpace 0 => g (timeCoordinate 0 x)) (volume : Measure (FourierSpace 0)) := by
    have hmap : LocallyIntegrable g
        (Measure.map e2_rep3_timeHomeomorph (volume : Measure (FourierSpace 0))) := by
      rw [e2_rep3_timeMeasurePreserving.map_eq]
      exact hloc
    exact (locallyIntegrable_map_homeomorph e2_rep3_timeHomeomorph).mp hmap
  unfold RepresentsHomogeneousHalfTimeDerivative
  refine ⟨hgloc, ?_⟩
  intro φ hφ hc hzero
  let ψ := realCompactTest φ hφ hc
  let G : FourierSpace 0 → ℝ := fun x => F (timeCoordinate 0 x)
  have hFhp := hhp 0 G hG φ hφ hc hzero
  rcases hFhp with ⟨hinner, hbracket⟩
  refine ⟨hinner, fun R => hbracket.integrableOn, ?_⟩
  have hwindow : Tendsto (halfTimeWindowPairing G ψ) atTop
      (𝓝 (∫ t, halfTimeSpatialBracket G ψ t)) := by
    change Tendsto (fun R : ℝ => ∫ t in Set.Icc (-R) R,
      halfTimeSpatialBracket G (realCompactTest φ hφ hc) t) atTop
        (𝓝 (∫ t, halfTimeSpatialBracket G (realCompactTest φ hφ hc) t))
    exact e2_rep3_tendsto_window hbracket
  have hkernel : ∀ᵐ t : ℝ,
      halfTimeDeriv 0 ψ (WithLp.toLp 2 (0, t)) = testKernel ψ (WithLp.toLp 2 (0, t)) := by
    have hmp : MeasurePreserving e2_rep3_timeHomeomorph.toMeasurableEquiv
        (volume : Measure (FourierSpace 0)) (volume : Measure ℝ) := by
      exact ⟨e2_rep3_timeHomeomorph.toMeasurableEquiv.measurable,
        e2_rep3_timeMeasurePreserving.map_eq⟩
    have hmpInv := MeasurePreserving.symm e2_rep3_timeHomeomorph.toMeasurableEquiv hmp
    have hmpInv' : MeasurePreserving e2_rep3_timeHomeomorph.toMeasurableEquiv.symm
        (volume : Measure ℝ) (volume : Measure (FourierSpace 0)) := by
      simpa using hmpInv
    have h := hmpInv'.quasiMeasurePreserving.ae (testKernel_ae_halfTimeDeriv ψ).symm
    have hsymm (t : ℝ) :
        e2_rep3_timeHomeomorph.toMeasurableEquiv.symm t = WithLp.toLp 2 (0, t) := rfl
    filter_upwards [h] with t ht
    rw [hsymm] at ht
    exact ht
  have hbracket_eq : ∀ t : ℝ,
      halfTimeSpatialBracket G ψ t =
        (F t : ℂ) * halfTimeDeriv 0 ψ (WithLp.toLp 2 (0, t)) := by
    intro t
    exact e2_rep3_bracket_eq F ψ t
  let q : ℝ → ℂ := fun t =>
    (F t : ℂ) * testKernel ψ (WithLp.toLp 2 (0, t))
  have hqHalf : Integrable (fun t : ℝ =>
      (F t : ℂ) * halfTimeDeriv 0 ψ (WithLp.toLp 2 (0, t))) volume := by
    apply hbracket.congr
    filter_upwards [Filter.Eventually.of_forall hbracket_eq] with t ht
    exact ht
  have hqEq : (fun t : ℝ =>
      (F t : ℂ) * halfTimeDeriv 0 ψ (WithLp.toLp 2 (0, t))) =ᵐ[volume] q := by
    filter_upwards [hkernel] with t ht
    simp [q, ht]
  have hq : Integrable q volume := hqHalf.congr hqEq
  have hpairing_integral :
      (∫ x : FourierSpace 0, (F (timeCoordinate 0 x) : ℂ) * testKernel ψ x) = ∫ t, q t := by
    have hfun : (fun x : FourierSpace 0 =>
        (F (timeCoordinate 0 x) : ℂ) * testKernel ψ x) =
          fun x => q (timeCoordinate 0 x) := by
      funext x
      have hx : WithLp.toLp 2 (0, (WithLp.ofLp x).2) = x := by
        apply (fourierCoordinatesHomeomorph 0).injective
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl
      calc
        (F (timeCoordinate 0 x) : ℂ) * testKernel ψ x =
            (F (timeCoordinate 0 x) : ℂ) *
              testKernel ψ (WithLp.toLp 2 (0, (WithLp.ofLp x).2)) := by rw [← hx]
        _ = q (timeCoordinate 0 x) := rfl
    rw [hfun]
    have hmp : MeasurePreserving e2_rep3_timeHomeomorph.toMeasurableEquiv
        (volume : Measure (FourierSpace 0)) (volume : Measure ℝ) := by
      exact ⟨e2_rep3_timeHomeomorph.toMeasurableEquiv.measurable,
        e2_rep3_timeMeasurePreserving.map_eq⟩
    exact hmp.integral_comp' q
  have hlimit_value :
      (∫ t, halfTimeSpatialBracket G ψ t) =
        ∫ x : FourierSpace 0, (g (timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
    calc
      (∫ t, halfTimeSpatialBracket G ψ t)
          = ∫ t : ℝ, (F t : ℂ) * halfTimeDeriv 0 ψ (WithLp.toLp 2 (0, t)) :=
            integral_congr_ae (Filter.Eventually.of_forall hbracket_eq)
      _ = ∫ t, q t := integral_congr_ae hqEq
      _ = ∫ x : FourierSpace 0, (F (timeCoordinate 0 x) : ℂ) * testKernel ψ x :=
            hpairing_integral.symm
      _ = ∫ x : FourierSpace 0, (g (timeCoordinate 0 x) : ℂ) * (φ x : ℂ) := by
            exact hpair φ hφ hc
  simpa only [hlimit_value] using hwindow

end ParabolicRectifiability.Examples
