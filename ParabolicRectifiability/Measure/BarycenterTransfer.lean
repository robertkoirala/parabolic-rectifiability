import ParabolicRectifiability.Geometry.ModelSpace
import ParabolicRectifiability.Measure.SpatialMoments
import Mathlib.Analysis.Convex.Integral

/-!
# Space-time barycenters of bounded restrictions

The barycenter is taken in ordinary coordinates and returned to the actual
parabolic space. Only the mass of the restricted set is assumed finite.
Normalization of that restriction makes it a probability measure, so the
existing fixed-model convexity gives Jensen before any infimum over models.
The spatial radius of a closed cylinder is `R`, whereas its time radius is `R²`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

variable {n k : ℕ} {T : FamilyKind}

/-- The ordinary coordinate barycenter, as a point of parabolic space.
This does not redefine `SpatialSource.barycenter`, which is spatial only. -/
def spaceTimeBarycenter (ν : Measure (Space n)) (C : Set (Space n)) : Space n :=
  (coordinatesHomeomorph n).symm
    ((ν C).toReal⁻¹ • ∫ w in C, coordinatesHomeomorph n w ∂ν)

/-- Probability normalization of a restriction with nonzero finite mass. -/
def normalizedRestriction (ν : Measure (Space n)) (C : Set (Space n)) :
    Measure (Space n) := (ν C)⁻¹ • ν.restrict C

theorem isProbabilityMeasure_normalizedRestriction (ν : Measure (Space n))
    (C : Set (Space n)) (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤) :
    IsProbabilityMeasure (normalizedRestriction ν C) := by
  constructor
  simp [normalizedRestriction, ENNReal.inv_mul_cancel h0 hfin]

/-- Boundedness and finite restricted mass suffice for every continuous integrand;
no local or global finiteness assumption is made on `ν`. -/
theorem integrableOn_continuous_of_bounded {E : Type*} [NormedAddCommGroup E]
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤)
    {f : Space n → E} (hf : Continuous f) : IntegrableOn f C ν :=
  hf.continuousOn.integrableOn_of_subset_isCompact hbound.isCompact_closure
    hC subset_closure hfin

theorem integrableOn_coordinates (ν : Measure (Space n)) {C : Set (Space n)}
    (hC : MeasurableSet C) (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤) :
    IntegrableOn (coordinatesHomeomorph n) C ν :=
  integrableOn_continuous_of_bounded ν hC hbound hfin (coordinatesHomeomorph n).continuous

theorem integrableOn_spatial (ν : Measure (Space n)) {C : Set (Space n)}
    (hC : MeasurableSet C) (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤) :
    IntegrableOn (fun w => w.1) C ν :=
  integrableOn_continuous_of_bounded ν hC hbound hfin continuous_spatial

theorem integrableOn_time (ν : Measure (Space n)) {C : Set (Space n)}
    (hC : MeasurableSet C) (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤) :
    IntegrableOn (fun w => w.2.val) C ν :=
  integrableOn_continuous_of_bounded ν hC hbound hfin continuous_time

theorem integrableOn_spatial_coordinate (ν : Measure (Space n)) {C : Set (Space n)}
    (hC : MeasurableSet C) (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤) (i : Fin n) :
    IntegrableOn (fun w => w.1 i) C ν :=
  integrableOn_continuous_of_bounded ν hC hbound hfin (by fun_prop)

theorem integrableOn_modelRealCost_of_bounded (ν : Measure (Space n)) {C : Set (Space n)}
    (hC : MeasurableSet C) (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤)
    (L : Models n k T) : IntegrableOn (modelRealCost L) C ν :=
  integrableOn_continuous_of_bounded ν hC hbound hfin
    (continuous_modelRealCost.comp (continuous_const.prodMk continuous_id))

theorem lintegral_modelCost_eq_ofReal_integral
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤) (L : Models n k T) :
    (∫⁻ w in C, modelCost L w ∂ν) = ENNReal.ofReal (∫ w in C, modelRealCost L w ∂ν) := by
  simp only [modelCost_eq_ofReal]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_modelRealCost_of_bounded ν hC hbound hfin L)
    (Filter.Eventually.of_forall (modelRealCost_nonneg L))).symm

theorem lintegral_modelCost_lt_top_of_bounded
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (hfin : ν C ≠ ⊤) (L : Models n k T) :
    (∫⁻ w in C, modelCost L w ∂ν) < ⊤ := by
  rw [lintegral_modelCost_eq_ofReal_integral ν hC hbound hfin L]
  exact ENNReal.ofReal_lt_top

theorem coordinates_spaceTimeBarycenter (ν : Measure (Space n)) (C : Set (Space n)) :
    coordinatesHomeomorph n (spaceTimeBarycenter ν C) =
      (ν C).toReal⁻¹ • ∫ w in C, coordinatesHomeomorph n w ∂ν :=
  (coordinatesHomeomorph n).apply_symm_apply _

theorem spaceTimeBarycenter_spatial (ν : Measure (Space n)) (C : Set (Space n))
    (hi : IntegrableOn (coordinatesHomeomorph n) C ν) :
    (spaceTimeBarycenter ν C).1 = (ν C).toReal⁻¹ • ∫ w in C, w.1 ∂ν := by
  change (ν C).toReal⁻¹ • (∫ w in C, coordinatesHomeomorph n w ∂ν).1 = _
  rw [fst_integral hi]
  rfl

theorem spaceTimeBarycenter_time (ν : Measure (Space n)) (C : Set (Space n))
    (hi : IntegrableOn (coordinatesHomeomorph n) C ν) :
    (spaceTimeBarycenter ν C).2.val = (ν C).toReal⁻¹ * ∫ w in C, w.2.val ∂ν := by
  change (ν C).toReal⁻¹ * (∫ w in C, coordinatesHomeomorph n w ∂ν).2 = _
  rw [snd_integral hi]
  rfl

/-- Compatibility with the previously defined spatial-only barycenter, including
the zero-mass convention. -/
theorem SpatialSource.spaceTimeBarycenter_spatial (S : SpatialSource n) :
    (spaceTimeBarycenter S.measure univ).1 = S.barycenter := by
  rw [ParabolicRectifiability.spaceTimeBarycenter_spatial]
  · simp [SpatialSource.barycenter, SpatialSource.mass, measureReal_def]
  · simpa using S.integrable (coordinatesHomeomorph n).continuous

theorem integral_normalizedRestriction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : Measure (Space n)) (C : Set (Space n)) (f : Space n → E) :
    (∫ w, f w ∂normalizedRestriction ν C) = (ν C).toReal⁻¹ • ∫ w in C, f w ∂ν := by
  rw [normalizedRestriction, integral_smul_measure, ENNReal.toReal_inv]

theorem integral_coordinates_normalizedRestriction (ν : Measure (Space n))
    (C : Set (Space n)) :
    (∫ w, coordinatesHomeomorph n w ∂normalizedRestriction ν C) =
      coordinatesHomeomorph n (spaceTimeBarycenter ν C) := by
  rw [integral_normalizedRestriction, coordinates_spaceTimeBarycenter]

/-- Jensen for the actual probability normalization of the restricted source. -/
theorem modelRealCost_spaceTimeBarycenter_le_normalizedIntegral
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤)
    (L : Models n k T) :
    modelRealCost L (spaceTimeBarycenter ν C) ≤
      ∫ w, modelRealCost L w ∂normalizedRestriction ν C := by
  let _ := isProbabilityMeasure_normalizedRestriction ν C h0 hfin
  have hi : Integrable (coordinatesHomeomorph n) (normalizedRestriction ν C) :=
    (integrableOn_coordinates ν hC hbound hfin).smul_measure (ENNReal.inv_ne_top.mpr h0)
  have hgi : Integrable (modelRealCost L) (normalizedRestriction ν C) :=
    (integrableOn_modelRealCost_of_bounded ν hC hbound hfin L).smul_measure
      (ENNReal.inv_ne_top.mpr h0)
  have hc : Continuous (fun y : Coordinates n =>
      modelRealCost L ((coordinatesHomeomorph n).symm y)) :=
    continuous_modelRealCost.comp
      (continuous_const.prodMk (coordinatesHomeomorph n).symm.continuous)
  have h := (convexOn_modelRealCost L).map_integral_le
    (μ := normalizedRestriction ν C) hc.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hi
    (by simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hgi)
  simpa only [integral_coordinates_normalizedRestriction,
    Homeomorph.symm_apply_apply] using h

/-- Unnormalized fixed-model Jensen with real mass and real squared cost. -/
theorem mass_mul_modelRealCost_spaceTimeBarycenter_le
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤)
    (L : Models n k T) :
    (ν C).toReal * modelRealCost L (spaceTimeBarycenter ν C) ≤
      ∫ w in C, modelRealCost L w ∂ν := by
  have h := modelRealCost_spaceTimeBarycenter_le_normalizedIntegral ν hC hbound h0 hfin L
  rw [integral_normalizedRestriction, smul_eq_mul] at h
  have hm : 0 < (ν C).toReal := ENNReal.toReal_pos h0 hfin
  simpa [← mul_assoc, ne_of_gt hm] using mul_le_mul_of_nonneg_left h hm.le

/-- Unnormalized fixed-model Jensen in the same extended-real convention as beta.
The family parameter includes horizontal, vertical and mixed actual models. -/
theorem mass_mul_modelCost_spaceTimeBarycenter_le
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (hbound : Bornology.IsBounded C) (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤)
    (L : Models n k T) :
    ν C * modelCost L (spaceTimeBarycenter ν C) ≤ ∫⁻ w in C, modelCost L w ∂ν := by
  have h := ENNReal.ofReal_le_ofReal
    (mass_mul_modelRealCost_spaceTimeBarycenter_le ν hC hbound h0 hfin L)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_modelRealCost_of_bounded ν hC hbound hfin L)
      (Filter.Eventually.of_forall (modelRealCost_nonneg L))] at h
  simpa only [modelCost_eq_ofReal] using h

/-- Coordinate form of a parabolic closed ball. Time has radius `R²`. -/
theorem mem_closedBall_iff_coordinate_bounds (w z : Space n) {R : ℝ} (hR : 0 ≤ R) :
    w ∈ Metric.closedBall z R ↔ ‖w.1 - z.1‖ ≤ R ∧ |w.2.val - z.2.val| ≤ R ^ 2 := by
  rcases w with ⟨x, ⟨t⟩⟩
  rcases z with ⟨y, ⟨s⟩⟩
  exact mem_closedBall_point y x s t R hR

theorem ae_mem_normalizedRestriction (ν : Measure (Space n))
    {C : Set (Space n)} (hC : MeasurableSet C) :
    ∀ᵐ w ∂normalizedRestriction ν C, w ∈ C :=
  Measure.ae_smul_measure (ae_restrict_mem hC) _

/-- The two estimates have distinct scales: spatial norm at most `R`, absolute
time displacement at most `R²`. This also covers the degenerate radius zero. -/
theorem spaceTimeBarycenter_coordinate_bounds
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤) (z : Space n) {R : ℝ} (hR : 0 ≤ R)
    (hsub : C ⊆ Metric.closedBall z R) :
    ‖(spaceTimeBarycenter ν C).1 - z.1‖ ≤ R ∧
      |(spaceTimeBarycenter ν C).2.val - z.2.val| ≤ R ^ 2 := by
  let _ := isProbabilityMeasure_normalizedRestriction ν C h0 hfin
  have hi : Integrable (coordinatesHomeomorph n) (normalizedRestriction ν C) :=
    (integrableOn_coordinates ν hC (Metric.isBounded_closedBall.subset hsub)
      hfin).smul_measure (ENNReal.inv_ne_top.mpr h0)
  have hae := (ae_mem_normalizedRestriction ν hC).mono fun w hw =>
    (mem_closedBall_iff_coordinate_bounds w z hR).mp (hsub hw)
  have hs := (convex_closedBall z.1 R).integral_mem (μ := normalizedRestriction ν C)
    Metric.isClosed_closedBall (hae.mono fun w hw => by
      rw [Metric.mem_closedBall, dist_eq_norm]
      change ‖w.1 - z.1‖ ≤ R
      exact hw.1) hi.fst
  have ht := (convex_Icc (z.2.val - R ^ 2) (z.2.val + R ^ 2)).integral_mem
    (μ := normalizedRestriction ν C) isClosed_Icc (hae.mono fun w hw => by
      change z.2.val - R ^ 2 ≤ w.2.val ∧ w.2.val ≤ z.2.val + R ^ 2
      have h := abs_le.mp hw.2
      exact ⟨by linarith [h.1], by linarith [h.2]⟩) hi.snd
  have he := integral_coordinates_normalizedRestriction ν C
  have hsp := congrArg Prod.fst he
  have htp := congrArg Prod.snd he
  rw [fst_integral hi] at hsp
  rw [snd_integral hi] at htp
  change (∫ w, w.1 ∂normalizedRestriction ν C) = (spaceTimeBarycenter ν C).1 at hsp
  change (∫ w, w.2.val ∂normalizedRestriction ν C) =
    (spaceTimeBarycenter ν C).2.val at htp
  change (∫ w, w.1 ∂normalizedRestriction ν C) ∈ Metric.closedBall z.1 R at hs
  change (∫ w, w.2.val ∂normalizedRestriction ν C) ∈
    Icc (z.2.val - R ^ 2) (z.2.val + R ^ 2) at ht
  rw [hsp, Metric.mem_closedBall, dist_eq_norm] at hs
  rw [htp] at ht
  exact ⟨hs, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩

theorem spaceTimeBarycenter_mem_closedBall
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤) (z : Space n) {R : ℝ} (hR : 0 ≤ R)
    (hsub : C ⊆ Metric.closedBall z R) :
    spaceTimeBarycenter ν C ∈ Metric.closedBall z R :=
  (mem_closedBall_iff_coordinate_bounds _ z hR).mpr
    (spaceTimeBarycenter_coordinate_bounds ν hC h0 hfin z hR hsub)

/-- The scaled version with radius `ε r`, retaining the squared time radius explicitly. -/
theorem spaceTimeBarycenter_mem_scaled_closedBall
    (ν : Measure (Space n)) {C : Set (Space n)} (hC : MeasurableSet C)
    (h0 : ν C ≠ 0) (hfin : ν C ≠ ⊤) (z : Space n) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hsub : C ⊆ Metric.closedBall z (ε * r)) :
    spaceTimeBarycenter ν C ∈ Metric.closedBall z (ε * r) ∧
      ‖(spaceTimeBarycenter ν C).1 - z.1‖ ≤ ε * r ∧
      |(spaceTimeBarycenter ν C).2.val - z.2.val| ≤ (ε * r) ^ 2 :=
  ⟨spaceTimeBarycenter_mem_closedBall ν hC h0 hfin z (mul_pos hε hr).le hsub,
    spaceTimeBarycenter_coordinate_bounds ν hC h0 hfin z (mul_pos hε hr).le hsub⟩

end ParabolicRectifiability
