import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Geometry.SubspaceCoordinates

/-! # Transport of affine errors to ordinary coordinates

The intrinsic vertical base `W × Time` and the coordinate base `ℝ^(rank W) × Time` are
identified by the parabolic isometry `Φ = subspaceParabolicIsometry W`, which applies the
orthonormal spatial coordinates `Λ : W ≃ₗᵢ ℝ^(rank W)` and fixes time. `Φ` preserves balls
and carries the intrinsic volume to the ordinary volume (`subspaceParabolic_measurePreserving`).
Spatial slopes correspond bijectively through `B ↦ B ∘ Λ`, and the homogeneous dimensions
`rank W + 2` of the two bases coincide, so every squared affine error, trace error and
affine Carleson integral is preserved.

The change of variables below is for lower integrals of arbitrary (not necessarily
measurable) integrands over arbitrary sets: `Φ` is a measurable equivalence.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

variable {n : ℕ}

/-- The homogeneous dimensions of `W × Time` and `ℝ^(rank W) × Time` coincide. -/
theorem baseDimension_spatial_finrank (W : Submodule ℝ (Spatial n)) :
    baseDimension (Spatial (Module.finrank ℝ W)) = baseDimension W := by
  simp only [baseDimension, finrank_euclideanSpace_fin]

/-- Lower integrals over arbitrary sets transport along the measurable parabolic isometry,
for an arbitrary measure on the intrinsic base and an arbitrary integrand. -/
theorem setLIntegral_comp_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    (ν : Measure (SubspaceSpace W)) (S : Set (SubspaceSpace W))
    (g : Space (Module.finrank ℝ W) → ℝ≥0∞) :
    ∫⁻ z in S, g (subspaceParabolicIsometry W z) ∂ν =
      ∫⁻ w in subspaceParabolicIsometry W '' S, g w
        ∂(ν.map (subspaceParabolicMeasurableEquiv W)) := by
  set e := subspaceParabolicMeasurableEquiv W
  have he : (e : SubspaceSpace W → Space (Module.finrank ℝ W)) = subspaceParabolicIsometry W :=
    rfl
  rw [← he, e.restrict_map, e.preimage_image, lintegral_map_equiv]

/-- Fit integrals transport along `Φ`: the slope `B` on `ℝ^(rank W)` corresponds to `B ∘ Λ`. -/
theorem affineFitIntegral_map_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (ν : Measure (SubspaceSpace W)) (f : SubspaceSpace W → Y) (a : Y)
    (B : Spatial (Module.finrank ℝ W) →L[ℝ] Y) (p : SubspaceSpace W) (r : ℝ) :
    affineFitIntegral (ν.map (subspaceParabolicMeasurableEquiv W))
        (f ∘ (subspaceParabolicIsometry W).symm) a B (subspaceParabolicIsometry W p) r =
      affineFitIntegral ν f a
        (B.comp ((subspaceCoordinates W).toContinuousLinearEquiv :
          W →L[ℝ] Spatial (Module.finrank ℝ W))) p r := by
  unfold affineFitIntegral
  rw [← (subspaceParabolicIsometry W).image_ball]
  refine (setLIntegral_comp_subspaceParabolicIsometry W ν (Metric.ball p r)
    (fun w => ‖(f ∘ (subspaceParabolicIsometry W).symm) w - (a + B w.1)‖ₑ ^ 2)).symm.trans ?_
  refine lintegral_congr fun z => ?_
  simp only [Function.comp_apply, IsometryEquiv.symm_apply_apply]
  rfl

/-- Squared affine errors transport along `Φ`, for an arbitrary measure on the intrinsic
base: the pushforward measure, the transported values and the image center. -/
theorem affineErrorSq_map_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (ν : Measure (SubspaceSpace W)) (f : SubspaceSpace W → Y) (p : SubspaceSpace W) (r : ℝ) :
    affineErrorSq (ν.map (subspaceParabolicMeasurableEquiv W))
        (f ∘ (subspaceParabolicIsometry W).symm) (subspaceParabolicIsometry W p) r =
      affineErrorSq ν f p r := by
  rcases le_or_gt r 0 with hr | hr
  · rw [affineErrorSq_of_nonpos _ _ _ hr, affineErrorSq_of_nonpos _ _ _ hr]
  rw [affineErrorSq_of_pos _ _ _ hr, affineErrorSq_of_pos _ _ _ hr,
    baseDimension_spatial_finrank]
  congr 1
  refine iInf_congr fun a => ?_
  simp only [affineFitIntegral_map_subspaceParabolicIsometry]
  have hsurj : Function.Surjective
      (fun B : Spatial (Module.finrank ℝ W) →L[ℝ] Y => B.comp
        ((subspaceCoordinates W).toContinuousLinearEquiv :
          W →L[ℝ] Spatial (Module.finrank ℝ W))) := by
    intro B
    refine ⟨B.comp ((subspaceCoordinates W).symm.toContinuousLinearEquiv :
      Spatial (Module.finrank ℝ W) →L[ℝ] W), ?_⟩
    ext u
    simp
  exact hsurj.iInf_comp (fun B => affineFitIntegral ν f a B p r)

/-- The intrinsic volume restricted to an arbitrary set `K` is carried by `Φ` to the
ordinary volume restricted to `Φ K`. -/
theorem map_restrict_subspaceParabolicIsometry (W : Submodule ℝ (Spatial n))
    (K : Set (SubspaceSpace W)) :
    ((intrinsicParabolicVolume W).restrict K).map (subspaceParabolicMeasurableEquiv W) =
      (parabolicVolume (Module.finrank ℝ W)).restrict (subspaceParabolicIsometry W '' K) := by
  set e := subspaceParabolicMeasurableEquiv W
  have he : (e : SubspaceSpace W → Space (Module.finrank ℝ W)) = subspaceParabolicIsometry W :=
    rfl
  rw [← (subspaceParabolic_measurePreserving W).map_eq, e.restrict_map, ← he,
    e.preimage_image]

/-- The trace error is preserved by the transport to ordinary coordinates; the statement of
`traceErrorSq_subspaceParabolicIsometry`. -/
theorem traceErrorSq_subspaceParabolicIsometry_proof {n : ℕ} (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (K : Set (SubspaceSpace W))
    (f : SubspaceSpace W → Y) (p : SubspaceSpace W) (r : ℝ) :
    traceErrorSq (intrinsicParabolicVolume W) K f p r =
      traceErrorSq (parabolicVolume (Module.finrank ℝ W)) (subspaceParabolicIsometry W '' K)
        (f ∘ (subspaceParabolicIsometry W).symm) (subspaceParabolicIsometry W p) r := by
  unfold traceErrorSq
  rw [← map_restrict_subspaceParabolicIsometry, affineErrorSq_map_subspaceParabolicIsometry]

/-- The affine Carleson bound is preserved by the transport to ordinary coordinates; the
statement of `hasAffineCarlesonBound_comp_subspaceParabolicIsometry`. -/
theorem hasAffineCarlesonBound_comp_subspaceParabolicIsometry_proof {n : ℕ}
    (W : Submodule ℝ (Spatial n)) {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (H : Space (Module.finrank ℝ W) → Y) (B : ℝ) :
    HasAffineCarlesonBound (parabolicVolume (Module.finrank ℝ W)) H B ↔
      HasAffineCarlesonBound (intrinsicParabolicVolume W) (H ∘ subspaceParabolicIsometry W) B := by
  have hmap : (intrinsicParabolicVolume W).map (subspaceParabolicMeasurableEquiv W) =
      parabolicVolume (Module.finrank ℝ W) := (subspaceParabolic_measurePreserving W).map_eq
  have hκ : ∀ y s, affineErrorSq (intrinsicParabolicVolume W) (H ∘ subspaceParabolicIsometry W)
      y s = affineErrorSq (parabolicVolume (Module.finrank ℝ W)) H
        (subspaceParabolicIsometry W y) s := by
    intro y s
    rw [← affineErrorSq_map_subspaceParabolicIsometry W (intrinsicParabolicVolume W)
      (H ∘ subspaceParabolicIsometry W) y s, hmap]
    congr 1
    funext w
    simp
  have hC : ∀ z R, affineCarlesonIntegral (intrinsicParabolicVolume W)
      (H ∘ subspaceParabolicIsometry W) z R =
      affineCarlesonIntegral (parabolicVolume (Module.finrank ℝ W)) H
        (subspaceParabolicIsometry W z) R := by
    intro z R
    unfold affineCarlesonIntegral
    simp only [hκ]
    refine (setLIntegral_comp_subspaceParabolicIsometry W _ (Metric.ball z R) (fun w =>
      ∫⁻ s in Ioo 0 R, affineErrorSq (parabolicVolume (Module.finrank ℝ W)) H w s
        ∂scaleMeasure)).trans ?_
    rw [hmap, IsometryEquiv.image_ball]
  unfold HasAffineCarlesonBound
  rw [baseDimension_spatial_finrank]
  constructor
  · rintro ⟨hB, h⟩
    exact ⟨hB, fun z R hR => (hC z R).trans_le (h _ R hR)⟩
  · rintro ⟨hB, h⟩
    refine ⟨hB, fun w R hR => ?_⟩
    have h' := h ((subspaceParabolicIsometry W).symm w) R hR
    rwa [hC, IsometryEquiv.apply_symm_apply] at h'

end ParabolicRectifiability
