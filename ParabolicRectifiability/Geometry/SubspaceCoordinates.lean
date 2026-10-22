import ParabolicRectifiability.Metric.Measure

/-!
# Intrinsic coordinates on vertical bases

An actual orthonormal basis identifies each spatial subspace with Euclidean
coordinates of its rank. Ordinary time gives the analytic product-volume
transport, while snowflaked time gives the parabolic isometry. The reference
measure uses intrinsic inner-product volume on the subspace, not a restriction
of ambient volume to its image.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability

variable {n : ℕ}

/-- Orthonormal coordinates constructed on the intrinsic spatial subspace. -/
def subspaceCoordinates (W : Submodule ℝ (Spatial n)) :
    W ≃ₗᵢ[ℝ] Spatial (Module.finrank ℝ W) :=
  (stdOrthonormalBasis ℝ W).repr

theorem subspaceCoordinates_spatial_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceCoordinates W).toHomeomorph.toMeasurableEquiv
      (volume : Measure W) (volume : Measure (Spatial (Module.finrank ℝ W))) :=
  (stdOrthonormalBasis ℝ W).measurePreserving_repr

theorem subspaceCoordinate_abs_le_norm (W : Submodule ℝ (Spatial n)) (v : W)
    (i : Fin (Module.finrank ℝ W)) :
    |subspaceCoordinates W v i| ≤ ‖v‖ := by
  simpa only [Real.norm_eq_abs, (subspaceCoordinates W).norm_map] using
    PiLp.norm_apply_le (subspaceCoordinates W v) i

/-- Orthonormal coordinates constructed on the actual normal subspace. -/
def normalCoordinates (W : Submodule ℝ (Spatial n)) :
    W.orthogonal ≃ₗᵢ[ℝ] Spatial (Module.finrank ℝ W.orthogonal) :=
  subspaceCoordinates W.orthogonal

theorem subspace_finrank_add_normal (W : Submodule ℝ (Spatial n)) :
    Module.finrank ℝ W + Module.finrank ℝ W.orthogonal = n := by
  simpa only [finrank_euclideanSpace_fin] using W.finrank_add_finrank_orthogonal

def subspaceCoordinatesHomeomorph (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ₜ Coordinates (Module.finrank ℝ W) :=
  (subspaceCoordinates W).toHomeomorph.prodCongr (Homeomorph.refl ℝ)

def subspaceCoordinatesMeasurableEquiv (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ᵐ Coordinates (Module.finrank ℝ W) :=
  (subspaceCoordinatesHomeomorph W).toMeasurableEquiv

@[simp]
theorem subspaceCoordinatesMeasurableEquiv_apply (W : Submodule ℝ (Spatial n)) (y : W × ℝ) :
    subspaceCoordinatesMeasurableEquiv W y = (subspaceCoordinates W y.1, y.2) := rfl

@[simp]
theorem subspaceCoordinatesMeasurableEquiv_symm_apply (W : Submodule ℝ (Spatial n))
    (y : Coordinates (Module.finrank ℝ W)) :
    (subspaceCoordinatesMeasurableEquiv W).symm y = ((subspaceCoordinates W).symm y.1, y.2) :=
  rfl

theorem subspaceCoordinates_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceCoordinatesMeasurableEquiv W)
      ((volume : Measure W).prod (volume : Measure ℝ)) (coordinateVolume (Module.finrank ℝ W)) :=
  MeasurePreserving.prod (stdOrthonormalBasis ℝ W).measurePreserving_repr
    (MeasurePreserving.id volume)

def subspaceToFourierHomeomorph (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ₜ FourierSpace (Module.finrank ℝ W) :=
  (subspaceCoordinatesHomeomorph W).trans (fourierCoordinatesHomeomorph (Module.finrank ℝ W)).symm

def subspaceToFourier (W : Submodule ℝ (Spatial n)) :
    W × ℝ ≃ᵐ FourierSpace (Module.finrank ℝ W) :=
  (subspaceToFourierHomeomorph W).toMeasurableEquiv

@[simp]
theorem subspaceToFourier_apply (W : Submodule ℝ (Spatial n)) (y : W × ℝ) :
    subspaceToFourier W y = WithLp.toLp 2 (subspaceCoordinates W y.1, y.2) := rfl

@[simp]
theorem subspaceToFourier_symm_apply (W : Submodule ℝ (Spatial n))
    (x : FourierSpace (Module.finrank ℝ W)) :
    (subspaceToFourier W).symm x =
      ((subspaceCoordinates W).symm (WithLp.ofLp x).1, (WithLp.ofLp x).2) := rfl

theorem subspaceToFourier_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceToFourier W)
      ((volume : Measure W).prod (volume : Measure ℝ))
      (volume : Measure (FourierSpace (Module.finrank ℝ W))) :=
  (subspaceCoordinates_measurePreserving W).trans
    (fourierCoordinates_symm_measurePreserving_prod (Module.finrank ℝ W))

theorem subspaceToFourier_symm_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceToFourier W).symm
      (volume : Measure (FourierSpace (Module.finrank ℝ W)))
      ((volume : Measure W).prod (volume : Measure ℝ)) :=
  (subspaceToFourier_measurePreserving W).symm

theorem subspaceToFourier_restrict_measurePreserving (W : Submodule ℝ (Spatial n))
    (s : Set (FourierSpace (Module.finrank ℝ W))) :
    MeasurePreserving (subspaceToFourier W)
      (((volume : Measure W).prod (volume : Measure ℝ)).restrict (subspaceToFourier W ⁻¹' s))
      (volume.restrict s) :=
  (subspaceToFourier_measurePreserving W).restrict_preimage_emb
    (subspaceToFourier W).measurableEmbedding s

theorem subspaceToFourier_symm_restrict_measurePreserving (W : Submodule ℝ (Spatial n))
    (s : Set (FourierSpace (Module.finrank ℝ W))) :
    MeasurePreserving (subspaceToFourier W).symm (volume.restrict s)
      (((volume : Measure W).prod (volume : Measure ℝ)).restrict (subspaceToFourier W ⁻¹' s)) :=
  (subspaceToFourier_restrict_measurePreserving W s).symm

/-- The intrinsic vertical base with the inherited maximum parabolic metric. -/
abbrev SubspaceSpace (W : Submodule ℝ (Spatial n)) := W × Time

/-- Spatial orthonormal coordinates preserve the actual parabolic metric. -/
def subspaceParabolicIsometry (W : Submodule ℝ (Spatial n)) :
    SubspaceSpace W ≃ᵢ Space (Module.finrank ℝ W) where
  toEquiv := (subspaceCoordinates W).toEquiv.prodCongr (Equiv.refl Time)
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro z w
    change max (dist (subspaceCoordinates W z.1) (subspaceCoordinates W w.1)) (dist z.2 w.2) =
      max (dist z.1 w.1) (dist z.2 w.2)
    rw [(subspaceCoordinates W).dist_map]

@[simp]
theorem subspaceParabolicIsometry_apply (W : Submodule ℝ (Spatial n)) (z : SubspaceSpace W) :
    subspaceParabolicIsometry W z = (subspaceCoordinates W z.1, z.2) := rfl

@[simp]
theorem subspaceParabolicIsometry_symm_apply (W : Submodule ℝ (Spatial n))
    (z : Space (Module.finrank ℝ W)) :
    (subspaceParabolicIsometry W).symm z = ((subspaceCoordinates W).symm z.1, z.2) := rfl

def subspaceParabolicMeasurableEquiv (W : Submodule ℝ (Spatial n)) :
    SubspaceSpace W ≃ᵐ Space (Module.finrank ℝ W) :=
  (subspaceParabolicIsometry W).toHomeomorph.toMeasurableEquiv

/-- The intrinsic base embeds isometrically into its original ambient space. -/
def subspaceInclusion (W : Submodule ℝ (Spatial n)) (z : SubspaceSpace W) : Space n :=
  ((z.1 : Spatial n), z.2)

theorem isometry_subspaceInclusion (W : Submodule ℝ (Spatial n)) :
    Isometry (subspaceInclusion W) :=
  Isometry.of_dist_eq fun _ _ => rfl

theorem range_subspaceInclusion (W : Submodule ℝ (Spatial n)) :
    Set.range (subspaceInclusion W) = {z : Space n | z.1 ∈ W} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact y.1.property
  · intro hz
    exact ⟨(⟨z.1, hz⟩, z.2), rfl⟩

theorem dist_subspace_time (W : Submodule ℝ (Spatial n)) (u v : W) (t s : ℝ) :
    dist ((u, Metric.Snowflaking.toSnowflaking t) : SubspaceSpace W)
      ((v, Metric.Snowflaking.toSnowflaking s) : SubspaceSpace W) =
      max ‖(u : Spatial n) - (v : Spatial n)‖ (Real.sqrt |t - s|) := by
  exact dist_point (u : Spatial n) (v : Spatial n) t s

def subspaceTimeHomeomorph (W : Submodule ℝ (Spatial n)) : SubspaceSpace W ≃ₜ W × ℝ :=
  (Homeomorph.refl W).prodCongr Metric.Snowflaking.homeomorph

def subspaceTimeMeasurableEquiv (W : Submodule ℝ (Spatial n)) : SubspaceSpace W ≃ᵐ W × ℝ :=
  (subspaceTimeHomeomorph W).toMeasurableEquiv

@[simp]
theorem subspaceTimeMeasurableEquiv_apply (W : Submodule ℝ (Spatial n)) (z : SubspaceSpace W) :
    subspaceTimeMeasurableEquiv W z = (z.1, z.2.val) := rfl

@[simp]
theorem subspaceTimeMeasurableEquiv_symm_apply (W : Submodule ℝ (Spatial n)) (y : W × ℝ) :
    (subspaceTimeMeasurableEquiv W).symm y = (y.1, Metric.Snowflaking.toSnowflaking y.2) := rfl

/-- Intrinsic reference volume: spatial inner-product volume times real time volume,
transported only through the inverse snowflake time coordinate map. -/
def intrinsicParabolicVolume (W : Submodule ℝ (Spatial n)) : Measure (SubspaceSpace W) :=
  Measure.map (subspaceTimeHomeomorph W).symm
    ((volume : Measure W).prod (volume : Measure ℝ))

theorem subspaceTime_symm_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceTimeMeasurableEquiv W).symm
      ((volume : Measure W).prod (volume : Measure ℝ)) (intrinsicParabolicVolume W) :=
  ⟨(subspaceTimeMeasurableEquiv W).symm.measurable, rfl⟩

theorem subspaceTime_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceTimeMeasurableEquiv W) (intrinsicParabolicVolume W)
      ((volume : Measure W).prod (volume : Measure ℝ)) :=
  (subspaceTime_symm_measurePreserving W).symm

theorem subspaceParabolic_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceParabolicMeasurableEquiv W) (intrinsicParabolicVolume W)
      (parabolicVolume (Module.finrank ℝ W)) :=
  ((subspaceTime_measurePreserving W).trans (subspaceCoordinates_measurePreserving W)).trans
    (coordinates_symm_measurePreserving (Module.finrank ℝ W))

theorem subspaceParabolic_symm_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceParabolicMeasurableEquiv W).symm
      (parabolicVolume (Module.finrank ℝ W)) (intrinsicParabolicVolume W) :=
  (subspaceParabolic_measurePreserving W).symm

def subspaceFourierToParabolic (W : Submodule ℝ (Spatial n)) :
    FourierSpace (Module.finrank ℝ W) ≃ᵐ SubspaceSpace W :=
  (subspaceToFourier W).symm.trans (subspaceTimeMeasurableEquiv W).symm

@[simp]
theorem subspaceFourierToParabolic_apply (W : Submodule ℝ (Spatial n))
    (x : FourierSpace (Module.finrank ℝ W)) :
    subspaceFourierToParabolic W x =
      ((subspaceCoordinates W).symm (WithLp.ofLp x).1,
        Metric.Snowflaking.toSnowflaking (WithLp.ofLp x).2) := rfl

theorem subspaceFourierToParabolic_measurePreserving (W : Submodule ℝ (Spatial n)) :
    MeasurePreserving (subspaceFourierToParabolic W)
      (volume : Measure (FourierSpace (Module.finrank ℝ W))) (intrinsicParabolicVolume W) :=
  (subspaceToFourier_symm_measurePreserving W).trans (subspaceTime_symm_measurePreserving W)

theorem subspaceParabolic_fourierToParabolic (W : Submodule ℝ (Spatial n))
    (x : FourierSpace (Module.finrank ℝ W)) :
    subspaceParabolicIsometry W (subspaceFourierToParabolic W x) =
      fourierToParabolicMeasurableEquiv (Module.finrank ℝ W) x := by
  change point (subspaceCoordinates W ((subspaceCoordinates W).symm (WithLp.ofLp x).1))
    (WithLp.ofLp x).2 = point (WithLp.ofLp x).1 (WithLp.ofLp x).2
  rw [(subspaceCoordinates W).apply_symm_apply]

theorem subspaceFourier_preimage_ball (W : Submodule ℝ (Spatial n)) (z : SubspaceSpace W)
    (r : ℝ) (hr : 0 < r) :
    subspaceFourierToParabolic W ⁻¹' Metric.ball z r =
      analyticCylinder (subspaceParabolicIsometry W z) r := by
  rw [← (subspaceParabolicIsometry W).isometry.preimage_ball z r,
    analyticCylinder_eq_preimage_ball _ r hr]
  ext x
  simp only [mem_preimage]
  rw [subspaceParabolic_fourierToParabolic]

theorem intrinsicParabolicVolume_ball (W : Submodule ℝ (Spatial n)) (z : SubspaceSpace W)
    (r : ℝ) (hr : 0 < r) :
    intrinsicParabolicVolume W (Metric.ball z r) =
      2 * omega (Module.finrank ℝ W) * ENNReal.ofReal r ^ (Module.finrank ℝ W + 2) := by
  rw [← (subspaceParabolicIsometry W).isometry.preimage_ball z r,
    ]
  change intrinsicParabolicVolume W (subspaceParabolicMeasurableEquiv W ⁻¹'
    Metric.ball (subspaceParabolicIsometry W z) r) = _
  rw [(subspaceParabolic_measurePreserving W).measure_preimage_equiv]
  exact parabolicVolume_ball _ r hr

theorem intrinsicParabolicVolume_ball_of_dimension (W : Submodule ℝ (Spatial n))
    (k : ℕ) (hk : Module.finrank ℝ W + 2 = k) (z : SubspaceSpace W) (r : ℝ) (hr : 0 < r) :
    intrinsicParabolicVolume W (Metric.ball z r) =
      2 * omega (Module.finrank ℝ W) * ENNReal.ofReal r ^ k := by
  rw [← hk]
  exact intrinsicParabolicVolume_ball W z r hr

end ParabolicRectifiability
