import ParabolicRectifiability.Metric.ProperSpace
import ParabolicRectifiability.Analysis.Coordinates

/-!
# Coordinate Lebesgue measure on parabolic space

The measure is transported by the explicit inverse coordinate map. Balls are
ordinary coordinate rectangles, so their volumes follow from spatial Haar
volume and real interval length. Analytic cylinders live in the Euclidean
type `FourierSpace n`; they are preimages of these rectangles, not Euclidean balls.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability

/-- Product of ordinary Euclidean spatial volume and one-dimensional
Lebesgue time measure; the coordinate dimension is `n + 1`. -/
def coordinateVolume (n : ℕ) : Measure (Coordinates n) :=
  (volume : Measure (Spatial n)).prod (volume : Measure ℝ)

/-- Coordinate Lebesgue volume transported to `Space n`. For `r > 0`,
a parabolic ball has measure `2 * omega n * r^(n+2)`. This volume is distinct
from the unnormalized Hausdorff measures `hausdorffP n k`. -/
def parabolicVolume (n : ℕ) : Measure (Space n) :=
  Measure.map (coordinatesHomeomorph n).symm (coordinateVolume n)

theorem coordinateVolume_eq_volume (n : ℕ) :
    coordinateVolume n = (volume : Measure (Coordinates n)) := rfl

theorem coordinates_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (coordinatesMeasurableEquiv n).symm
      (coordinateVolume n) (parabolicVolume n) :=
  ⟨(coordinatesMeasurableEquiv n).symm.measurable, rfl⟩

theorem coordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (coordinatesMeasurableEquiv n)
      (parabolicVolume n) (coordinateVolume n) :=
  (coordinates_symm_measurePreserving n).symm

def fourierToParabolic (n : ℕ) : FourierSpace n ≃ₜ Space n :=
  (fourierCoordinatesHomeomorph n).trans (coordinatesHomeomorph n).symm

def fourierToParabolicMeasurableEquiv (n : ℕ) : FourierSpace n ≃ᵐ Space n :=
  (fourierToParabolic n).toMeasurableEquiv

@[simp]
theorem fourierToParabolic_apply {n : ℕ} (x : FourierSpace n) :
    fourierToParabolic n x = point (WithLp.ofLp x).1 (WithLp.ofLp x).2 := rfl

@[simp]
theorem fourierToParabolic_symm_apply {n : ℕ} (z : Space n) :
    (fourierToParabolic n).symm z = WithLp.toLp 2 (z.1, z.2.val) := rfl

@[simp]
theorem fourierToParabolicMeasurableEquiv_apply {n : ℕ} (x : FourierSpace n) :
    fourierToParabolicMeasurableEquiv n x = point (WithLp.ofLp x).1 (WithLp.ofLp x).2 := rfl

@[simp]
theorem fourierToParabolicMeasurableEquiv_symm_apply {n : ℕ} (z : Space n) :
    (fourierToParabolicMeasurableEquiv n).symm z = WithLp.toLp 2 (z.1, z.2.val) := rfl

theorem fourierToParabolic_measurePreserving (n : ℕ) :
    MeasurePreserving (fourierToParabolicMeasurableEquiv n)
      (volume : Measure (FourierSpace n)) (parabolicVolume n) :=
  (fourierCoordinates_measurePreserving_prod n).trans (coordinates_symm_measurePreserving n)

theorem fourierToParabolic_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (fourierToParabolicMeasurableEquiv n).symm
      (parabolicVolume n) (volume : Measure (FourierSpace n)) :=
  (fourierToParabolic_measurePreserving n).symm

theorem parabolicVolume_apply {n : ℕ} (A : Set (Space n)) :
    parabolicVolume n A =
      coordinateVolume n ((coordinatesMeasurableEquiv n).symm ⁻¹' A) :=
  ((coordinates_symm_measurePreserving n).measure_preimage_equiv A).symm

theorem coordinates_symm_preimage_ball {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) :
    (coordinatesMeasurableEquiv n).symm ⁻¹' Metric.ball z r =
      Metric.ball z.1 r ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2) := by
  rcases z with ⟨x, ⟨t⟩⟩
  ext ⟨y, s⟩
  change point y s ∈ Metric.ball (point x t) r ↔
    y ∈ Metric.ball x r ∧ s ∈ Ioo (t - r ^ 2) (t + r ^ 2)
  rw [mem_ball_point x y t s r hr]
  simp only [Metric.mem_ball, dist_eq_norm, mem_Ioo]
  rw [abs_lt]
  constructor <;> rintro ⟨h, ht⟩ <;> refine ⟨h, ?_⟩ <;> constructor <;> linarith [ht.1, ht.2]

theorem coordinates_symm_preimage_closedBall {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 ≤ r) :
    (coordinatesMeasurableEquiv n).symm ⁻¹' Metric.closedBall z r =
      Metric.closedBall z.1 r ×ˢ Icc (z.2.val - r ^ 2) (z.2.val + r ^ 2) := by
  rcases z with ⟨x, ⟨t⟩⟩
  ext ⟨y, s⟩
  change point y s ∈ Metric.closedBall (point x t) r ↔
    y ∈ Metric.closedBall x r ∧ s ∈ Icc (t - r ^ 2) (t + r ^ 2)
  rw [mem_closedBall_point x y t s r hr]
  simp only [Metric.mem_closedBall, dist_eq_norm, mem_Icc]
  rw [abs_le]
  constructor <;> rintro ⟨h, ht⟩ <;> refine ⟨h, ?_⟩ <;> constructor <;> linarith [ht.1, ht.2]

theorem coordinates_image_ball {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) :
    coordinatesMeasurableEquiv n '' Metric.ball z r =
      Metric.ball z.1 r ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2) := by
  rw [(coordinatesMeasurableEquiv n).image_eq_preimage_symm]
  exact coordinates_symm_preimage_ball z r hr

theorem coordinates_image_closedBall {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 ≤ r) :
    coordinatesMeasurableEquiv n '' Metric.closedBall z r =
      Metric.closedBall z.1 r ×ˢ Icc (z.2.val - r ^ 2) (z.2.val + r ^ 2) := by
  rw [(coordinatesMeasurableEquiv n).image_eq_preimage_symm]
  exact coordinates_symm_preimage_closedBall z r hr

/-- An open parabolic ball is the preimage of the coordinate rectangle
`B(x, r) × (t - r², t + r²)`. -/
theorem coordinates_preimage_ball_rectangle {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) :
    coordinatesMeasurableEquiv n ⁻¹'
      (Metric.ball z.1 r ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2)) = Metric.ball z r := by
  rw [← coordinates_image_ball z r hr, (coordinatesMeasurableEquiv n).preimage_image]

theorem coordinates_preimage_closedBall_rectangle {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 ≤ r) :
    coordinatesMeasurableEquiv n ⁻¹'
      (Metric.closedBall z.1 r ×ˢ Icc (z.2.val - r ^ 2) (z.2.val + r ^ 2)) =
      Metric.closedBall z r := by
  rw [← coordinates_image_closedBall z r hr, (coordinatesMeasurableEquiv n).preimage_image]

/-- The analytic parabolic cylinder, expressed in ordinary Fourier coordinates. -/
def analyticCylinder {n : ℕ} (z : Space n) (r : ℝ) : Set (FourierSpace n) :=
  fourierCoordinatesMeasurableEquiv n ⁻¹'
    (Metric.ball z.1 r ×ˢ Ioo (z.2.val - r ^ 2) (z.2.val + r ^ 2))

theorem measurableSet_analyticCylinder {n : ℕ} (z : Space n) (r : ℝ) :
    MeasurableSet (analyticCylinder z r) :=
  (fourierCoordinatesMeasurableEquiv n).measurable
    (measurableSet_ball.prod measurableSet_Ioo)

theorem analyticCylinder_eq_preimage_ball {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) :
    analyticCylinder z r = fourierToParabolicMeasurableEquiv n ⁻¹' Metric.ball z r := by
  rw [analyticCylinder, ← coordinates_symm_preimage_ball z r hr]
  rfl

/-- Ordinary spatial open unit-ball volume, including rank zero. -/
def omega (n : ℕ) : ℝ≥0∞ := (volume : Measure (Spatial n)) (Metric.ball 0 1)

theorem omega_pos (n : ℕ) : 0 < omega n :=
  Metric.measure_ball_pos volume _ zero_lt_one

theorem omega_lt_top (n : ℕ) : omega n < ∞ := measure_ball_lt_top

@[simp]
theorem omega_zero : omega 0 = 1 := by
  rw [omega, volume_euclideanSpace_eq_dirac (Fin 0)]
  simp

private theorem spatial_ball_volume {n : ℕ} (x : Spatial n) (r : ℝ) (hr : 0 < r) :
    (volume : Measure (Spatial n)) (Metric.ball x r) = ENNReal.ofReal r ^ n * omega n := by
  simpa [omega, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr.le] using
    Measure.addHaar_ball_of_pos (volume : Measure (Spatial n)) x hr

private theorem spatial_closedBall_volume {n : ℕ} (x : Spatial n) (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure (Spatial n)) (Metric.closedBall x r) = ENNReal.ofReal r ^ n * omega n := by
  simpa [omega, finrank_euclideanSpace_fin, ENNReal.ofReal_pow hr] using
    Measure.addHaar_closedBall (volume : Measure (Spatial n)) x hr

theorem parabolicVolume_ball {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) :
    parabolicVolume n (Metric.ball z r) = 2 * omega n * ENNReal.ofReal r ^ (n + 2) := by
  rw [parabolicVolume_apply, coordinates_symm_preimage_ball z r hr, coordinateVolume,
    Measure.prod_prod, spatial_ball_volume z.1 r hr, Real.volume_Ioo]
  rw [show z.2.val + r ^ 2 - (z.2.val - r ^ 2) = 2 * r ^ 2 by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow hr.le]
  norm_num
  rw [pow_add]
  ring

theorem parabolicVolume_closedBall {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 ≤ r) :
    parabolicVolume n (Metric.closedBall z r) = 2 * omega n * ENNReal.ofReal r ^ (n + 2) := by
  rw [parabolicVolume_apply, coordinates_symm_preimage_closedBall z r hr, coordinateVolume,
    Measure.prod_prod, spatial_closedBall_volume z.1 r hr, Real.volume_Icc]
  rw [show z.2.val + r ^ 2 - (z.2.val - r ^ 2) = 2 * r ^ 2 by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow hr]
  norm_num
  rw [pow_add]
  ring

theorem volume_analyticCylinder {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) :
    (volume : Measure (FourierSpace n)) (analyticCylinder z r) =
      2 * omega n * ENNReal.ofReal r ^ (n + 2) := by
  rw [analyticCylinder_eq_preimage_ball z r hr,
    (fourierToParabolic_measurePreserving n).measure_preimage_equiv]
  exact parabolicVolume_ball z r hr

instance parabolicVolume_finiteOnCompacts (n : ℕ) :
    IsFiniteMeasureOnCompacts (parabolicVolume n) := by
  have : IsFiniteMeasureOnCompacts (coordinateVolume n) := by
    rw [coordinateVolume_eq_volume]
    infer_instance
  exact Measure.IsFiniteMeasureOnCompacts.map (coordinateVolume n) (coordinatesHomeomorph n).symm

theorem parabolicVolume_sphere {n : ℕ} (z : Space n) (r : ℝ) :
    parabolicVolume n (Metric.sphere z r) = 0 := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · simp [Metric.sphere_eq_empty_of_neg hr]
  · subst r
    apply measure_mono_null Metric.sphere_subset_closedBall
    rw [parabolicVolume_closedBall z 0 le_rfl]
    simp
  · rw [← Metric.closedBall_sdiff_ball,
      measure_sdiff Metric.ball_subset_closedBall measurableSet_ball.nullMeasurableSet
        (measure_ball_lt_top (μ := parabolicVolume n)).ne,
      parabolicVolume_closedBall z r hr.le, parabolicVolume_ball z r hr, tsub_self]

theorem parabolicVolume_frontier_ball {n : ℕ} (z : Space n) (r : ℝ) :
    parabolicVolume n (frontier (Metric.ball z r)) = 0 :=
  measure_mono_null Metric.frontier_ball_subset_sphere (parabolicVolume_sphere z r)

theorem parabolicVolume_frontier_closedBall {n : ℕ} (z : Space n) (r : ℝ) :
    parabolicVolume n (frontier (Metric.closedBall z r)) = 0 :=
  measure_mono_null Metric.frontier_closedBall_subset_sphere (parabolicVolume_sphere z r)

@[simp]
theorem parabolicVolume_singleton {n : ℕ} (z : Space n) : parabolicVolume n {z} = 0 := by
  rw [← Metric.closedBall_zero]
  rw [parabolicVolume_closedBall z 0 le_rfl]
  simp

theorem parabolicVolume_ball_two_mul {n : ℕ} (z : Space n) (r : ℝ) (hr : 0 < r) :
    parabolicVolume n (Metric.ball z (2 * r)) =
      2 ^ (n + 2) * parabolicVolume n (Metric.ball z r) := by
  rw [parabolicVolume_ball z (2 * r) (by positivity), parabolicVolume_ball z r hr,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  rw [mul_pow]
  ring

def coordinateDilationHomeomorph (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Coordinates n ≃ₜ Coordinates n :=
  (Homeomorph.smulOfNeZero a ha.ne' : Spatial n ≃ₜ Spatial n).prodCongr
    (Homeomorph.smulOfNeZero (a ^ 2) (pow_ne_zero _ ha.ne') : ℝ ≃ₜ ℝ)

/-- The invertible version of the existing parabolic dilation. -/
def dilationHomeomorph (n : ℕ) (a : ℝ) (ha : 0 < a) : Space n ≃ₜ Space n :=
  ((coordinatesHomeomorph n).trans (coordinateDilationHomeomorph n a ha)).trans
    (coordinatesHomeomorph n).symm

def dilationMeasurableEquiv (n : ℕ) (a : ℝ) (ha : 0 < a) : Space n ≃ᵐ Space n :=
  (dilationHomeomorph n a ha).toMeasurableEquiv

@[simp]
theorem dilationHomeomorph_apply {n : ℕ} (a : ℝ) (ha : 0 < a) (z : Space n) :
    dilationHomeomorph n a ha z = dilate a z := rfl

@[simp]
theorem dilationMeasurableEquiv_apply {n : ℕ} (a : ℝ) (ha : 0 < a) (z : Space n) :
    dilationMeasurableEquiv n a ha z = dilate a z := rfl

theorem measurable_dilate {n : ℕ} (a : ℝ) : Measurable (dilate a : Space n → Space n) := by
  unfold dilate
  exact measurable_point.comp
    ((measurable_spatial.const_smul a).prodMk (measurable_const.mul measurable_time))

private theorem haar_scaling_factor (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ENNReal.ofReal |(a ^ k)⁻¹| = (ENNReal.ofReal a)⁻¹ ^ k := by
  rw [abs_of_pos (inv_pos.mpr (pow_pos ha k)), ENNReal.ofReal_inv_of_pos (pow_pos ha k),
    ENNReal.ofReal_pow ha.le, ENNReal.inv_pow]

private theorem map_coordinateDilation (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Measure.map (coordinateDilationHomeomorph n a ha) (coordinateVolume n) =
      (ENNReal.ofReal a)⁻¹ ^ (n + 2) • coordinateVolume n := by
  have h1 : Measure.map (fun x : Spatial n => a • x) volume =
      (ENNReal.ofReal a)⁻¹ ^ n • (volume : Measure (Spatial n)) := by
    rw [Measure.map_addHaar_smul volume ha.ne', finrank_euclideanSpace_fin,
      haar_scaling_factor a ha n]
  have h2 : Measure.map (fun t : ℝ => a ^ 2 • t) volume =
      (ENNReal.ofReal a)⁻¹ ^ 2 • (volume : Measure ℝ) := by
    rw [Measure.map_addHaar_smul volume (pow_ne_zero _ ha.ne'), Module.finrank_self, pow_one,
      haar_scaling_factor a ha 2]
  change Measure.map (Prod.map (fun x : Spatial n => a • x) (fun t : ℝ => a ^ 2 • t))
    ((volume : Measure (Spatial n)).prod (volume : Measure ℝ)) = _
  rw [← Measure.map_prod_map (f := fun x : Spatial n => a • x)
    (g := fun t : ℝ => a ^ 2 • t) _ _ (measurable_id.const_smul a)
    (measurable_id.const_smul (a ^ 2)), h1, h2, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul, ← pow_add]
  rfl

/-- Pushforward has the reciprocal scaling factor. -/
theorem map_dilate_parabolicVolume {n : ℕ} (a : ℝ) (ha : 0 < a) :
    Measure.map (dilate a) (parabolicVolume n) =
      (ENNReal.ofReal a)⁻¹ ^ (n + 2) • parabolicVolume n := by
  rw [parabolicVolume, Measure.map_map (measurable_dilate a)
    (coordinatesHomeomorph n).symm.measurable]
  have hf : dilate a ∘ (coordinatesHomeomorph n).symm =
      (coordinatesHomeomorph n).symm ∘ coordinateDilationHomeomorph n a ha := rfl
  rw [hf, ← Measure.map_map (coordinatesHomeomorph n).symm.measurable
    (coordinateDilationHomeomorph n a ha).measurable, map_coordinateDilation n a ha,
    Measure.map_smul _ (coordinatesHomeomorph n).symm.measurable.aemeasurable]

/-- Image scaling has the direct factor, for arbitrary sets by the measurable equivalence. -/
theorem parabolicVolume_dilate_image {n : ℕ} (a : ℝ) (ha : 0 < a) (A : Set (Space n)) :
    parabolicVolume n (dilate a '' A) =
      ENNReal.ofReal a ^ (n + 2) * parabolicVolume n A := by
  let e := dilationMeasurableEquiv n a ha
  let k := ENNReal.ofReal a ^ (n + 2)
  have h0 : k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr ha)
  have ht : k ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h : parabolicVolume n A = k⁻¹ * parabolicVolume n (e '' A) := by
    have hm := congrArg (fun μ : Measure (Space n) => μ (e '' A))
      (map_dilate_parabolicVolume (n := n) a ha)
    change (parabolicVolume n).map e (e '' A) = _ at hm
    rw [e.map_apply, e.preimage_image, Measure.smul_apply] at hm
    simpa [k, ENNReal.inv_pow] using hm
  change parabolicVolume n (e '' A) = k * parabolicVolume n A
  calc
    parabolicVolume n (e '' A) = (k * k⁻¹) * parabolicVolume n (e '' A) := by
      rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
    _ = k * parabolicVolume n A := by rw [mul_assoc, ← h]

end ParabolicRectifiability
