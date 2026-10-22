import ParabolicRectifiability.Metric.Space

/-!
# Euclidean analytic coordinates and volume transport

The L² product wrapper supplies the ordinary real inner product needed for
analysis. Its coordinate maps preserve canonical volume by mathlib's Haar
volume theorem for products of finite-dimensional real inner-product spaces,
not merely because the maps are homeomorphisms.

All dimensions, including zero, use the same type and inherited instances.
No measure on the snowflaked parabolic space is defined here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ParabolicRectifiability

/-- Ordinary Euclidean analytic space, with the L² product inner product. -/
abbrev FourierSpace (m : ℕ) := WithLp 2 (Coordinates m)

/-- Ordinary spatial and time coordinates of the Euclidean L² product. -/
def fourierCoordinatesHomeomorph (m : ℕ) : FourierSpace m ≃ₜ Coordinates m :=
  WithLp.homeomorphProd 2 (Spatial m) ℝ

@[simp]
theorem fourierCoordinatesHomeomorph_apply {m : ℕ} (x : FourierSpace m) :
    fourierCoordinatesHomeomorph m x = WithLp.ofLp x := rfl

@[simp]
theorem fourierCoordinatesHomeomorph_symm_apply {m : ℕ} (y : Coordinates m) :
    (fourierCoordinatesHomeomorph m).symm y = WithLp.toLp 2 y := rfl

@[simp]
theorem fourierCoordinatesHomeomorph_toLp {m : ℕ} (y : Coordinates m) :
    fourierCoordinatesHomeomorph m (WithLp.toLp 2 y) = y := rfl

/-- The same coordinates with their inherited Borel structures. -/
def fourierCoordinatesMeasurableEquiv (m : ℕ) : FourierSpace m ≃ᵐ Coordinates m :=
  (fourierCoordinatesHomeomorph m).toMeasurableEquiv

@[simp]
theorem fourierCoordinatesMeasurableEquiv_apply {m : ℕ} (x : FourierSpace m) :
    fourierCoordinatesMeasurableEquiv m x = WithLp.ofLp x := rfl

@[simp]
theorem fourierCoordinatesMeasurableEquiv_symm_apply {m : ℕ} (y : Coordinates m) :
    (fourierCoordinatesMeasurableEquiv m).symm y = WithLp.toLp 2 y := rfl

@[simp]
theorem fourierCoordinatesMeasurableEquiv_symm_ofLp {m : ℕ} (x : FourierSpace m) :
    (fourierCoordinatesMeasurableEquiv m).symm (WithLp.ofLp x) = x := rfl

theorem volume_coordinates_eq_prod (m : ℕ) :
    (volume : Measure (Coordinates m)) =
      (volume : Measure (Spatial m)).prod (volume : Measure ℝ) :=
  Measure.volume_eq_prod _ _

/-- Canonical Euclidean volume preservation, instantiated from the Haar theorem. -/
theorem fourierCoordinates_measurePreserving (m : ℕ) :
    MeasurePreserving (fourierCoordinatesMeasurableEquiv m)
      (volume : Measure (FourierSpace m)) (volume : Measure (Coordinates m)) :=
  WithLp.volume_preserving_ofLp (Spatial m) ℝ

/-- The inverse uses the library's canonical volume-preserving `toLp` map. -/
theorem fourierCoordinates_symm_measurePreserving (m : ℕ) :
    MeasurePreserving (fourierCoordinatesMeasurableEquiv m).symm
      (volume : Measure (Coordinates m)) (volume : Measure (FourierSpace m)) :=
  WithLp.volume_preserving_toLp (Spatial m) ℝ

theorem fourierCoordinates_measurePreserving_prod (m : ℕ) :
    MeasurePreserving (fourierCoordinatesMeasurableEquiv m)
      (volume : Measure (FourierSpace m))
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ)) := by
  rw [← volume_coordinates_eq_prod m]
  exact fourierCoordinates_measurePreserving m

theorem fourierCoordinates_symm_measurePreserving_prod (m : ℕ) :
    MeasurePreserving (fourierCoordinatesMeasurableEquiv m).symm
      ((volume : Measure (Spatial m)).prod (volume : Measure ℝ))
      (volume : Measure (FourierSpace m)) := by
  rw [← volume_coordinates_eq_prod m]
  exact fourierCoordinates_symm_measurePreserving m

/-- Embedding transport also permits arbitrary restriction sets; in particular
it applies to every measurable coordinate set without additional assumptions. -/
theorem fourierCoordinates_restrict_measurePreserving (m : ℕ) (s : Set (Coordinates m)) :
    MeasurePreserving (fourierCoordinatesMeasurableEquiv m)
      (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s))
      (volume.restrict s) :=
  (fourierCoordinates_measurePreserving m).restrict_preimage_emb
    (fourierCoordinatesMeasurableEquiv m).measurableEmbedding s

theorem fourierCoordinates_symm_restrict_measurePreserving (m : ℕ) (s : Set (Coordinates m)) :
    MeasurePreserving (fourierCoordinatesMeasurableEquiv m).symm
      (volume.restrict s)
      (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)) :=
  (fourierCoordinates_restrict_measurePreserving m s).symm

theorem ae_fourierCoordinates_iff {m : ℕ} (P : Coordinates m → Prop) :
    (∀ᵐ x ∂(volume : Measure (FourierSpace m)), P ((fourierCoordinatesMeasurableEquiv m) x)) ↔ ∀ᵐ y ∂(volume : Measure (Coordinates m)), P y := by
  rw [← (fourierCoordinates_measurePreserving m).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).measurableEmbedding.ae_map_iff.symm

theorem memLp_fourierCoordinates_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (f : Coordinates m → E) (p : ℝ≥0∞) :
    MemLp (f ∘ (fourierCoordinatesMeasurableEquiv m)) p (volume : Measure (FourierSpace m)) ↔ MemLp f p (volume : Measure (Coordinates m)) := by
  rw [← (fourierCoordinates_measurePreserving m).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).memLp_map_measure_iff.symm

theorem integrable_fourierCoordinates_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (f : Coordinates m → E) :
    Integrable (f ∘ (fourierCoordinatesMeasurableEquiv m)) (volume : Measure (FourierSpace m)) ↔ Integrable f (volume : Measure (Coordinates m)) :=
  (fourierCoordinates_measurePreserving m).integrable_comp_emb (fourierCoordinatesMeasurableEquiv m).measurableEmbedding

/-- Total Bochner-integral identity; integrability is transported separately. -/
theorem integral_fourierCoordinates {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Coordinates m → E) :
    (∫ x, f ((fourierCoordinatesMeasurableEquiv m) x) ∂(volume : Measure (FourierSpace m))) = ∫ y, f y ∂(volume : Measure (Coordinates m)) :=
  (fourierCoordinates_measurePreserving m).integral_comp' f

theorem ae_fourierCoordinates_symm_iff {m : ℕ} (P : FourierSpace m → Prop) :
    (∀ᵐ x ∂(volume : Measure (Coordinates m)), P ((fourierCoordinatesMeasurableEquiv m).symm x)) ↔ ∀ᵐ y ∂(volume : Measure (FourierSpace m)), P y := by
  rw [← (fourierCoordinates_symm_measurePreserving m).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).symm.measurableEmbedding.ae_map_iff.symm

theorem memLp_fourierCoordinates_symm_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (f : FourierSpace m → E) (p : ℝ≥0∞) :
    MemLp (f ∘ (fourierCoordinatesMeasurableEquiv m).symm) p (volume : Measure (Coordinates m)) ↔ MemLp f p (volume : Measure (FourierSpace m)) := by
  rw [← (fourierCoordinates_symm_measurePreserving m).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).symm.memLp_map_measure_iff.symm

theorem integrable_fourierCoordinates_symm_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (f : FourierSpace m → E) :
    Integrable (f ∘ (fourierCoordinatesMeasurableEquiv m).symm) (volume : Measure (Coordinates m)) ↔ Integrable f (volume : Measure (FourierSpace m)) :=
  (fourierCoordinates_symm_measurePreserving m).integrable_comp_emb (fourierCoordinatesMeasurableEquiv m).symm.measurableEmbedding

/-- Total Bochner-integral identity; integrability is transported separately. -/
theorem integral_fourierCoordinates_symm {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : FourierSpace m → E) :
    (∫ x, f ((fourierCoordinatesMeasurableEquiv m).symm x) ∂(volume : Measure (Coordinates m))) = ∫ y, f y ∂(volume : Measure (FourierSpace m)) :=
  (fourierCoordinates_symm_measurePreserving m).integral_comp' f

theorem ae_fourierCoordinates_restrict_iff {m : ℕ} (s : Set (Coordinates m)) (P : Coordinates m → Prop) :
    (∀ᵐ x ∂(volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)), P ((fourierCoordinatesMeasurableEquiv m) x)) ↔ ∀ᵐ y ∂(volume.restrict s), P y := by
  rw [← (fourierCoordinates_restrict_measurePreserving m s).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).measurableEmbedding.ae_map_iff.symm

theorem memLp_fourierCoordinates_restrict_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (s : Set (Coordinates m)) (f : Coordinates m → E) (p : ℝ≥0∞) :
    MemLp (f ∘ (fourierCoordinatesMeasurableEquiv m)) p (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)) ↔ MemLp f p (volume.restrict s) := by
  rw [← (fourierCoordinates_restrict_measurePreserving m s).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).memLp_map_measure_iff.symm

theorem integrable_fourierCoordinates_restrict_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (s : Set (Coordinates m)) (f : Coordinates m → E) :
    Integrable (f ∘ (fourierCoordinatesMeasurableEquiv m)) (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)) ↔ Integrable f (volume.restrict s) :=
  (fourierCoordinates_restrict_measurePreserving m s).integrable_comp_emb (fourierCoordinatesMeasurableEquiv m).measurableEmbedding

/-- Total Bochner-integral identity; integrability is transported separately. -/
theorem integral_fourierCoordinates_restrict {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set (Coordinates m)) (f : Coordinates m → E) :
    (∫ x, f ((fourierCoordinatesMeasurableEquiv m) x) ∂(volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s))) = ∫ y, f y ∂(volume.restrict s) :=
  (fourierCoordinates_restrict_measurePreserving m s).integral_comp' f

theorem ae_fourierCoordinates_symm_restrict_iff {m : ℕ} (s : Set (Coordinates m)) (P : FourierSpace m → Prop) :
    (∀ᵐ x ∂(volume.restrict s), P ((fourierCoordinatesMeasurableEquiv m).symm x)) ↔ ∀ᵐ y ∂(volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)), P y := by
  rw [← (fourierCoordinates_symm_restrict_measurePreserving m s).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).symm.measurableEmbedding.ae_map_iff.symm

theorem memLp_fourierCoordinates_symm_restrict_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (s : Set (Coordinates m)) (f : FourierSpace m → E) (p : ℝ≥0∞) :
    MemLp (f ∘ (fourierCoordinatesMeasurableEquiv m).symm) p (volume.restrict s) ↔ MemLp f p (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)) := by
  rw [← (fourierCoordinates_symm_restrict_measurePreserving m s).map_eq]
  exact (fourierCoordinatesMeasurableEquiv m).symm.memLp_map_measure_iff.symm

theorem integrable_fourierCoordinates_symm_restrict_iff {m : ℕ} {E : Type*}
    [TopologicalSpace E] [ContinuousENorm E] (s : Set (Coordinates m)) (f : FourierSpace m → E) :
    Integrable (f ∘ (fourierCoordinatesMeasurableEquiv m).symm) (volume.restrict s) ↔ Integrable f (volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)) :=
  (fourierCoordinates_symm_restrict_measurePreserving m s).integrable_comp_emb (fourierCoordinatesMeasurableEquiv m).symm.measurableEmbedding

/-- Total Bochner-integral identity; integrability is transported separately. -/
theorem integral_fourierCoordinates_symm_restrict {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Set (Coordinates m)) (f : FourierSpace m → E) :
    (∫ x, f ((fourierCoordinatesMeasurableEquiv m).symm x) ∂(volume.restrict s)) = ∫ y, f y ∂(volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' s)) :=
  (fourierCoordinates_symm_restrict_measurePreserving m s).integral_comp' f

end ParabolicRectifiability
