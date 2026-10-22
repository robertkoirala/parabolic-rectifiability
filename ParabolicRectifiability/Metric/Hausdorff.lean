import ParabolicRectifiability.Metric.ProperSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Hausdorff measure for parabolic space and partial domains

The measure is the library's unnormalized diameter-power Hausdorff measure
for the actual parabolic metric. A chart may be defined only on a subset;
its source Hausdorff measure is identified with the ambient one by the
isometric subtype inclusion. No extension of the chart is assumed.

Compact sets with finite Hausdorff measure give finite inner-regular
restrictions. This does not assert regularity of the unrestricted measure,
or identify Hausdorff measure with coordinate volume.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Unnormalized `k`-dimensional Hausdorff measure for the parabolic metric. -/
def hausdorffP (n k : ℕ) : Measure (Space n) :=
  Measure.hausdorffMeasure (k : ℝ)

theorem hausdorffP_eq (n k : ℕ) :
    hausdorffP n k = Measure.hausdorffMeasure (k : ℝ) := rfl

section MetricSpaces

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Passing from a subset's metric to its ambient metric preserves Hausdorff measure. -/
theorem hausdorffMeasure_subtype_coe (k : ℕ) (A : Set X) (E : Set A) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure X) ((Subtype.val : A → X) '' E) =
      (Measure.hausdorffMeasure (k : ℝ) : Measure A) E :=
  isometry_subtype_coe.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg k)) E

/-- The upper image bound for a map on an arbitrary partial domain. -/
theorem hausdorffMeasure_subtype_image_le {A : Set X} {L : ℝ≥0} {f : A → Y}
    (hf : LipschitzWith L f) (k : ℕ) (E : Set A) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (f '' E) ≤
      (L : ℝ≥0∞) ^ k *
        (Measure.hausdorffMeasure (k : ℝ) : Measure X) ((Subtype.val : A → X) '' E) := by
  rw [hausdorffMeasure_subtype_coe]
  simpa only [ENNReal.rpow_natCast] using
    hf.hausdorffMeasure_image_le (Nat.cast_nonneg k) E

/-- The inverse metric bound gives the lower Hausdorff bound, also for infinite measure. -/
theorem hausdorffMeasure_subtype_image_ge {A : Set X} {l : ℝ≥0} {f : A → Y}
    (hl : 0 < l) (hf : AntilipschitzWith l⁻¹ f) (k : ℕ) (E : Set A) :
    (l : ℝ≥0∞) ^ k *
        (Measure.hausdorffMeasure (k : ℝ) : Measure X) ((Subtype.val : A → X) '' E) ≤
      (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (f '' E) := by
  rw [hausdorffMeasure_subtype_coe]
  have h := hf.le_hausdorffMeasure_image (Nat.cast_nonneg k) E
  rw [ENNReal.rpow_natCast] at h
  have hc : (l : ℝ≥0∞) * ((l⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.coe_inv (ne_of_gt hl)]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast ne_of_gt hl) ENNReal.coe_ne_top
  calc
    (l : ℝ≥0∞) ^ k * (Measure.hausdorffMeasure (k : ℝ) : Measure A) E ≤
        (l : ℝ≥0∞) ^ k *
          (((l⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k *
            (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (f '' E)) :=
      mul_le_mul_right h _
    _ = _ := by rw [← mul_assoc, ← mul_pow, hc, one_pow, one_mul]

/-- The corresponding upper bound when the function is given on the ambient space. -/
theorem hausdorffMeasure_image_le_of_subset {A E : Set X} {L : ℝ≥0} {f : X → Y}
    (hf : LipschitzOnWith L f A) (hE : E ⊆ A) (k : ℕ) :
    (Measure.hausdorffMeasure (k : ℝ) : Measure Y) (f '' E) ≤
      (L : ℝ≥0∞) ^ k * (Measure.hausdorffMeasure (k : ℝ) : Measure X) E := by
  simpa only [ENNReal.rpow_natCast] using
    (hf.mono hE).hausdorffMeasure_image_le (Nat.cast_nonneg k)

end MetricSpaces

section CompactRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem hausdorffMeasure_restrict_isFinite (k : ℕ) {K : Set X}
    (hfin : (Measure.hausdorffMeasure (k : ℝ) : Measure X) K < ∞) :
    IsFiniteMeasure ((Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict K) :=
  isFiniteMeasure_restrict.mpr hfin.ne

/-- Compactness is used on the subtype, not as a regularity assumption on ambient Hausdorff measure. -/
theorem hausdorffMeasure_restrict_innerRegular (k : ℕ) {K : Set X}
    (hK : IsCompact K) (hfin : (Measure.hausdorffMeasure (k : ℝ) : Measure X) K < ∞) :
    Measure.InnerRegular ((Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict K) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hmass : (Measure.hausdorffMeasure (k : ℝ) : Measure K) Set.univ =
      (Measure.hausdorffMeasure (k : ℝ) : Measure X) K := by
    simpa only [Set.image_univ, Subtype.range_coe] using
      (hausdorffMeasure_subtype_coe k K Set.univ).symm
  let : IsFiniteMeasure (Measure.hausdorffMeasure (k : ℝ) : Measure K) :=
    ⟨by rw [hmass]; exact hfin⟩
  have hreg : Measure.InnerRegular
      (Measure.map (Subtype.val : K → X) (Measure.hausdorffMeasure (k : ℝ) : Measure K)) :=
    Measure.InnerRegular.map_of_continuous continuous_subtype_val
  have hmap : Measure.map (Subtype.val : K → X)
      (Measure.hausdorffMeasure (k : ℝ) : Measure K) =
      (Measure.hausdorffMeasure (k : ℝ) : Measure X).restrict K := by
    simpa only [Subtype.range_coe] using
      (isometry_subtype_coe : Isometry (Subtype.val : K → X)).map_hausdorffMeasure
        (Or.inl (Nat.cast_nonneg k))
  rwa [hmap] at hreg

end CompactRestriction

theorem hausdorffP_restrict_isFinite {n k : ℕ} {K : Set (Space n)}
    (hfin : hausdorffP n k K < ∞) : IsFiniteMeasure ((hausdorffP n k).restrict K) :=
  hausdorffMeasure_restrict_isFinite k hfin

theorem hausdorffP_restrict_innerRegular {n k : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hfin : hausdorffP n k K < ∞) :
    Measure.InnerRegular ((hausdorffP n k).restrict K) :=
  hausdorffMeasure_restrict_innerRegular k hK hfin

theorem hausdorffP_singleton {n k : ℕ} (hk : 0 < k) (z : Space n) :
    hausdorffP n k {z} = 0 := by
  let := Measure.nullSingletonClass_hausdorff (Space n) (Nat.cast_pos.mpr hk : (0 : ℝ) < k)
  change (Measure.hausdorffMeasure (k : ℝ) : Measure (Space n)) {z} = 0
  exact measure_singleton z

theorem hausdorffP_zero_singleton {n : ℕ} (z : Space n) : hausdorffP n 0 {z} = 1 := by
  simpa only [hausdorffP, Nat.cast_zero] using Measure.hausdorffMeasure_zero_singleton z

end ParabolicRectifiability
