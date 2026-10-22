import ParabolicRectifiability.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Ordinary coordinates for parabolic space

Snowflaking changes the time metric but preserves its topology. The library
snowflake homeomorphism and product construction therefore identify parabolic
space with ordinary space-time coordinates. We put the Borel structure on
`Time` once and retain the library product measurable structure on `Space n`.
The library supplies product Borel compatibility and second countability,
including when `n = 0`.
-/

noncomputable section

namespace ParabolicRectifiability

/-- Ordinary space-time coordinates, with the library product structures. -/
abbrev Coordinates (n : ℕ) := Spatial n × ℝ

instance instMeasurableSpaceTime : MeasurableSpace Time := borel Time

instance instBorelSpaceTime : BorelSpace Time := ⟨rfl⟩

/-- Forget the snowflaked time metric while preserving the topology. -/
def coordinatesHomeomorph (n : ℕ) : Space n ≃ₜ Coordinates n :=
  (Homeomorph.refl (Spatial n)).prodCongr Metric.Snowflaking.homeomorph

@[simp]
theorem coordinatesHomeomorph_apply {n : ℕ} (z : Space n) :
    coordinatesHomeomorph n z = (z.1, z.2.val) := rfl

@[simp]
theorem coordinatesHomeomorph_symm_apply {n : ℕ} (y : Coordinates n) :
    (coordinatesHomeomorph n).symm y = point y.1 y.2 := rfl

@[simp]
theorem coordinatesHomeomorph_point {n : ℕ} (x : Spatial n) (t : ℝ) :
    coordinatesHomeomorph n (point x t) = (x, t) := rfl

/-- The same coordinate maps, for the Borel product measurable structures. -/
def coordinatesMeasurableEquiv (n : ℕ) : Space n ≃ᵐ Coordinates n :=
  (coordinatesHomeomorph n).toMeasurableEquiv

@[simp]
theorem coordinatesMeasurableEquiv_apply {n : ℕ} (z : Space n) :
    coordinatesMeasurableEquiv n z = (z.1, z.2.val) := rfl

@[simp]
theorem coordinatesMeasurableEquiv_symm_apply {n : ℕ} (y : Coordinates n) :
    (coordinatesMeasurableEquiv n).symm y = point y.1 y.2 := rfl

@[simp]
theorem coordinatesMeasurableEquiv_point {n : ℕ} (x : Spatial n) (t : ℝ) :
    coordinatesMeasurableEquiv n (point x t) = (x, t) := rfl

theorem continuous_spatial {n : ℕ} : Continuous (fun z : Space n => z.1) :=
  continuous_fst

theorem continuous_time {n : ℕ} : Continuous (fun z : Space n => z.2.val) :=
  continuous_snd.comp (coordinatesHomeomorph n).continuous

theorem measurable_spatial {n : ℕ} : Measurable (fun z : Space n => z.1) :=
  measurable_fst

theorem measurable_time {n : ℕ} : Measurable (fun z : Space n => z.2.val) :=
  measurable_snd.comp (coordinatesMeasurableEquiv n).measurable

/-- Joint continuity of the inverse coordinate map. -/
theorem continuous_point {n : ℕ} :
    Continuous (fun y : Coordinates n => point y.1 y.2) :=
  (coordinatesHomeomorph n).symm.continuous

/-- Joint measurability of the inverse coordinate map. -/
theorem measurable_point {n : ℕ} :
    Measurable (fun y : Coordinates n => point y.1 y.2) :=
  (coordinatesMeasurableEquiv n).symm.measurable

end ParabolicRectifiability
