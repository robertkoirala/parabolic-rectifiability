import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Spec.Basic

/-! Specification: the definitions of `ParabolicRectifiability.Metric.Space` used by the headline statements. -/

noncomputable section
namespace ParabolicRectifiability
/-- Ordinary space-time coordinates, with the library product structures. -/
abbrev Coordinates (n : ℕ) := Spatial n × ℝ

instance instMeasurableSpaceTime : MeasurableSpace Time := borel Time

instance instBorelSpaceTime : BorelSpace Time := by
  sorry

/-- Forget the snowflaked time metric while preserving the topology. -/
def coordinatesHomeomorph (n : ℕ) : Space n ≃ₜ Coordinates n :=
  (Homeomorph.refl (Spatial n)).prodCongr Metric.Snowflaking.homeomorph

end ParabolicRectifiability
