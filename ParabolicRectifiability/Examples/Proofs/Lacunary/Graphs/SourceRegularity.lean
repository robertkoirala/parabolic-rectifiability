import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support

/-!
# Finite and absolutely continuous lacunary sources

Bounded parameter restriction gives finiteness. Continuity of the graph map
then permits evaluating its pushforward on a measurable null hull. The exact
Hausdorff image identity is an outer-measure identity on every parameter set,
so it applies to the intersection with a merely null-measurable restriction.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The restricted graph source is finite, inner regular, and absolutely
continuous with respect to parabolic two-dimensional Hausdorff measure. -/
theorem e2_lacunarySource_finite_ac_proof :
    E2HausdorffExactStatement → LacunaryIsometryStatement →
    ∀ (ε : ℝ) (a : ℕ → ℝ) (N : ℕ → ℕ), 0 < ε → ε ≤ 3 / 16 → IsLacunaryData a N →
    ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ lacunaryInterval →
      IsFiniteMeasure (lacunarySource ε a N E) ∧ (lacunarySource ε a N E).InnerRegular ∧
        lacunarySource ε a N E ≪ hausdorffP 1 2 := by
  intro hHaus hIso ε a N hε hε' hd E _hE hEJ
  have hF : Continuous (lacunaryGraphMap ε a N) :=
    (e2_isometry_time_of_dist (hIso ε a N hε hε' hd)).continuous.comp
      Metric.Snowflaking.continuous_toSnowflaking
  have hEfinite : volume E < ∞ := by
    apply lt_of_le_of_lt (measure_mono hEJ)
    simp [lacunaryInterval, Real.volume_Icc]
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hEfinite.ne
  let : IsFiniteMeasure (lacunarySource ε a N E) :=
    Measure.isFiniteMeasure_map (volume.restrict E) (lacunaryGraphMap ε a N)
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro A hA
  obtain ⟨B, hAB, hB, hBzero⟩ := exists_measurable_superset_of_null hA
  have hImage : lacunaryGraphMap ε a N '' (lacunaryGraphMap ε a N ⁻¹' B ∩ E) ⊆ B := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht.1
  have hPreimage : volume (lacunaryGraphMap ε a N ⁻¹' B ∩ E) = 0 := by
    rw [← hHaus ε a N hε hε' hd]
    exact measure_mono_null hImage hBzero
  have hSource : lacunarySource ε a N E B = 0 := by
    rw [lacunarySource, Measure.map_apply hF.measurable hB,
      Measure.restrict_apply (hF.measurable hB)]
    exact hPreimage
  exact measure_mono_null hAB hSource

end ParabolicRectifiability.Examples
