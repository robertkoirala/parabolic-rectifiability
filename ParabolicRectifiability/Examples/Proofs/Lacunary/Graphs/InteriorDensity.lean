import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements

/-! # Interior density of the lacunary parameter interval

For an interior point, sufficiently small closed balls lie in `[-1,1]`.
Their positive finite Lebesgue measure cancels in the density quotient.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- Every strict interior point of the parameter interval is a Lebesgue density point. -/
theorem e2_interior_densityPoint_proof : E2InteriorDensityPointStatement := by
  intro t ht
  change Tendsto (fun r => volume (lacunaryInterval ∩ Metric.closedBall t r) /
    volume (Metric.closedBall t r)) (𝓝[>] (0 : ℝ)) (𝓝 1)
  have hmargin : 0 < min (1 + t) (1 - t) := by
    exact lt_min (by linarith [ht.1]) (by linarith [ht.2])
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds hmargin)] with r hr hsmall
  symm
  have hrpos : 0 < r := hr
  have hsub : Metric.closedBall t r ⊆ lacunaryInterval := by
    intro s hs
    have habs : |s - t| ≤ r := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hs
    obtain ⟨hleft, hright⟩ := abs_le.mp habs
    change -1 ≤ s ∧ s ≤ 1
    constructor
    · linarith [lt_of_lt_of_le hsmall (min_le_left (1 + t) (1 - t))]
    · linarith [lt_of_lt_of_le hsmall (min_le_right (1 + t) (1 - t))]
  rw [inter_eq_right.mpr hsub, Real.volume_closedBall]
  exact ENNReal.div_self
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith [hrpos] : 0 < 2 * r)))
    ENNReal.ofReal_ne_top

end ParabolicRectifiability.Examples
