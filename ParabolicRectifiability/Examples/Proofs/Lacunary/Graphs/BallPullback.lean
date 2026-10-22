import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateStatements
import ParabolicRectifiability.Examples.Proofs.Lacunary.Support

/-! # Pulling back lacunary graph ball integrals

The snowflake isometry makes the graph map continuous and identifies each ball preimage with
an open time interval. Restricting the source only after this measurable preimage preserves
arbitrary time sets, without requiring those sets to be measurable.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- Pull back every nonnegative measurable ball integrand along the lacunary graph. -/
theorem e2_lacunary_ballPullback_proof :
    LacunaryIsometryStatement → E2BallPullbackStatement := by
  intro hiso ε a N hε hε' hd E t r hr g hg
  have hdist := hiso ε a N hε hε' hd
  have hF : Continuous (lacunaryGraphMap ε a N) :=
    (e2_isometry_time_of_dist hdist).continuous.comp
      Metric.Snowflaking.continuous_toSnowflaking
  have hpre : lacunaryGraphMap ε a N ⁻¹' Metric.ball (lacunaryGraphMap ε a N t) r =
      Ioo (t - r ^ 2) (t + r ^ 2) := by
    ext s
    simp only [mem_preimage, Metric.mem_ball, hdist, Real.sqrt_lt' hr, mem_Ioo,
      abs_lt]
    constructor
    · intro h
      constructor <;> linarith
    · intro h
      constructor <;> linarith
  rw [lacunarySource, setLIntegral_map Metric.isOpen_ball.measurableSet hg hF.measurable,
    Measure.restrict_restrict (Metric.isOpen_ball.measurableSet.preimage hF.measurable),
    hpre, inter_comm]

end ParabolicRectifiability.Examples
