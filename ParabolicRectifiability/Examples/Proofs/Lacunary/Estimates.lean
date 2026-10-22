import ParabolicRectifiability.Examples.Proofs.Lacunary.EstimateLemmas
import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyLemmas
import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionLemmas

/-! # The lacunary estimates: assembly

Assembles `LacunaryEstimatesStatement` (isometry, exact ball measure, Hausdorff identity,
density limits, full-interval density, upper and lower energy bounds, small slope) from the
intermediate lacunary estimates.

* `e2_lacunary_estimates_of : E2LacunaryWeightStatement → E2StationaryLengthStatement →
  LacunaryEstimatesStatement` (implication form over the weight estimate and the stationary-phase
  length bound);
* `e2_lacunary_estimates : LacunaryEstimatesStatement`, with the same type as
  `Examples.lacunary_estimates_bundle` and `Examples.lacunary_estimates`.

The intermediate consequences `e2_isometry_of`, `e2_ballMeasure_of`, `e2_hausdorff_of`,
`e2_hausdorffExact_of`, `e2_plateauBeta_of` and `e2_lowerEnergy_of` are also used for the source
regularity, carried restriction and positive energy of the lacunary graph.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The isometry property of the lacunary graph, from the weight estimate, through the kernel
bound, the kernel sum bound and the reciprocal-square-root decay. -/
theorem e2_isometry_of (hW : E2LacunaryWeightStatement) : LacunaryIsometryStatement :=
  e2_lacunary_isometry (e2_lacunary_kernelBound hW) e2_kernelSum_le e2_lacunary_invSqrtDecay

/-- The exact ball identity is the ball pullback at `g = 1`. -/
theorem e2_ballMeasure_of (hGB : E2BallPullbackStatement) : LacunaryBallMeasureStatement := by
  intro ε a N hε hε' hd E _ _ t r hr
  have h := hGB ε a N hε hε' hd E t r hr (fun _ => 1) measurable_const
  simpa only [setLIntegral_one] using h

/-- The exact Hausdorff identity `H_P²(F(E)) = |E|`, using the isometry obtained from the weight
estimate. -/
theorem e2_hausdorffExact_of (hW : E2LacunaryWeightStatement) : E2HausdorffExactStatement :=
  e2_lacunary_hausdorffExact e2_time_hausdorff (e2_isometry_of hW)

/-- The Hausdorff identity with `c_H = 1`. -/
theorem e2_hausdorff_of (hH : E2HausdorffExactStatement) : LacunaryHausdorffStatement :=
  ⟨1, one_pos, fun ε a N hε hε' hd E _ _ => by
    rw [hH ε a N hε hε' hd E, ENNReal.ofReal_one, one_mul]⟩

/-- The plateau beta bound from the weight estimate, through the ball pullback and the plateau
error and lower bounds. Also used for the positive integrated energy. -/
theorem e2_plateauBeta_of (hW : E2LacunaryWeightStatement) : E2PlateauBetaStatement :=
  e2_plateau_beta (e2_lacunary_ballPullback (e2_isometry_of hW))
    (e2_plateau_lower (e2_plateau_error hW) e2_cosPlateau)

/-- The lower energy bound. The second clause (`E = J`, every interior point) is the first
clause at `E = J`, since interior points of `J` are density points of `J`. -/
theorem e2_lowerEnergy_of (hL : E2LowerEnergyFirstStatement)
    (hI : E2InteriorDensityPointStatement) : LacunaryLowerEnergyStatement := by
  obtain ⟨c, hc, h1⟩ := hL
  refine ⟨c, hc, fun ε a N hε hε' hd => ⟨h1 ε a N hε hε' hd, fun t ht R hR => ?_⟩⟩
  exact h1 ε a N hε hε' hd lacunaryInterval measurableSet_Icc.nullMeasurableSet subset_rfl t
    ⟨Ioo_subset_Icc_self ht, ht⟩ (hI t ht) R hR

/-- **The lacunary estimates**, in implication form over the weight estimate
`E2LacunaryWeightStatement` and the stationary-phase length bound `E2StationaryLengthStatement`. -/
theorem e2_lacunary_estimates_of (hW : E2LacunaryWeightStatement)
    (hSP : E2StationaryLengthStatement) : LacunaryEstimatesStatement := by
  have hKB : E2KernelBoundStatement := e2_lacunary_kernelBound hW
  have hiso : LacunaryIsometryStatement := e2_isometry_of hW
  have hGB : E2BallPullbackStatement := e2_lacunary_ballPullback hiso
  have hball : LacunaryBallMeasureStatement := e2_ballMeasure_of hGB
  refine ⟨hiso, hball, e2_hausdorff_of (e2_hausdorffExact_of hW),
    e2_lacunary_densityLimit hball, e2_lacunary_fullInterval hball hSP,
    e2_lacunary_upperEnergy (e2_lacunary_testBound hGB hKB) e2_kernelJensen
      e2_kernelLogIntegral e2_kernelSum_le e2_lacunary_invSqrtDecay,
    e2_lowerEnergy_of
      (e2_lacunary_lowerFirst (e2_plateauBeta_of hW) e2_betaPow_band e2_lacunary_occupancy
        e2_lacunary_invSqrtDecay)
      e2_interior_densityPoint,
    e2_lacunary_smallSlope (e2_lacunary_littleHolder hKB e2_kernelSum_le e2_lacunary_invSqrtDecay)
      e2_snowflake_extension⟩

/-- **The lacunary estimates.** The type is that of `Examples.lacunary_estimates_bundle`; the
two hypotheses of `e2_lacunary_estimates_of` are supplied by `e2_lacunaryWeight` and
`e2_stationary_length`. -/
theorem e2_lacunary_estimates : LacunaryEstimatesStatement :=
  e2_lacunary_estimates_of e2_lacunaryWeight e2_stationary_length

end ParabolicRectifiability.Examples
