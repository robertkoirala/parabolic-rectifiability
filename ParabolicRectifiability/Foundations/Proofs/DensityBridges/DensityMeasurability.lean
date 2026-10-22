import ParabolicRectifiability.Foundations.Proofs.DensityBridges.DensityMeasurabilityLemmas
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Measurability of the upper and lower densities

`fmeas1_density_measurability : DensityMeasurabilityStatement` proves that the lower and upper
`k`-densities of a measure finite on compacts are measurable functions of the centre (the
statement of `densities_measurable_of_locallyRadon`).

Proof: each rational-radius ratio `z ↦ μ(P(z,q))/q^k` is measurable
(`fmeas1_measurable_ball_measure` followed by division by a constant); countable infima and
suprema of measurable `ℝ≥0∞`-valued functions are measurable; `fmeas1_densities_eq_rat`
identifies the two densities with these countable extrema. The inner regularity hypothesis is
not used.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The lower and upper `k`-densities of a measure finite on compacts are measurable. -/
theorem fmeas1_density_measurability : DensityMeasurabilityStatement := by
  intro n _ k _ _ μ hfin _
  have hq : ∀ r : ℝ, Measurable (fun z : Space n => densityRatio μ k z r) := fun r =>
    (measurable_div_const' (ENNReal.ofReal r ^ k)).comp (fmeas1_measurable_ball_measure μ hfin r)
  have hlow : lowerDensity μ k = fun z => ⨆ j : ℕ,
      ⨅ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / ((j : ℝ) + 1)}, densityRatio μ k z (q.1 : ℝ) :=
    funext fun z => (fmeas1_densities_eq_rat n μ k z).1
  have hup : upperDensity μ k = fun z => ⨅ j : ℕ,
      ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / ((j : ℝ) + 1)}, densityRatio μ k z (q.1 : ℝ) :=
    funext fun z => (fmeas1_densities_eq_rat n μ k z).2
  refine ⟨?_, ?_⟩
  · rw [hlow]
    exact Measurable.iSup fun j => Measurable.iInf fun q => hq _
  · rw [hup]
    exact Measurable.iInf fun j => Measurable.iSup fun q => hq _

end ParabolicRectifiability.Foundations
