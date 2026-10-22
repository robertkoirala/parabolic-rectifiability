import ParabolicRectifiability.Enhancements.Statements.ScalingRates
import ParabolicRectifiability.Enhancements.Assembly.ScalingRates
import ParabolicRectifiability.Composition.MainTheoremOne
import ParabolicRectifiability.Foundations.Assembly.ProvedStatements

/-! # Scaled rectifiable Reifenberg theorem and energy rates

The scaled rectifiable Reifenberg theorem with graph-domain covers (`scaled_rectifiable_reifenberg`), the
power-energy rate (`power_rate`) and the gauge rate (`gauge_rate`). Each is obtained from
the corresponding implication `…_of_providers` by supplying the compact bridge cover and
the energy rescaling identity.
-/

namespace ParabolicRectifiability.Enhancements

/-- **Scaled rectifiable Reifenberg theorem on an arbitrary parent ball, with graph-domain covers.**
Statement: `ScaledRectifiableReifenbergStatement`. -/
theorem scaled_rectifiable_reifenberg : ScaledRectifiableReifenbergStatement := by
  exact scaled_rectifiable_reifenberg_of_providers Composition.compactBridgeCover_proof
    Foundations.squareEnergy_rescaledSource_eq

/-- **Power-energy rate, including zero energy.** Statement: `PowerRateStatement`. -/
theorem power_rate : PowerRateStatement := by
  exact power_rate_of_providers Composition.compactBridgeCover_proof
    Foundations.squareEnergy_rescaledSource_eq

/-- **Gauge rate and an approximated numerical infimum.** Statement:
`GaugeRateStatement`. -/
theorem gauge_rate : GaugeRateStatement := by
  exact gauge_rate_of_providers Composition.compactBridgeCover_proof
    Foundations.squareEnergy_rescaledSource_eq

end ParabolicRectifiability.Enhancements
