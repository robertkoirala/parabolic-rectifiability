import ParabolicRectifiability.BetaP.Proofs.Comparison.ComparisonStatements
import ParabolicRectifiability.BetaP.Proofs.Laws.Annulus
import ParabolicRectifiability.Foundations.Proofs.UpperDensityBound
import ParabolicRectifiability.BetaP.Proofs.Comparison.SmallScaleBelowTwo
import ParabolicRectifiability.BetaP.Proofs.Comparison.EnergyEndpoint
import ParabolicRectifiability.BetaP.Proofs.Comparison.SmallScaleAboveTwo

/-! # Pointwise comparison of `S_p` and `S_2`: the intermediate results

The intermediate results used for `energyS_lt_top_of_squareEnergy_lt_top` and
`squareEnergy_lt_top_of_energyS_lt_top`, each a restatement of the corresponding `…_proof`
theorem, together with the finite-annulus law `c2_cmp_input_annulus`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Finite annuli**: the law `BetaPowAnnulusStatement` (as in `betaPowAnnulus_law`), proved by
`c2_betaPowAnnulus_proof`; used through `c2_energyS_endpoint`. -/
theorem c2_cmp_input_annulus : BetaPowAnnulusStatement := by exact ParabolicRectifiability.BetaP.c2_betaPowAnnulus_proof

/-- **Upper-density bound** (`c2_UpperDensityBoundStatement`), used in both directions. -/
theorem c2_upperDensity_bound : c2_UpperDensityBoundStatement := by exact ParabolicRectifiability.Foundations.f2c_upperDensity_bound_proof

/-- **Small scales below two** (`c2_CmpLtSmallScaleStatement`). -/
theorem c2_cmpLt_smallScale : c2_CmpLtSmallScaleStatement := by exact ParabolicRectifiability.BetaP.c2_cmpLt_smallScale_proof

/-- **`S_p` endpoint completion** (`c2_EnergySEndpointStatement`, with the finite-annulus law as
a hypothesis). -/
theorem c2_energyS_endpoint : c2_EnergySEndpointStatement := by exact ParabolicRectifiability.BetaP.c2_energyS_endpoint_proof

/-- **Small scales above two** (`c2_CmpGtSmallScaleStatement`). -/
theorem c2_cmpGt_smallScale : c2_CmpGtSmallScaleStatement := by exact ParabolicRectifiability.BetaP.c2_cmpGt_smallScale_proof

end ParabolicRectifiability.BetaP
