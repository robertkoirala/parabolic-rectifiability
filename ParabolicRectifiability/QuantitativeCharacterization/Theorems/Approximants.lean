import ParabolicRectifiability.QuantitativeCharacterization.Statements.Approximants
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Approximants
import ParabolicRectifiability.Foundations.Proofs.AmbientEnergy
import ParabolicRectifiability.Characterization.Assembly.Branches
import ParabolicRectifiability.IntegralCanonical.Theorems.Canonical
import ParabolicRectifiability.BetaP.Proofs.Laws.Holder
import ParabolicRectifiability.BetaP.Proofs.Laws.Clamping
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo

/-! # Endpoints: approximants, local, bounded-support and ambient corollaries; common constants

The exact specifications in the `Statements` module of the same name are assembled from intrinsic
sufficiency, the canonical decomposition, the approximant constructions, and the Holder, clamping
and quadratic beta identities. The ambient case uses the vanishing of the ambient energy.
-/

set_option autoImplicit false

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **Approximants of a covering.** Exact statement: `MeasureApproximantsStatement`. -/
theorem measure_approximants : MeasureApproximantsStatement := by
  exact measure_approximants_of_providers ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton ParabolicRectifiability.IntegralCanonical.canonical_decomposition

/-- **The local forward and reverse clauses.** Exact statement: `UniformLocalStatement`. -/
theorem uniform_local : UniformLocalStatement := by
  exact uniform_local_of_providers ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton

/-- **The bounded-support case.** Exact statement: `BoundedSupportStatement`. -/
theorem bounded_support : BoundedSupportStatement := by
  exact bounded_support_of_providers ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton ParabolicRectifiability.IntegralCanonical.canonical_decomposition

/-- **The ambient case `k = n + 2`.** Exact statement: `AmbientEndpointStatement`. -/
theorem ambient_endpoint : AmbientEndpointStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.ambient_endpoint_of_providers (fun n hn μ _ _ T hT => ParabolicRectifiability.Foundations.ambient_betaSq_squareEnergy_eq_zero_proof n hn μ T hT)

/-- Common constants `L₀, C` (and `B_loc`, `C(A,k)`) of the quantitative characterization and its local,
bounded-support and beta-`p` corollaries. Exact statement:
`QuantitativeCommonConstantsStatement`. -/
theorem quantitative_common_constants : QuantitativeCommonConstantsStatement := by
  exact quantitative_common_constants_of_providers ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton ParabolicRectifiability.IntegralCanonical.canonical_decomposition ParabolicRectifiability.BetaP.claws_holder_proof ParabolicRectifiability.BetaP.cclamp_betaPowClamping_proof ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof

end ParabolicRectifiability.QuantitativeCharacterization
