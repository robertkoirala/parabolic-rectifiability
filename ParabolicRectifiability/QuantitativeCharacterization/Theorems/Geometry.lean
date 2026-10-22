import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceEstimates
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Monotonicity

/-!
# Beta scaling, quantitative monotonicity and reference estimates

`beta_scaling` gives the exact normalized mixed-beta identity under positive
parabolic rescaling. `isQuantitativelyMixedRectifiable_mono` increases the
allowed quantitative constants. `reference_estimates` supplies global ADR and
own-type Carleson estimates for the defined reference classes; these estimates
are outputs rather than premises in their definitions.

The exact contracts are in the `Statements` module of the same name. The proofs use the beta
rescaling law `betaSq_rescaledSource`, `quantitativeRectifiability_mono_skeleton` and
`ba1_reference_estimates`.
-/

set_option autoImplicit false

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **The scaling identity.** From `betaSq_rescaledSource` at the centre
`(similarity a R hR).symm z`. -/
theorem beta_scaling : BetaScalingStatement := by
  intro n _ k _ _ μ a R hR z r hr
  have h := betaSq_rescaledSource μ k .mixed a R hR ((similarity a R hR).symm z) hr
  rwa [Homeomorph.apply_symm_apply] at h

/-- Increasing either quantitative constant preserves the covering
property: from `1 ≤ K ≤ K′` and `1 ≤ L ≤ L′`, an `(K,L)` source is also
an `(K′,L′)` source. The precise locally Radon and dimension hypotheses
are in `QuantitativeRectifiabilityMonoStatement`. -/
theorem isQuantitativelyMixedRectifiable_mono : QuantitativeRectifiabilityMonoStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.quantitativeRectifiability_mono_skeleton

/-- **Reference estimates.** Closed by `ba1_reference_estimates`. -/
theorem reference_estimates : ReferenceEstimatesStatement := by
  exact ba1_reference_estimates

end ParabolicRectifiability.QuantitativeCharacterization
