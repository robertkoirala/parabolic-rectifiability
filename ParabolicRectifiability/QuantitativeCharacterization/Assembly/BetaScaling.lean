import ParabolicRectifiability.QuantitativeCharacterization.Assembly.ComponentStatements

/-! # Beta scaling and the reference estimates

* `beta_scaling_skeleton` is proved from the base theorem `betaSq_rescaledSource`.
* `reference_estimates_skeleton` is the statement `reference_estimates` itself.
* Monotonicity is `quantitativeRectifiability_mono_skeleton`.
-/

set_option autoImplicit false

namespace ParabolicRectifiability.QuantitativeCharacterization

/-- **The scaling identity.** Proved from
`betaSq_rescaledSource` at the centre `(similarity a R hR).symm z`. -/
theorem beta_scaling_skeleton : BetaScalingStatement := by
  intro n _ k _ _ μ a R hR z r hr
  have h := betaSq_rescaledSource μ k .mixed a R hR ((similarity a R hR).symm z) hr
  rwa [Homeomorph.apply_symm_apply] at h

/-- **Reference estimates**: the statement `reference_estimates`. -/
theorem reference_estimates_skeleton : ReferenceEstimatesStatement :=
  reference_estimates

end ParabolicRectifiability.QuantitativeCharacterization
