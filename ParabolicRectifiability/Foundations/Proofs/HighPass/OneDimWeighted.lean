import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.OneDimWeighted

/-! # The weighted one-dimensional estimate

Proof of `fhpbc_b1_oneDimWeighted : FhpbcOneDimWeightedStatement`. The one-dimensional analysis
is `ParabolicRectifiability.FractionalKernel.fhpbb1w_oneDimWeighted`, stated for an arbitrary
real normalization; this wrapper specializes it to `κ = FractionalKernel.kappa`, so that the
operator is exactly `fhpbc_halfDeriv1D` (definitional unfolding).
-/

namespace ParabolicRectifiability.Foundations

/-- **The weighted one-dimensional estimate** (`fhpbc_b1_oneDimWeighted`): a universal `C ≥ 0` with
`∫⁻ (1 + √|t|) ‖D f t‖ₑ ≤ C ∫⁻ (1 + |t|) (‖f t‖ₑ + ‖f' t‖ₑ)` for every integrable `C¹`
`f : ℝ → ℂ` with `∫ f = 0`, where `D = fhpbc_halfDeriv1D`. -/
theorem fhpbc_b1_oneDimWeighted_proof : FhpbcOneDimWeightedStatement :=
  FractionalKernel.fhpbb1w_oneDimWeighted FractionalKernel.kappa

end ParabolicRectifiability.Foundations
