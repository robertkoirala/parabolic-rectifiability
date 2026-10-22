import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.OneDimUnweighted

/-! # The unweighted one-dimensional estimate

Proof of `fhpbc_b1_oneDimUnweighted : FhpbcOneDimUnweightedStatement`. The one-dimensional
analysis is `ParabolicRectifiability.FractionalKernel.fhpbb1u_oneDimUnweighted`, stated for an
arbitrary real normalization; this wrapper specializes it to `κ = FractionalKernel.kappa`, so that the operator
is exactly `fhpbc_halfDeriv1D` (definitional unfolding).
-/

namespace ParabolicRectifiability.Foundations

/-- **The unweighted one-dimensional estimate** (`fhpbc_b1_oneDimUnweighted`): a universal `C ≥ 0` with
`∫⁻ ‖D f t‖ₑ ≤ C ∫⁻ (‖f t‖ₑ + ‖f' t‖ₑ)` for every `C¹` `f : ℝ → ℂ`, where
`D = fhpbc_halfDeriv1D`. No integrability of `f` is assumed. -/
theorem fhpbc_b1_oneDimUnweighted_proof : FhpbcOneDimUnweightedStatement :=
  FractionalKernel.fhpbb1u_oneDimUnweighted FractionalKernel.kappa

end ParabolicRectifiability.Foundations
