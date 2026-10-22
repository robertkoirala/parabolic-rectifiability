import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.InverseHalfFourier

/-! # The normalized Fourier transform of `|t|^{-1/2}`

Proves `fhpbc_b2_inverseHalfFourier : FhpbcInverseHalfFourierStatement` under the name
`fhpbc_b2_inverseHalfFourier_proof`. The type has no hypotheses. The one-dimensional analysis
(Gaussian subordination with real Gamma integrals for nonzero variables, the Gaussian transform
and two absolutely convergent interchanges) is `FractionalKernel.fhpbb2f_inverseHalf_fourier_schwartz`;
this module only identifies `fhp_inverseHalfKernel t = |t|^{-1/2}`.
-/

namespace ParabolicRectifiability.Foundations

/-- **The normalized Fourier transform of `|t|^{-1/2}`.** For every `ψ : 𝓢(ℝ, ℂ)`,
`∫ |t|^{-1/2} ψ̂(t) dt = ∫ |τ|^{-1/2} ψ(τ) dτ` with Mathlib's Fourier phase and constant one. -/
theorem fhpbc_b2_inverseHalfFourier_proof : FhpbcInverseHalfFourierStatement := fun ψ =>
  FractionalKernel.fhpbb2f_inverseHalf_fourier_schwartz ψ

end ParabolicRectifiability.Foundations
