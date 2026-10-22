import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.InverseHalfAsymptotic

/-! # Asymptotic expansion of `ρ * I`

Proof of `fhpbc_b2_inverseHalfAsymptotic : FhpbcInverseHalfAsymptoticStatement`. The
one-dimensional analysis is
`ParabolicRectifiability.FractionalKernel.fhpbb2a_inverseHalf_asymptotic`; this wrapper only
unfolds `fhp_inverseHalfKernel t = |t|^{-1/2}`.
-/

namespace ParabolicRectifiability.Foundations

/-- **Asymptotic expansion of `ρ * I`** (`fhpbc_b2_inverseHalfAsymptotic`): for a real Schwartz `ρ` and every `N`,
`∫ ρ(s) I(t-s) ds = Σ_{k<N} ((-1)^k / k!) (∫ s^k ρ) I^{(k)}(t) + O(|t|^{-N})` on `|t| ≥ 1`,
with `I(t) = |t|^{-1/2}` (`fhp_inverseHalfKernel`). -/
theorem fhpbc_b2_inverseHalfAsymptotic_proof : FhpbcInverseHalfAsymptoticStatement :=
  fun ρ N => FractionalKernel.fhpbb2a_inverseHalf_asymptotic ρ N

end ParabolicRectifiability.Foundations
