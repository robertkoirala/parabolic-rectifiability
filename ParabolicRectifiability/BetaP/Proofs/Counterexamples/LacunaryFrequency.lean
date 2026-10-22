import ParabolicRectifiability.Examples.Proofs.Lacunary.Frequencies
import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces

/-! # Existence of lacunary frequencies

`c2_lacunaryFrequencyExistence` proves `LacunaryFrequencyExistence`, the existence of lacunary
frequencies for admissible amplitudes. The construction is `Examples.e2_lacunaryFrequencyExistence`;
`exact` closes the proposition by unfolding its definition.
-/

namespace ParabolicRectifiability.BetaP

/-- **Existence of lacunary frequencies**: `LacunaryFrequencyExistence`. -/
theorem c2_lacunaryFrequencyExistence : LacunaryFrequencyExistence :=
  Examples.e2_lacunaryFrequencyExistence

end ParabolicRectifiability.BetaP
