import ParabolicRectifiability.Foundations.Statements.Ambient
import ParabolicRectifiability.Foundations.Proofs.AmbientEnergy
import ParabolicRectifiability.Foundations.Proofs.AmbientCover
import ParabolicRectifiability.Foundations.Proofs.Ambient.LocalCore
import ParabolicRectifiability.Foundations.Proofs.Ambient.Densities
import ParabolicRectifiability.Foundations.Proofs.Ambient.Characterization

/-! # The ambient case `k = n + 2`

Theorems for the ambient case. The exact propositions are the statement definitions
`AmbientEnergyZeroStatement`, `AmbientZeroGraphCoverStatement`,
`AmbientCharacterizationStatement`, `AmbientAbsolutelyContinuousDensityStatement` and
`AmbientLocalCoreStatement`.

The fifth clause ("the ambient core has zero remainder without an energy assumption")
is proved at every local scale `P(q,R)` as `ambient_local_core`
(`AmbientLocalCoreStatement`). The theorem
`ParabolicRectifiability.ambient_rectifiability : AmbientRectifiabilityStatement`
covers only the unit ball `P(0,1)`; it is a cross-reference, not the statement of the clause.

The first clause is stated in its locally Radon form (`ambient_energy_zero`) and, separately,
in the arbitrary-measure generalization (`ambient_energy_zero_arbitrary_source`); both are
proved from `ambient_betaSq_squareEnergy_eq_zero_proof`.
-/

namespace ParabolicRectifiability.Foundations

/-- First clause: at `k = n + 2` every
available natural beta and square function of a locally Radon source vanishes
identically. Proved by `ambient_betaSq_squareEnergy_eq_zero_proof` with the two locally Radon
hypotheses discarded. -/
theorem ambient_energy_zero : AmbientEnergyZeroStatement := by
  exact fun n hn μ _ _ T hT => ParabolicRectifiability.Foundations.ambient_betaSq_squareEnergy_eq_zero_proof n hn μ T hT

/-- Generalization of the first clause to an arbitrary measure: at `k = n + 2` every
available natural beta and square function vanishes identically. Proved by
`ambient_betaSq_squareEnergy_eq_zero_proof`. -/
theorem ambient_energy_zero_arbitrary_source :
    AmbientEnergyZeroArbitrarySourceStatement := by
  exact ParabolicRectifiability.Foundations.ambient_betaSq_squareEnergy_eq_zero_proof

/-- Second clause: the zero-function full
regular graph is all of `X` at every positive tolerance, and every set is regularly
`(n + 2)`-rectifiable of vertical and of mixed type. Proved by
`ambient_zero_graph_cover_all_proof`. -/
theorem ambient_zero_graph_cover : AmbientZeroGraphCoverStatement := by
  exact ParabolicRectifiability.Foundations.ambient_zero_graph_cover_all_proof

/-- Third clause: for locally Radon `μ`,
regular `(n + 2)`-rectifiability (mixed or vertical) `↔ μ ≪ H_P^{n+2}` `↔`
`0 < Θ^{n+2,*} < ∞` `μ`-almost everywhere. -/
theorem ambient_characterization : AmbientCharacterizationStatement := by
  exact ParabolicRectifiability.Foundations.f2i_ambient_rectifiable_iff_ac_iff_density

/-- Fourth clause: a locally Radon
`μ ≪ L^{n+1}` has positive finite lower and upper `(n + 2)`-densities `μ`-almost
everywhere. -/
theorem ambient_absolutely_continuous_density :
    AmbientAbsolutelyContinuousDensityStatement := by
  exact ParabolicRectifiability.Foundations.f2i_ambientDensities_proof

/-- Fifth clause: for a locally Radon `μ` and
every `P(q,R)`, the decomposition `μ = μ⌊P(q,R)ᶜ + μ⌊P(q,R)` has zero remainder on
`P(q,R)`, and `supp(μ⌊P(q,R))` satisfies the regular support bounds at `n + 2`, with one
dimensional constant and no energy assumption. -/
theorem ambient_local_core : AmbientLocalCoreStatement := by
  exact ParabolicRectifiability.Foundations.f3_ambient_local_core_bounds_proof

end ParabolicRectifiability.Foundations
