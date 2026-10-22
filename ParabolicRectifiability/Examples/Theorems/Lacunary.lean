import ParabolicRectifiability.Examples.Statements.Lacunary
import ParabolicRectifiability.Examples.Assembly.Lacunary
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFiniteness
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.EnergyTwo

/-! # Lacunary space-time graphs and exponent witnesses

For admissible `ε`, amplitudes, and frequencies (`Examples.IsLacunaryData`),
`lacunary_convergence` proves absolute summability and uniform convergence of the primitive.
`lacunary_estimates` provides its snowflake isometry, exact ball and Hausdorff identities,
density limits, upper and restriction-stable lower energy bounds, and small-slope covers.
The lower-bound tail index is chosen before the exponent.

With `a_j = (j+1)^{-1/2}`, `lacunary_nonregular` gives a compact graph of positive finite
`H_P²` measure admitting ordinary covers at every positive slope but no regular graph
cover. `lacunary_exponent_witnesses` adds the complementary `T_p` examples above and below
`p = 2`, including a general regular full function with divergent `T_p` when `p < 2`.
These are graphs and sources in `Space 1` with parabolic dimension `2`, not time-slice
rectifiability assertions.

The construction is `lacunaryFunction`; the exact statements are
`LacunaryConvergenceStatement`, `LacunaryEstimatesStatement`, `NonregularStatement` and
`ExponentWitnessesStatement`.
-/

namespace ParabolicRectifiability.Examples

/-- For `0 < ε ≤ 3/16` and `IsLacunaryData a N`, the primitive series is absolutely
summable at every real time and its finite partial sums converge uniformly on `ℝ` to
`lacunaryFunction ε a N`. -/
theorem lacunary_convergence : LacunaryConvergenceStatement := by
  exact ParabolicRectifiability.Examples.lacunary_convergence_skeleton

/-- The lacunary graph estimates:
isometry for `√|t-s|`, exact ball and Hausdorff identities, density and ADR statements,
all-scale upper `T_q` bounds for `q ≥ 1`, and restriction-stable lower bounds for `q > 0`.
At each density point and positive endpoint the lower-bound tail index works for all
`q > 0`. If `a_j → 0`, finitely many ordinary full vertical graphs give an exact cover
of the fixed graph at every positive slope. The full quantifiers are in
`LacunaryEstimatesStatement`. -/
theorem lacunary_estimates : LacunaryEstimatesStatement := by
  exact ParabolicRectifiability.Examples.lacunary_estimates_skeleton

/-- For `a_j = (j+1)^{-1/2}`, the compact lacunary graph has positive finite `H_P²`
measure and ordinary graph covers at every positive slope, but its source is null on
every finite-norm general regular vertical graph and is not regularly rectifiable.
The square diverges on every positive-measure parameter restriction, while for `p > 2`
the all-scale `T_p` energy is uniformly at most `C_p ε^p`. -/
theorem lacunary_nonregular : NonregularStatement := by
  exact ParabolicRectifiability.Examples.nonregular_of_providers ParabolicRectifiability.Characterization.b2_graph_source_square_finite ParabolicRectifiability.Foundations.f2c_energyTwo_proof

/-- Complementary `T_p` witnesses.
Above `2`, a mass-`1/2` lacunary source in the unit ball has small positive integrated
`T_p` energy and vanishes on countably regular carriers with Hausdorff-null residuals.
Below `2`, square-summable amplitudes outside every `ℓ^p`, `0 < p < 2`, give a full
general regular function whose `T_p^R` diverges at every interior parameter point and
every `R > 0`; its half-time derivative is also specified as a periodic `L²` limit. -/
theorem lacunary_exponent_witnesses : ExponentWitnessesStatement := by
  exact exponent_witnesses_of_providers
    ParabolicRectifiability.Characterization.b2_graph_source_square_finite
    ParabolicRectifiability.Foundations.f2c_energyTwo_proof

end ParabolicRectifiability.Examples
