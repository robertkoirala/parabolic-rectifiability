import ParabolicRectifiability.IntegralCanonical.Statements.Integral
import ParabolicRectifiability.IntegralCanonical.Assembly.IntegralTests
import ParabolicRectifiability.Characterization.Theorems.Main

/-! # Exact integral tests for square finiteness and rectifiability

`integral_equivalences` identifies both capped limits with the source mass of the
infinite-energy set on every bounded Borel testing set. It then characterizes almost
everywhere finiteness by the five tests of `IntegralTest`: capped tails,
normalized capped values, compact exhaustion, a positive weight, and adaptive concave gauges.
Testing on expanding origin balls suffices for the four tests that use testing sets.

`integral_criterion` combines these tests with each of the two density conditions or the
intrinsic-source condition, giving all fifteen rectifiability criteria. The endpoint,
family-availability, and locally Radon hypotheses are stated in
`IntegralEquivalencesStatement` and `IntegralCriterionStatement`; every energy uses the
original source. The proofs are assembled in `integralEquivalences_skeleton` and
`integralCriterion_of_providers`, and the criterion uses
`Characterization.qualitative_characterization`.
-/

namespace ParabolicRectifiability.IntegralCanonical

/-- Exact detection of the infinite-square set: on a
bounded Borel `A`, both capped limits equal `μ(A ∩ {S¹ = ∞})`. For locally Radon `μ`,
`1 ≤ k ≤ n + 2`, and an available family, each of the five integral tests is equivalent
to `S¹ < ∞` almost everywhere; origin balls suffice for tests (1), (2), (4), (5). -/
theorem integral_equivalences : IntegralEquivalencesStatement := by
  exact ParabolicRectifiability.IntegralCanonical.integralEquivalences_skeleton

/-- All fifteen integral rectifiability criteria: pair
any of the three structural conditions with any of the five tests. For every positive
endpoint and available family this is equivalent to regular measure rectifiability,
and yields positive finite densities and graph covers at every positive tolerance.
The compact tests restrict testing points; they leave the energy source equal to `μ`. -/
theorem integral_criterion : IntegralCriterionStatement := by
  exact ParabolicRectifiability.IntegralCanonical.integralCriterion_of_providers ParabolicRectifiability.Characterization.qualitative_characterization

end ParabolicRectifiability.IntegralCanonical
