import ParabolicRectifiability.BetaP.Statements.Main
import ParabolicRectifiability.BetaP.Proofs.Support.SupportTheorem
import ParabolicRectifiability.Composition.MainTheoremOne
import ParabolicRectifiability.Foundations.Proofs.Ambient.LocalCore
import ParabolicRectifiability.Foundations.Proofs.BetaPowLaws.BetaPowTwo
import ParabolicRectifiability.Characterization.Proofs.FiniteHausdorff.Criterion
import ParabolicRectifiability.Characterization.Assembly.Branches
import ParabolicRectifiability.BetaP.Proofs.Packing.MainPacking

/-! # Beta-`p` support decomposition and active-radius packing

`betaP_support_theorem` implements the unit, localized, and ambient clauses of
`BetaPSupportStatement`. It produces a nonnegative measure decomposition with compact
actual supports satisfying `HasRegularSupportBounds`; it does not identify the good
measures as restrictions to disjoint sets. One constant `C(n,p)` works for all admissible
dimensions, available families, sources, thresholds, and parent balls.

The active-radius endpoints bound the mass of the finite atomic source
`σ = Σ_i b_i r_i^k δ_{z_i}` from tails tested at each active radius. They include the
scale-truncated source, a unit-parent endpoint `2`, and exceptional indices with additive
loss exactly `Γ`. These packing results require `p ≥ 2` and `1 ≤ k < n + 2`.

Definitions and exact quantifiers are in `BetaPSupportStatement` and the
`ActiveRadiusPacking…Statement` definitions.
-/

namespace ParabolicRectifiability.BetaP

/-- The beta-`p` support theorem: for `p ≥ 2`, a weak threshold for
`S_p^{2R}` gives local loss `C M^{p/2} R^k + Γ`; for `0 < p ≤ 2`, a threshold for
`T_p^{2R}` gives `C M R^k + Γ`. The source is locally Radon, the family available,
and `C = C(n,p)` is uniform in the remaining data. Good measures and their actual compact
supports are fixed before graph tolerances. Zero thresholds are included; at `k = n + 2`
the unit-parent zero-loss conclusion requires no energy assumption. -/
theorem betaP_support_theorem : BetaPSupportStatement := by exact ParabolicRectifiability.BetaP.betaPSupport_of_providers ParabolicRectifiability.Composition.rectifiable_reifenberg_theorem ParabolicRectifiability.Foundations.f3_ambient_local_core_bounds_proof ParabolicRectifiability.Foundations.f3_betaPow_two_eq_betaSq_proof ParabolicRectifiability.Characterization.b4_finite_hausdorff_criterion ParabolicRectifiability.Characterization.typed_refinement_set_skeleton

/-- Active-radius packing for `p ≥ 2` and `1 ≤ k < n + 2`: disjoint
positive-radius balls in `P(q,R)` with `0 < b_i ≤ b` and full-source tails
`∫_{r_i}^∞ B_p(σ;z_i,s)^{2/p} ds/s ≤ B` satisfy
`σ(X) ≤ C(n,p) (b + B^{p/2}) R^k`. -/
theorem activeRadiusPacking : ActiveRadiusPackingStatement := by exact ParabolicRectifiability.BetaP.activeRadiusPacking_skeleton

/-- The active-radius mass bound with the source at each scale replaced by
`σ_s = Σ_{r_j ≤ s} b_j r_j^k δ_{z_j}`. Under `ActiveRadiusPackingTruncatedStatement`'s
packing hypotheses and tails over `(r_i,∞)`, the conclusion still bounds the total mass
of the original atomic source `σ` by `C(n,p) (b + B^{p/2}) R^k`. -/
theorem activeRadiusPacking_truncated : ActiveRadiusPackingTruncatedStatement := by exact ParabolicRectifiability.BetaP.activeRadiusPacking_truncated_skeleton

/-- For a packing in `P(q,1)`, the full atomic-source tails need only be integrated
over `(r_i,2)` to obtain `σ(X) ≤ C(n,p) (b + B^{p/2})`, for `p ≥ 2` and
`1 ≤ k < n + 2`. -/
theorem activeRadiusPacking_unitParent : ActiveRadiusPackingUnitParentStatement := by exact ParabolicRectifiability.BetaP.activeRadiusPacking_unitParent_skeleton

/-- If the all-scale tail condition holds outside a finite set of indices whose atomic
weights sum to at most `Γ`, the packing bound is
`σ(X) ≤ C(n,p) (b + B^{p/2}) R^k + Γ`. The testing source in each good-index tail remains
the full `σ`; the exceptional loss has coefficient one. -/
theorem activeRadiusPacking_exceptional : ActiveRadiusPackingExceptionalStatement := by exact ParabolicRectifiability.BetaP.activeRadiusPacking_exceptional_skeleton

/-- The unit-parent active-radius bound with tails over `(r_i,2)` required only outside
indices of total weight at most `Γ`: `σ(X) ≤ C(n,p) (b + B^{p/2}) + Γ`.
The source in the good-index tests remains the full atomic source. -/
theorem activeRadiusPacking_unitParent_exceptional :
    ActiveRadiusPackingUnitParentExceptionalStatement := by exact ParabolicRectifiability.BetaP.activeRadiusPacking_unitParent_exceptional_skeleton

end ParabolicRectifiability.BetaP
