import ParabolicRectifiability.Enhancements.Statements.GraphDomains
import ParabolicRectifiability.Enhancements.Assembly.GraphDomains
import ParabolicRectifiability.Composition.MainTheoremOne

/-!
# Graph-domain covers on fixed compact carriers

`graphDomainCover_of_fixedCarrier` turns every-small-tolerance graph coverage
in one available horizontal or vertical family on a compact finite-Hausdorff
carrier into graph-domain cover data. Trace sets and preimages are Borel, patch
radii are positive and at most the requested mesh, and the patch charges
satisfy the relative global and local bounds.

`graph_enhanced_rectifiable_reifenberg` applies that construction to the same actual
supports selected by the rectifiable Reifenberg theorem. Supports are chosen before
both graph tolerance and mesh. The proof is assembled in
`fixed_carrier_graph_domain_skeleton` and `graph_enhanced_of_main_and_fixedCarrier`; exact
quantifiers and the additional local-growth estimate are in
`FixedCarrierGraphDomainStatement` and `GraphEnhancedRectifiableReifenbergStatement`.
-/

namespace ParabolicRectifiability.Enhancements

/-- For `n ≥ 1` and `1 ≤ k ≤ n+2`, a compact carrier of finite `H_P^k` measure
with covers in one available horizontal or vertical family at every positive
tolerance admits graph-domain covers at every positive tolerance and mesh.
The constant depends only on `n`. The same chosen cover satisfies the local
charge estimate `C * A * R^k` under any subsequent local-growth bound
`H_P^k(K ∩ P(q,s)) ≤ A*s^k`, for `0 < 2R ≤ R_*`. -/
theorem graphDomainCover_of_fixedCarrier : FixedCarrierGraphDomainStatement := by
  exact fixed_carrier_graph_domain_skeleton

/-- The rectifiable Reifenberg conclusion with graph-domain covers of its fixed
actual supports at every `ε, δ > 0`. One dimensional constant controls both
the original remainder `C * M + Γ` and total/local patch charges. Mixed,
available fixed-family, zero-threshold and ambient cases are retained. -/
theorem graph_enhanced_rectifiable_reifenberg : GraphEnhancedRectifiableReifenbergStatement := by
  exact graph_enhanced_of_main_and_fixedCarrier Composition.rectifiable_reifenberg_theorem
    fixed_carrier_graph_domain_skeleton

end ParabolicRectifiability.Enhancements
