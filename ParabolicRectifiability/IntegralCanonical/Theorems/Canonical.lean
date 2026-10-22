import ParabolicRectifiability.IntegralCanonical.Statements.Canonical
import ParabolicRectifiability.IntegralCanonical.Assembly.CanonicalDecomposition
import ParabolicRectifiability.Foundations.Proofs.AmbientEnergy
import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.DensityBridgeAndTypeSeparationProofs
import ParabolicRectifiability.Characterization.Assembly.Branches
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFiniteness
import ParabolicRectifiability.Foundations.Proofs.SquareEnergyBounds

/-! # The canonical horizontal, vertical, and graph-pure decomposition

The canonical parts are restrictions of the original source to its horizontal finite-energy,
vertical finite-energy, and infinite-mixed-energy sets (`horizontalPart`, `verticalPart`,
`purePart`).
Under the intrinsic-source assumption, or positive finite upper density almost everywhere,
`canonical_decomposition` proves that these parts sum to the source, are pairwise singular,
and are respectively horizontally rectifiable, vertically rectifiable, and graph-pure.
The parts are independent of the positive endpoint and unique among all nonnegative
decompositions with those three properties.

`isIntrinsicSource_of_upperDensity` supplies the density bridge. `type_separation` proves
the quantitative projection inequality and Hausdorff nullity for intersections of a small
horizontal graph with an ordinary full vertical graph. `canonical_guards` handles missing
types, the ambient endpoint, and the possible literal overlap for the zero source.
The exact statements are `IntrinsicSourceOfDensityStatement`, `CanonicalDecompositionStatement`,
`TypeSeparationStatement` and `CanonicalGuardsStatement`; the proofs use
`canonicalDecomposition_of_providers`, `canonicalGuards_of_providers`, the graph-source square
finiteness `Characterization.b2_graph_source_square_finite` and the ambient-energy identity
`Foundations.ambient_betaSq_squareEnergy_eq_zero_proof`.
-/

namespace ParabolicRectifiability.IntegralCanonical

/-- Positive finite upper `k`-density almost everywhere implies `μ ≪ H_P^k` and a Borel
sigma-finite `H_P^k` carrier for a locally Radon source in `1 ≤ k ≤ n + 2`.
No square-energy hypothesis is needed. -/
theorem isIntrinsicSource_of_upperDensity : IntrinsicSourceOfDensityStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_isIntrinsicSource_of_hasPositiveFiniteUpperDensity

/-- The full canonical decomposition for a locally Radon intrinsic source, or one with
positive finite upper density almost everywhere.
At every `R > 0`, the full-source energy sets define pairwise singular restrictions
`μ_H`, `μ_V`, `μ_+`, with typed rectifiability, graph purity, endpoint independence, and
uniqueness as recorded in `IsCanonicalDecomposition`. -/
theorem canonical_decomposition : CanonicalDecompositionStatement := by
  exact ParabolicRectifiability.IntegralCanonical.canonicalDecomposition_of_providers ParabolicRectifiability.Characterization.intrinsic_sufficiency_skeleton ParabolicRectifiability.Characterization.b2_graph_source_square_finite ParabolicRectifiability.Foundations.squareEnergy_lt_top_iff_of_endpoints_proof

/-- For `2 ≤ k ≤ n`, an ordinary vertical graph of Lipschitz bound `L` and a horizontal
graph of slope `ε ≤ 1` with `L ε ≤ 1/2` have `H_P^k`-null intersection. Spatial projection
onto the vertical base is injective there, with inverse bound
`d_P(p,q) ≤ 2(1+L) |P_W p - P_W q|`; at `k = 2` the intersection has at most one point. -/
theorem type_separation : TypeSeparationStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_horizontalGraph_inter_ordinaryVerticalGraph_separation

/-- Boundary cases of the canonical sets: `E_V = ∅` at
`k = 1`, `E_H = ∅` at `k = n + 1`, and for intrinsic sources the ambient decomposition
is `(0, μ, 0)`. For `μ = 0` the overlap is source-null, although when both types are
available its literal finite-energy overlap is the whole space. -/
theorem canonical_guards : CanonicalGuardsStatement := by
  exact ParabolicRectifiability.IntegralCanonical.canonicalGuards_of_providers (fun n hn μ _ _ T hT => ParabolicRectifiability.Foundations.ambient_betaSq_squareEnergy_eq_zero_proof n hn μ T hT)

end ParabolicRectifiability.IntegralCanonical
