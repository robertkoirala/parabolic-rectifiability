import ParabolicRectifiability.IntegralCanonical.Statements.Canonical
import ParabolicRectifiability.IntegralCanonical.Proofs.Canonical.DensityBridgeAndTypeSeparationProofs

/-! # The density bridge and the separation of types

The two auxiliary statements used by the canonical decomposition. Their types are exactly
`IntrinsicSourceOfDensityStatement` and `TypeSeparationStatement`; both theorems apply the
proofs `i2_isIntrinsicSource_of_hasPositiveFiniteUpperDensity` and
`i2_horizontalGraph_inter_ordinaryVerticalGraph_separation`. They are used in
`canonicalDecomposition_of_providers`: the density bridge for the density form of the
hypothesis, and the separation of types for the null overlap `μ(E_H ∩ E_V) = 0`.
-/

noncomputable section

namespace ParabolicRectifiability.IntegralCanonical

/-- **Density bridge.** For `n ≥ 1`, `1 ≤ k ≤ n+2` and a locally Radon `μ` with
`0 < Θ^{k,*}(μ,·) < ∞` `μ`-almost everywhere, `μ` is in the intrinsic source class:
`μ ≪ H_P^k` (finite upper density exhausts the source by the Borel classes `F_{a,j,N}`;
recentred cheap Hausdorff covers) and a Borel sigma-finite `H_P^k` carrier (positive upper
density and fivefold selection bound `H_P^k(P(0,N) ∩ {Θ^{k,*} > 1/j})`). No finite-square
hypothesis is used. This is the density form of the hypothesis in
`canonicalDecomposition_of_providers`. -/
theorem isIntrinsicSource_of_hasPositiveFiniteUpperDensity :
    IntrinsicSourceOfDensityStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_isIntrinsicSource_of_hasPositiveFiniteUpperDensity

/-- **Separation of types.** For `2 ≤ k ≤ n`, an ordinary full vertical graph over `W × ℝ` with parabolic
Lipschitz constant at most `L`, and a horizontal graph of slope at most `ε` with `ε ≤ 1` and
`L ε ≤ 1/2`: the spatial projection `P_W` is injective on the intersection, its inverse is
`2(1+L)`-Lipschitz into `d_P`, the intersection is `H_P^k`-null, and at `k = 2` it has at
most one point.

The proof splits on the sign of `ε`; the statement allows `ε < 0` and is not restricted to
`ε ≥ 0`.
* `ε < 0`: the `small_slope` field bounds a nonnegative maximum by `ε ‖u - v‖ ≤ 0`, so
  `u = v`. The domain, hence `H.image` and the intersection, is a subsingleton, and all four
  conclusions are immediate (`H_P^k` of a subsingleton vanishes since `k ≥ 2 > 0`).
* `ε ≥ 0`: the `lipschitz` field of the vertical graph gives `L ≥ 0`. For two intersection
  points with spatial-projection distance `a`, horizontal displacement `h`, vertical
  displacement `b` and parabolic distance `d`, the graph definitions give `h ≤ ε d` and
  `b ≤ L max(a, h) ≤ L a + L ε d`; the offsets cancel, and no compatibility between the
  two spatial orientations is needed. Hence `(1 - Lε) d ≤ (1+L) a` and `d ≤ 2(1+L) a`.
  Nullity: the inverse is defined on an arbitrary subset of the `(k-2)`-dimensional space
  `W`; covering its bounded pieces by `δ`-cubes gives `H_P^k` cost `O(δ^2) → 0`, with no
  measurability assumption on the intersection. At `k = 2`, injectivity into the rank-zero
  `W` gives a subsingleton.

Used in `canonicalDecomposition_of_providers` for the null overlap, only in the canonical
specialization (one vertical cover at norm `1`, so `L = 1`, and one horizontal cover at
slope `1/2`). -/
theorem horizontalGraph_inter_ordinaryVerticalGraph_separation :
    TypeSeparationStatement := by
  exact ParabolicRectifiability.IntegralCanonical.i2_horizontalGraph_inter_ordinaryVerticalGraph_separation

end ParabolicRectifiability.IntegralCanonical
