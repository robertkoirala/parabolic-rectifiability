import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.Statements
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.HorizontalClosedExtension
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.GraphImageBorel
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.GraphHausdorffFinite

/-! # Closed horizontal envelopes, Borel images, local Hausdorff finiteness

The five intermediate lemmas behind `fgenv_graph_borel_envelope` (the statement of
`ParabolicRectifiability.Characterization.graph_borel_envelope`). None mentions a measure or a
smallness of `ε`. The dimension `k`, the tolerance `ε` and the graph are arbitrary (no guard
`1 ≤ k ≤ n + 2`, no sign condition on `ε`: for `ε < 0` a horizontal domain has at most one
point, and no vertical graph exists since `L + B ≤ ε` with `L, B ≥ 0`). Each statement is
proved by the corresponding `…_proof` lemma.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

/-- **Closed envelope of a horizontal subset graph.**

Every horizontal graph `G` of slope at most `ε` over an arbitrary domain
`D ⊆ U` lies in a horizontal graph `G'` of the same slope bound whose domain is closed in `U`.

Construction: keep `direction`, `rank_eq` and `offset`; take `G'.domain = closure G.domain` (closure in
the subspace `U`). The slope bound gives `‖g u - g v‖ ≤ ε⁺ ‖u - v‖` and
`|h u - h v| ≤ (ε⁺ ‖u - v‖)²` on `D`, so `g` and `h` are uniformly continuous on `D` with values
in complete spaces; extend them to `closure D` (Mathlib `IsDenseInducing.extend` /
`IsUniformInducing` extension along the dense inclusion `D → closure D`, with `extend_eq` on
`D`). The inequality `max ‖g' u - g' v‖ (√|h' u - h' v|) ≤ ε ‖u - v‖` is a closed condition in
`(u,v)` and holds on the dense set `D × D`, hence on `closure D × closure D`
(`isClosed_le` with `Dense.induction`/`closure_minimal`). Image inclusion: the point of `G`
over `u ∈ D` is the point of `G'` over `⟨u, subset_closure u.2⟩`, by `extend_eq`.

The statement is the named `HorizontalClosedEnvelopeStatement`, which is also used by the
compact-cover argument.

Scope: the statement supplies a same-bound containing graph with closed domain. Preservation
of direction and offset, literal domain-closure equality (`G'.domain = closure G.domain`),
uniqueness, and image-closure equality belong to the construction above but are not exposed
by this type. Closure enlargement is not Hausdorff-null in
general: the flat graph over `ℚ ∩ [0,1]` has zero length, while its closure contains a unit
segment. Do not extend the time map `h` to the whole direction: a quadratic modulus on a line
forces constancy, whereas a two-point trace can have different heights. For `ε < 0` the domain
has at most one point and `G' = G` suffices; passing the original slope inequality to limits
preserves `ε` itself, not merely `ε⁺`. -/
theorem fgenv_horizontal_closed_extension : HorizontalClosedEnvelopeStatement := by
  exact fgenv_horizontal_closed_extension_proof

/-- **A closed-domain horizontal graph has Borel image.** If the domain of a horizontal graph
is closed in its direction `U`, its image is a Borel subset of `X`.

Proof: `U` is finite dimensional, hence proper and sigma-compact, so the closed domain `D` is
sigma-compact (`IsClosed`, `isSigmaCompact_univ` restricted through `Subtype.val`). The graph
map `u ↦ (a + u + g u, h u)` is continuous on `D` (Lipschitz normal part, `|h u - h v| ≤
ε² ‖u - v‖²`), so the image is sigma-compact (`IsSigmaCompact.image`), i.e. a countable union
of compact, hence closed, sets of the Hausdorff space `X`: `MeasurableSet.iUnion` of
`IsCompact.isClosed.measurableSet`. (Alternatively: the image is closed, by a projection
argument.) -/
theorem fgenv_horizontal_image_measurableSet_of_isClosed (n k : ℕ) (ε : ℝ)
    (G : HorizontalGraph n k ε) (hD : IsClosed G.domain) : MeasurableSet G.image := by
  exact fgenv_horizontal_image_measurableSet_of_isClosed_proof n k ε G hD

/-- **Local Hausdorff finiteness of a horizontal graph.** For every horizontal graph `G` of
slope at most `ε` (arbitrary domain), every centre `q` and radius `R`,
`H_P^k(G.image ∩ P(q,R)) < ∞`.

Proof: write `F u = (a + u + g u, h u)` on `D ⊆ U`. (i) Projection: if `F u ∈ P(q,R)` then
`‖u - π_U(q.1 - a)‖ ≤ ‖a + u + g u - q.1‖ < R` (orthogonality of `u - π_U(q.1-a)` and the
`U^⊥` parts), so the base points lie in a bounded set `E ⊆ U` and
`G.image ∩ P(q,R) ⊆ F '' (D ∩ E)`. (ii) `F` is Lipschitz from the Euclidean metric of `U` to
the parabolic metric, with constant `1 + |ε|` (or the sharp `√(1+ε²)`). (iii)
`hausdorffMeasure_subtype_image_le` gives
`H_P^k(F '' (D ∩ E)) ≤ C^k H^k_U(D ∩ E)`, with `k = finrank U` (`rank_eq`). (iv)
`horizontal_base_hausdorff_comparison` bounds `H^k_U` by
`horizontalHausdorffConstant k * volume`, and a bounded set of the finite-dimensional `U` has
finite volume (`measure_closedBall_lt_top`).

Endpoints: `R ≤ 0` gives an empty intersection. Horizontal `k = 0` gives at most one point,
whose `H_P^0` mass can be **one** (not zero), still finite. Domain measurability is not needed:
the image and base comparisons hold for arbitrary sets (an outer-measure assertion). -/
theorem fgenv_horizontal_hausdorffP_inter_ball_lt_top (n k : ℕ) (ε : ℝ)
    (G : HorizontalGraph n k ε) (q : Space n) (R : ℝ) :
    hausdorffP n k (G.image ∩ Metric.ball q R) < ⊤ := by
  exact fgenv_horizontal_hausdorffP_inter_ball_lt_top_proof n k ε G q R

/-- **A full general regular vertical graph has Borel image** (a general regular graph is in
particular an ordinary full vertical graph with Lipschitz bound `L ≤ ε`).

The image of every `GeneralRegularVerticalGraph n k ε` is Borel.

Proof: the base `SubspaceSpace W = W × Time` is proper and sigma-compact
(`instProperSpaceTime`, finite-dimensional `W`); the graph map `(u,t) ↦ (a + u + G(u,t), t)` is
continuous (`G` is Lipschitz by `regular`); `isSigmaCompact_range` and a countable union of
compact sets, as in `fgenv_horizontal_image_measurableSet_of_isClosed`. -/
theorem fgenv_vertical_image_measurableSet (n k : ℕ) (ε : ℝ)
    (G : GeneralRegularVerticalGraph n k ε) : MeasurableSet G.image := by
  exact fgenv_vertical_image_measurableSet_proof n k ε G

/-- **Local Hausdorff finiteness of a full vertical graph.** For every
`GeneralRegularVerticalGraph n k ε`, centre `q` and radius `R`,
`H_P^k(G.image ∩ P(q,R)) < ∞`.

Proof: `k = finrank W + 2` (`rank_eq`). (i) Projection: a graph point `Φ(u,t)` in `P(q,R)`
has `‖u - π_W(q.1 - a)‖ < R` and `√|t - q.2| < R`, so the base points lie in a bounded set
`E ⊆ W × Time`. (ii) `Φ` is Lipschitz from the parabolic metric of `W × Time` to that of `X`,
with constant `1 + L` (or the sharp `√(1+L²)`), `L` from `regular`. (iii)
`LipschitzWith.hausdorffMeasure_image_le` gives `H_P^k(Φ '' E) ≤ C^k H^k(E)`. (iv)
`vertical_base_hausdorff_comparison` bounds `H^k(E)` by
`verticalHausdorffConstant * intrinsicParabolicVolume W E`, finite on bounded sets
(`intrinsicParabolicVolume_ball`). Rank zero (`k = 2`) and full rank (`k = n + 2`) need no
separate argument. -/
theorem fgenv_vertical_hausdorffP_inter_ball_lt_top (n k : ℕ) (ε : ℝ)
    (G : GeneralRegularVerticalGraph n k ε) (q : Space n) (R : ℝ) :
    hausdorffP n k (G.image ∩ Metric.ball q R) < ⊤ := by
  exact fgenv_vertical_hausdorffP_inter_ball_lt_top_proof n k ε G q R

end ParabolicRectifiability.Foundations
