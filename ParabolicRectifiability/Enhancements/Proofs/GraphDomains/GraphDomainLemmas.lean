import ParabolicRectifiability.Foundations.GraphDomainCover
import ParabolicRectifiability.Metric.BaseVolume
import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.HalfDensityBalls
import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.Assignment
import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.HorizontalPatches
import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.VerticalPatches
import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.GraphGeometry

/-! # Intermediate statements for the graph-domain cover

This module states, and proves under the names below, the intermediate lemmas used to build
graph domains for a carrier covered by graphs (see `Enhancements.exists_fixedCarrier_graphDomainCover`).
They are assembled in `exists_fixedCarrier_graphDomainCover_of_providers`.

* `exists_disjoint_halfDensity_balls` takes the canonical fivefold selection
  `FivefoldSelectionStatement` as a hypothesis (implication form); its base type is in `Type`
  (the universe of that statement).
* The replacement of a horizontal graph by a graph over a closed domain is the hypothesis
  `HorizontalClosedEnvelopeStatement` of the assembly, not a lemma here.
* The per-graph lemmas only record that images are Borel for closed-domain horizontal graphs
  and for full vertical graphs; the first-graph assignment needs only Borel images.

| Lemma | Role |
|---|---|
| `exists_disjoint_halfDensity_balls` | density points and the selection of disjoint half-density balls |
| `horizontalGraph_geometry` | per-graph facts, horizontal |
| `verticalGraph_geometry` | per-graph facts, vertical |
| `horizontal_assignment`, `vertical_assignment` | disjoint Borel traces and the trace estimate |
| `horizontal_patches`, `vertical_patches` | the patch family and both charges |

**Conventions.**
* Every lemma takes its graphs, traces and selected balls as **hypotheses** (parametrization
  data). None assumes a conclusion of the main statement or of the typed hubs of the assembly,
  and none introduces a carrier packing, content or graphicality assumption beyond its stated
  inputs; the graph covers of the carrier are inputs of the main statement itself, and the
  charge bounds are proved outputs.
* Hausdorff measure is the unnormalized diameter-power `hausdorffP n k`. Base volumes are
  intrinsic: inner-product `volume` on the horizontal base `U` and `intrinsicParabolicVolume` on
  the vertical base `W × ℝ`, never ambient volume.
* The constants are explicit functions of `k`: the ball constant `v_B` (`omega k`
  horizontally, `2 * omega (k - 2)` vertically), which is also the lower comparison
  constant, and the upper comparison constant `2 ^ k` times
  `horizontalHausdorffConstant k` or `verticalHausdorffConstant (k - 2)`.
* Index sets of countable families are subsets of `ℕ` (finite and empty families allowed).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.GraphDomainTree

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization (FivefoldSelectionStatement)

/-! ## Density points and the fivefold selection on an abstract base -/

/-- **Disjoint half-density balls whose fivefold enlargements cover.**

Hypothesis (implication form): `hfive : FivefoldSelectionStatement`, the canonical `5r`
selection. Setting: a proper metric space `B` (in `Type`) with a Borel measure `μ` obeying the
exact ball law `μ(B(p,r)) = v r^k` for all `p` and `r > 0`, with `0 < v < ∞` (both graph bases
satisfy this: `omega k` horizontally, `2 omega (k-2)` vertically). Conclusion: for a bounded
Borel `E ⊆ B` and `δ > 0` there is a countable family of pairwise disjoint open balls
`B(p_l, r_l)` with centres `p_l ∈ E`, `0 < 5 r_l ≤ δ`, the half-density inequality
`v r_l^k ≤ 2 μ(E ∩ B(p_l, r_l))`, and `μ(E \ ⋃_l B(p_l, 5 r_l)) = 0`. Empty families are
allowed.

Proof route (no second covering argument). (i) Density: the ball law makes `μ` doubling and
locally finite, and gives null spheres (`μ(closedBall p r) = v r^k` by continuity from above,
so `μ(sphere p r) = 0`); the Lebesgue density theorem for doubling measures on the proper,
hence second-countable, space `B` (mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`,
with closed and open balls interchanged through the null spheres) gives a Borel `E' ⊆ E` with
`μ(E \ E') = 0` such that at each `p ∈ E'` the ratio `μ(E ∩ B(p,r)) / v r^k → 1`, hence
`v r^k ≤ 2 μ(E ∩ B(p,r))` for all `0 < r ≤ r_p` (no uniform radius). (ii) Selection: apply
`hfive` to `X = B` (separable, being proper) and the family of all balls `B(p, r)` with
`p ∈ E'`, `0 < r ≤ min (δ/5) r_p` and half density (radii positive and bounded by `δ/5`; every
`p ∈ E'` is a centre); the selected subfamily is countable, pairwise disjoint, and its fivefold
dilates cover every centre, hence `E'`. (iii) Reindex the countable selection by a subset of `ℕ`
(`Set.Countable.exists_injective_nat`-style), and conclude
`μ(E \ ⋃ B(p_l, 5 r_l)) ≤ μ(E \ E') = 0`. -/
theorem exists_disjoint_halfDensity_balls (hfive : FivefoldSelectionStatement)
    {B : Type} [MetricSpace B] [ProperSpace B] [MeasurableSpace B] [BorelSpace B]
    (μ : Measure B) (k : ℕ) (v : ℝ≥0∞) (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (hball : ∀ (p : B) (r : ℝ), 0 < r → μ (Metric.ball p r) = v * ENNReal.ofReal r ^ k)
    (E : Set B) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (L : Set ℕ) (p : L → B) (r : L → ℝ),
      (∀ l, p l ∈ E) ∧ (∀ l, 0 < r l ∧ 5 * r l ≤ δ) ∧
      (Pairwise fun l l' => Disjoint (Metric.ball (p l) (r l)) (Metric.ball (p l') (r l'))) ∧
      (∀ l, v * ENNReal.ofReal (r l) ^ k ≤ 2 * μ (E ∩ Metric.ball (p l) (r l))) ∧
      μ (E \ ⋃ l, Metric.ball (p l) (5 * r l)) = 0 := by
  exact exists_disjoint_halfDensity_balls_proof hfive μ k v hv0 hvt hball E hE hEb δ hδ

/-! ## Per-graph geometry -/

/-- **Geometry of a closed-domain horizontal graph of slope at most one.**

For `G` with closed domain `D ⊆ U` and slope bound `ε ≤ 1`, with graph map
`Φ(u) = (a + u + g u, h u)` on `D`:
1. `Φ⁻¹(F)` (`horizontalPreimage`, taken inside `D`) is Borel in `U` for every Borel `F`;
2. `Φ(A ∩ D)` is Borel in `X` for every Borel `A ⊆ U`;
3. `|u - w| ≤ d_P(Φ u, Φ w) ≤ √2 |u - w|` on `D`;
4. `λ_U(A) ≤ omega k · H_P^k(Φ(A))` for every `A ⊆ D` (lower comparison, with `v_B = omega k`);
5. `H_P^k(Φ(A)) ≤ 2^k · horizontalHausdorffConstant k · λ_U(A)` for every `A ⊆ D` (upper
   comparison; `(√2)^k ≤ 2^k`).

The closed domain is supplied by the closed-envelope hypothesis and the Borel image of the
whole graph by the Borel-image hypothesis of the assembly; neither is restated here.

Proof route: (3) orthogonality `|Δx|² = |Δu|² + |Δg|²`, `|Δg| ≤ ε|Δu| ≤ |Δu|` and
`√|Δh| ≤ |Δu|`; (1)-(2) by (3), `Φ` is a closed embedding of the closed, hence complete, set
`D` into `X` (`Isometry`-type lower bound, `IsClosedEmbedding`), so it is a measurable embedding
(`Topology.IsClosedEmbedding.measurableEmbedding`), and `D` is a closed (Borel) subset of `U`;
(4)-(5) `horizontal_base_hausdorff_comparison` (with `finrank U = k`),
`hausdorffMeasure_subtype_image_le` for `Φ` (constant `√2`) and for the `1`-Lipschitz
projection, and `hausdorffP_eq`. No measurability of `A` is needed in (4)-(5). -/
theorem horizontalGraph_geometry {n k : ℕ} {ε : ℝ} (hε : ε ≤ 1) (G : HorizontalGraph n k ε)
    (hD : IsClosed G.domain) :
    (∀ F : Set (Space n), MeasurableSet F → MeasurableSet (horizontalPreimage G F)) ∧
    (∀ A : Set G.direction, MeasurableSet A →
      MeasurableSet (horizontalGraphMap G '' {u : G.domain | (u : G.direction) ∈ A})) ∧
    (∀ u w : G.domain,
      dist (u : G.direction) (w : G.direction) ≤
          dist (horizontalGraphMap G u) (horizontalGraphMap G w) ∧
        dist (horizontalGraphMap G u) (horizontalGraphMap G w) ≤
          Real.sqrt 2 * dist (u : G.direction) (w : G.direction)) ∧
    (∀ A : Set G.domain,
      volume (Subtype.val '' A : Set G.direction) ≤
        omega k * hausdorffP n k (horizontalGraphMap G '' A)) ∧
    (∀ A : Set G.domain,
      hausdorffP n k (horizontalGraphMap G '' A) ≤
        2 ^ k * horizontalHausdorffConstant k * volume (Subtype.val '' A : Set G.direction)) := by
  exact horizontalGraph_geometry_proof hε G hD

/-- **Geometry of a full general regular vertical graph of norm at most one.**

For `G` with base `W × ℝ` (max parabolic metric, `dim W = k - 2`) and regular norm bound
`ε ≤ 1`, with map `Φ(u,t) = (a + u + G(u,t), t)`:
1. `Φ⁻¹(F)` is Borel for Borel `F`;
2. `Φ(A)` is Borel for Borel `A`;
3. `d(p,q) ≤ d_P(Φ p, Φ q) ≤ √2 d(p,q)`;
4. `intrinsicParabolicVolume W A ≤ 2 omega (k-2) · H_P^k(Φ(A))` for every `A`;
5. `H_P^k(Φ(A)) ≤ 2^k · verticalHausdorffConstant (k-2) · intrinsicParabolicVolume W A`.

The Borel image of the whole graph is a hypothesis of the assembly and is not restated here.

Proof route: the regular norm bound gives `Lip_P G ≤ L ≤ ε ≤ 1` (the BMO part is
nonnegative); (3) orthogonality and unchanged time; (1)-(2) `Φ` is continuous, and by (3) a
closed embedding of the complete base, hence a measurable embedding; (4)-(5)
`vertical_base_hausdorff_comparison` (with `finrank W + 2 = k`) and the Lipschitz image bounds.
Only the Lipschitz part of the regularity is used. Rank zero (`k = 2`) is included. -/
theorem verticalGraph_geometry {n k : ℕ} {ε : ℝ} (hε : ε ≤ 1)
    (G : GeneralRegularVerticalGraph n k ε) :
    (∀ F : Set (Space n), MeasurableSet F → MeasurableSet (G.map ⁻¹' F)) ∧
    (∀ A : Set (SubspaceSpace G.direction), MeasurableSet A → MeasurableSet (G.map '' A)) ∧
    (∀ p q : SubspaceSpace G.direction,
      dist p q ≤ dist (G.map p) (G.map q) ∧ dist (G.map p) (G.map q) ≤ Real.sqrt 2 * dist p q) ∧
    (∀ A : Set (SubspaceSpace G.direction),
      intrinsicParabolicVolume G.direction A ≤ 2 * omega (k - 2) * hausdorffP n k (G.map '' A)) ∧
    (∀ A : Set (SubspaceSpace G.direction),
      hausdorffP n k (G.map '' A) ≤
        2 ^ k * verticalHausdorffConstant (k - 2) * intrinsicParabolicVolume G.direction A) := by
  exact verticalGraph_geometry_proof hε G

/-! ## First-graph assignment and the trace estimate -/

/-- **Horizontal first-graph assignment and trace summation.**

Hypotheses (parametrization data): a Borel bounded carrier `K`; a countable family of
horizontal graphs with Borel images, Borel trace preimages, `1`-Lipschitz inverse projection,
and the lower comparison `λ_U(A) ≤ c H_P^k(Φ(A))`, covering `K` modulo `H_P^k`.
Conclusion: disjoint Borel traces `F_j ⊆ K ∩ Γ_j` covering `K` modulo `H_P^k`, bounded
trace preimages, and for every Borel `U`
`Σ_j λ_{U_j}(Φ_j⁻¹(F_j) ∩ Φ_j⁻¹(U)) ≤ c H_P^k(K ∩ U)`.

Proof route: `F_j = (K ∩ Γ_j) \ ⋃_{i < j} Γ_i` (order of `ℕ`; Borel because the images are);
`⋃ F_j = K ∩ ⋃ Γ_j`; `Φ_j⁻¹(F_j) ∩ Φ_j⁻¹(U) = Subtype.val '' Φ_j⁻¹(F_j ∩ U)` and its image is
`F_j ∩ U`; the lower comparison and countable additivity of `H_P^k` on the disjoint Borel sets
`F_j ∩ U`. Boundedness from `F_j ⊆ K` and the inverse projection. Any `c ∈ [0, ∞]`. -/
theorem horizontal_assignment {n k : ℕ} {ε : ℝ} (c : ℝ≥0∞) (K : Set (Space n))
    (hKm : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (J : Set ℕ) (G : J → HorizontalGraph n k ε)
    (himage : ∀ j, MeasurableSet (G j).image)
    (hpre : ∀ j (F : Set (Space n)), MeasurableSet F → MeasurableSet (horizontalPreimage (G j) F))
    (hproj : ∀ j (u w : (G j).domain), dist (u : (G j).direction) (w : (G j).direction) ≤
      dist (horizontalGraphMap (G j) u) (horizontalGraphMap (G j) w))
    (hlow : ∀ j (A : Set (G j).domain), volume (Subtype.val '' A : Set (G j).direction) ≤
      c * hausdorffP n k (horizontalGraphMap (G j) '' A))
    (hcov : hausdorffP n k (K \ ⋃ j, (G j).image) = 0) :
    ∃ F : J → Set (Space n),
      (∀ j, MeasurableSet (F j)) ∧ (∀ j, F j ⊆ K ∩ (G j).image) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      hausdorffP n k (K \ ⋃ j, F j) = 0 ∧
      (∀ j, Bornology.IsBounded (horizontalPreimage (G j) (F j))) ∧
      ∀ U : Set (Space n), MeasurableSet U →
        ∑' j, volume (horizontalPreimage (G j) (F j) ∩ horizontalPreimage (G j) U) ≤
          c * hausdorffP n k (K ∩ U) := by
  exact horizontal_assignment_proof c K hKm hKb J G himage hpre hproj hlow hcov

/-- **Vertical first-graph assignment and trace summation**, for full vertical graphs on
their whole bases with intrinsic product volume. Same statement and proof route as
`horizontal_assignment`, with `Φ_j⁻¹` the ordinary preimage under the full graph map. -/
theorem vertical_assignment {n k : ℕ} {ε : ℝ} (c : ℝ≥0∞) (K : Set (Space n))
    (hKm : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (J : Set ℕ) (G : J → GeneralRegularVerticalGraph n k ε)
    (himage : ∀ j, MeasurableSet (G j).image)
    (hpre : ∀ j (F : Set (Space n)), MeasurableSet F → MeasurableSet ((G j).map ⁻¹' F))
    (hproj : ∀ j (p q : SubspaceSpace (G j).direction), dist p q ≤ dist ((G j).map p) ((G j).map q))
    (hlow : ∀ j (A : Set (SubspaceSpace (G j).direction)),
      intrinsicParabolicVolume (G j).direction A ≤ c * hausdorffP n k ((G j).map '' A))
    (hcov : hausdorffP n k (K \ ⋃ j, (G j).image) = 0) :
    ∃ F : J → Set (Space n),
      (∀ j, MeasurableSet (F j)) ∧ (∀ j, F j ⊆ K ∩ (G j).image) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      hausdorffP n k (K \ ⋃ j, F j) = 0 ∧
      (∀ j, Bornology.IsBounded ((G j).map ⁻¹' F j)) ∧
      ∀ U : Set (Space n), MeasurableSet U →
        ∑' j, intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j ∩ (G j).map ⁻¹' U) ≤
          c * hausdorffP n k (K ∩ U) := by
  exact vertical_assignment_proof c K hKm hKb J G himage hpre hproj hlow hcov

/-! ## The patch families and their charges -/

/-- **Horizontal patch family with global and local charges.**

Hypotheses (parametrization data): disjoint Borel traces `F_j ⊆ K ∩ Γ_j` covering `K` modulo
`H_P^k` on graphs of slope `≤ min ε 1` with Borel trace preimages `E_j`; Borel images of Borel
base sets; the two-sided distance bound with constant `√2`; the lower comparison with constant
`v` and the upper comparison with constant `cU`; the ball bound `λ(B(p,r)) ≤ v r^k`; and, for
each `j`, selected disjoint balls `B(p_{j,l}, r_{j,l})` with centres in `E_j`, `0 < 5 r ≤ δ`,
half density `v r^k ≤ 2 λ(E_j ∩ B(p,r))` and `λ(E_j \ ⋃_l B(p_{j,l}, 5 r_{j,l})) = 0` (the
output of `exists_disjoint_halfDensity_balls`).

Conclusion: horizontal domain data whose trace volumes equal the given sums, and, with
`c_P = 2 · 5^k · (1 + v + cU v)`, `Σ_α c_α ≤ c_P H_P^k(K)` and
`Σ_{α ∈ I(q,R)} c_α ≤ c_P H_P^k(K ∩ P(q,2R))` for all `q`, `R > 0`. The construction (not
exposed by the type) uses the given graphs and traces, patches `α = (j,l)` with centre
`p_{j,l}`, radius `ρ_α = 5 r_{j,l} ≤ δ` and patch `Φ_j(E_j ∩ B(p, ρ_α))`.

Proof route: first a shared disjoint-charge summation lemma: disjoint
Borel charges `S_α ⊆ A` with `c_α ≤ c' H_P^k(S_α)` give `Σ_{α ∈ I} c_α ≤ c' H_P^k(A)`. Then the
charges `S_α = Φ_j(E_j ∩ B(p,r)) ⊆ F_j` are Borel and pairwise disjoint (disjoint balls and
injective `Φ_j` within `j`; disjoint traces across `j`); half density and lower comparison give
`ρ_α^k ≤ 2·5^k H_P^k(S_α)`; the ball bound and upper comparison give
`λ(B_α) ≤ v ρ_α^k` and `H_P^k(Q_α) ≤ cU v ρ_α^k`. For `α ∈ I(q,R)`,
`S_α ⊆ P(z_α, √2 ρ_α/5) ⊆ P(q,2R)`. Coverage: the uncovered part of
`K` lies in `K \ ⋃ F_j` and the images `Φ_j(E_j \ ⋃_l B(p_{j,l}, 5 r_{j,l}))`, null by the upper
comparison. Patch indices encode `(j,l)` by `Nat.pair`; the `tsum` reindexing over
`Σ j, L j` is the main bookkeeping. -/
theorem horizontal_patches {n k : ℕ} {ε δ : ℝ} (v cU : ℝ≥0∞) (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (K : Set (Space n)) (J : Set ℕ) (G : J → HorizontalGraph n k (min ε 1))
    (F : J → Set (Space n)) (hFm : ∀ j, MeasurableSet (F j))
    (hFsub : ∀ j, F j ⊆ K ∩ (G j).image) (hFdisj : Pairwise fun i j => Disjoint (F i) (F j))
    (hFcov : hausdorffP n k (K \ ⋃ j, F j) = 0)
    (hEm : ∀ j, MeasurableSet (horizontalPreimage (G j) (F j)))
    (hpatchm : ∀ j (A : Set (G j).direction), MeasurableSet A →
      MeasurableSet (horizontalGraphMap (G j) '' {u : (G j).domain | (u : (G j).direction) ∈ A}))
    (hlip : ∀ j (u w : (G j).domain),
      dist (u : (G j).direction) (w : (G j).direction) ≤
          dist (horizontalGraphMap (G j) u) (horizontalGraphMap (G j) w) ∧
        dist (horizontalGraphMap (G j) u) (horizontalGraphMap (G j) w) ≤
          Real.sqrt 2 * dist (u : (G j).direction) (w : (G j).direction))
    (hlow : ∀ j (A : Set (G j).domain), volume (Subtype.val '' A : Set (G j).direction) ≤
      v * hausdorffP n k (horizontalGraphMap (G j) '' A))
    (hup : ∀ j (A : Set (G j).domain), hausdorffP n k (horizontalGraphMap (G j) '' A) ≤
      cU * volume (Subtype.val '' A : Set (G j).direction))
    (hball : ∀ j (p : (G j).direction) (r : ℝ), 0 < r →
      volume (Metric.ball p r) ≤ v * ENNReal.ofReal r ^ k)
    (L : J → Set ℕ) (p : ∀ j, L j → (G j).direction) (r : ∀ j, L j → ℝ)
    (hp : ∀ j l, p j l ∈ horizontalPreimage (G j) (F j))
    (hr : ∀ j l, 0 < r j l ∧ 5 * r j l ≤ δ)
    (hdisj : ∀ j, Pairwise fun l l' =>
      Disjoint (Metric.ball (p j l) (r j l)) (Metric.ball (p j l') (r j l')))
    (hhalf : ∀ j l, v * ENNReal.ofReal (r j l) ^ k ≤
      2 * volume (horizontalPreimage (G j) (F j) ∩ Metric.ball (p j l) (r j l)))
    (hcov5 : ∀ j, volume (horizontalPreimage (G j) (F j) \
      ⋃ l, Metric.ball (p j l) (5 * r j l)) = 0) :
    ∃ D : HorizontalDomainData n k ε δ K,
      (∀ U : Set (Space n), D.traceVolume U =
        ∑' j, volume (horizontalPreimage (G j) (F j) ∩ horizontalPreimage (G j) U)) ∧
      D.totalCharge ≤ 2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k K ∧
      ∀ (q : Space n) (R : ℝ), 0 < R →
        D.localCharge q R ≤
          2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (K ∩ Metric.ball q (2 * R)) := by
  exact horizontal_patches_proof v cU hv0 hvt K J G F hFm hFsub hFdisj hFcov hEm hpatchm hlip hlow hup hball L p r hp hr hdisj hhalf hcov5

/-- **Vertical patch family with global and local charges.**

Same hypotheses and conclusion as `horizontal_patches`, for full general regular vertical
graphs with intrinsic product volume on `W × ℝ`. The patch `Q_α = Φ_j(B_α)` is the image of the
entire base ball; it may leave the carrier, but its charge `S_α = Φ_j(E_j ∩ B(p,r)) ⊆ F_j` stays
in it. The upper bound `H_P^k(Φ_j(B_α)) ≤ cU λ(B_α) ≤ cU v ρ_α^k` uses the whole ball. The
construction is as for `horizontal_patches`. -/
theorem vertical_patches {n k : ℕ} {ε δ : ℝ} (v cU : ℝ≥0∞) (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (K : Set (Space n)) (J : Set ℕ) (G : J → GeneralRegularVerticalGraph n k (min ε 1))
    (F : J → Set (Space n)) (hFm : ∀ j, MeasurableSet (F j))
    (hFsub : ∀ j, F j ⊆ K ∩ (G j).image) (hFdisj : Pairwise fun i j => Disjoint (F i) (F j))
    (hFcov : hausdorffP n k (K \ ⋃ j, F j) = 0)
    (hEm : ∀ j, MeasurableSet ((G j).map ⁻¹' F j))
    (hpatchm : ∀ j (A : Set (SubspaceSpace (G j).direction)), MeasurableSet A →
      MeasurableSet ((G j).map '' A))
    (hlip : ∀ j (p q : SubspaceSpace (G j).direction),
      dist p q ≤ dist ((G j).map p) ((G j).map q) ∧
        dist ((G j).map p) ((G j).map q) ≤ Real.sqrt 2 * dist p q)
    (hlow : ∀ j (A : Set (SubspaceSpace (G j).direction)),
      intrinsicParabolicVolume (G j).direction A ≤ v * hausdorffP n k ((G j).map '' A))
    (hup : ∀ j (A : Set (SubspaceSpace (G j).direction)),
      hausdorffP n k ((G j).map '' A) ≤ cU * intrinsicParabolicVolume (G j).direction A)
    (hball : ∀ j (p : SubspaceSpace (G j).direction) (r : ℝ), 0 < r →
      intrinsicParabolicVolume (G j).direction (Metric.ball p r) ≤ v * ENNReal.ofReal r ^ k)
    (L : J → Set ℕ) (p : ∀ j, L j → SubspaceSpace (G j).direction) (r : ∀ j, L j → ℝ)
    (hp : ∀ j l, p j l ∈ (G j).map ⁻¹' F j)
    (hr : ∀ j l, 0 < r j l ∧ 5 * r j l ≤ δ)
    (hdisj : ∀ j, Pairwise fun l l' =>
      Disjoint (Metric.ball (p j l) (r j l)) (Metric.ball (p j l') (r j l')))
    (hhalf : ∀ j l, v * ENNReal.ofReal (r j l) ^ k ≤
      2 * intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j ∩ Metric.ball (p j l) (r j l)))
    (hcov5 : ∀ j, intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j \
      ⋃ l, Metric.ball (p j l) (5 * r j l)) = 0) :
    ∃ D : VerticalDomainData n k ε δ K,
      (∀ U : Set (Space n), D.traceVolume U =
        ∑' j, intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j ∩ (G j).map ⁻¹' U)) ∧
      D.totalCharge ≤ 2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k K ∧
      ∀ (q : Space n) (R : ℝ), 0 < R →
        D.localCharge q R ≤
          2 * 5 ^ k * (1 + v + cU * v) * hausdorffP n k (K ∩ Metric.ball q (2 * R)) := by
  exact vertical_patches_proof v cU hv0 hvt K J G F hFm hFsub hFdisj hFcov hEm hpatchm hlip hlow hup hball L p r hp hr hdisj hhalf hcov5

end ParabolicRectifiability.Enhancements.GraphDomainTree
