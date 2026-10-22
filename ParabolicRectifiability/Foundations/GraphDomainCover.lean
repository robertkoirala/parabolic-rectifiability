import ParabolicRectifiability.Foundations.Graphs

/-! # Graph-domain covers

Definitions only, for the graph-domain cover.

A cover is parameterized by the two typed carriers `(K_H, K_V)`. A type outside the chosen
collection is represented by the empty carrier: its traces lie in the empty set, so it has
no patches and contributes nothing. An unavailable type has no graphs at all, so its
families are empty, and `HasGraphDomainCover` requires its carrier to be empty.

* Horizontal data use the existing `HorizontalGraph` (subset domain `A ⊂ U`, full base the
  spatial `k`-plane `U` with its Euclidean metric and inner-product volume `volume`).
* Vertical data use `GeneralRegularVerticalGraph` (full base and domain `W × ℝ`, max
  parabolic metric, `intrinsicParabolicVolume`).
* Graph maps have slope or regular norm at most `min ε 1`.
* All trace and patch data are fixed before the testing set `U` and the scale `(q,R)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

variable {n k : ℕ}

/-! ## Graph maps, preimages and patches -/

/-- The graph map `u ↦ (a + u + g(u), h(u))` of a horizontal subset graph, on its actual
domain. Its range is `HorizontalGraph.image`. -/
def horizontalGraphMap {ε : ℝ} (G : HorizontalGraph n k ε) (u : G.domain) : Space n :=
  point (G.offset + (u.val : Spatial n) + (G.normal u : Spatial n)) (G.time u)

/-- `Φ⁻¹(S)` for a horizontal graph, as a subset of the full base `U`. Only points of the
actual domain are used. -/
def horizontalPreimage {ε : ℝ} (G : HorizontalGraph n k ε) (S : Set (Space n)) :
    Set G.direction :=
  {u | ∃ h : u ∈ G.domain, horizontalGraphMap G ⟨u, h⟩ ∈ S}

/-- The horizontal patch `Φ(D ∩ B(p,ρ))`, with trace preimage `D = Φ⁻¹(F)`. A horizontal map is used only on its trace domain. -/
def horizontalPatch {ε : ℝ} (G : HorizontalGraph n k ε) (F : Set (Space n))
    (p : G.direction) (ρ : ℝ) : Set (Space n) :=
  horizontalGraphMap G ''
    {u : G.domain | (u : G.direction) ∈ horizontalPreimage G F ∩ Metric.ball p ρ}

/-- The vertical patch `Φ(B(p,ρ))`, using the whole parabolic base ball. -/
def verticalPatch {ε : ℝ} (G : GeneralRegularVerticalGraph n k ε)
    (p : SubspaceSpace G.direction) (ρ : ℝ) : Set (Space n) :=
  G.map '' Metric.ball p ρ

/-! ## Typed data -/

/-- The horizontal data of a graph-domain cover of the carrier `K`, at tolerance `ε` and
mesh `δ`: countably many graph maps, pairwise
disjoint Borel traces in `K` covering it modulo `H_P^k`, Borel trace preimages in the full
bases, and countably many patches with centres in the traces and radii in `(0, δ]`, whose
Borel images cover `K` modulo `H_P^k`. -/
structure HorizontalDomainData (n k : ℕ) (ε δ : ℝ) (K : Set (Space n)) where
  /-- Indices `j` of the horizontal graph maps. -/
  graphIndex : Set ℕ
  /-- The graph maps `Φ_{H,j}`, of slope at most `min ε 1`. -/
  graph : graphIndex → HorizontalGraph n k (min ε 1)
  /-- The traces `F_{H,j}`. -/
  trace : graphIndex → Set (Space n)
  measurableSet_trace : ∀ j, MeasurableSet (trace j)
  trace_subset : ∀ j, trace j ⊆ K ∩ (graph j).image
  pairwise_disjoint_trace : Pairwise fun i j => Disjoint (trace i) (trace j)
  trace_cover : hausdorffP n k (K \ ⋃ j, trace j) = 0
  /-- The trace preimages `D_{H,j} = Φ_{H,j}⁻¹(F_{H,j})` are Borel in the full bases. -/
  measurableSet_tracePreimage : ∀ j, MeasurableSet (horizontalPreimage (graph j) (trace j))
  /-- Patch indices `α`. -/
  patchIndex : Set ℕ
  /-- The graph `j(α)` assigned to each patch. -/
  patchGraph : patchIndex → graphIndex
  /-- The patch centre `p_α`, a point of the actual domain of its graph. -/
  center : ∀ α, (graph (patchGraph α)).domain
  /-- `p_α ∈ D_{H,j(α)}`. -/
  center_mem_tracePreimage : ∀ α,
    ((center α : (graph (patchGraph α)).direction)) ∈
      horizontalPreimage (graph (patchGraph α)) (trace (patchGraph α))
  /-- `z_α = Φ_{H,j(α)}(p_α) ∈ K_H`. -/
  centerPoint_mem : ∀ α, horizontalGraphMap (graph (patchGraph α)) (center α) ∈ K
  /-- The patch radius `ρ_α`. -/
  radius : patchIndex → ℝ
  radius_pos : ∀ α, 0 < radius α
  radius_le : ∀ α, radius α ≤ δ
  measurableSet_patch : ∀ α, MeasurableSet
    (horizontalPatch (graph (patchGraph α)) (trace (patchGraph α)) (center α) (radius α))
  patch_cover : hausdorffP n k (K \ ⋃ α,
    horizontalPatch (graph (patchGraph α)) (trace (patchGraph α)) (center α) (radius α)) = 0

/-- The vertical data of a graph-domain cover of the carrier `K`, at tolerance `ε` and mesh
`δ`. The vertical graph maps are defined on their
whole base `W × ℝ`, and the patches use whole base balls. -/
structure VerticalDomainData (n k : ℕ) (ε δ : ℝ) (K : Set (Space n)) where
  /-- Indices `j` of the vertical graph maps. -/
  graphIndex : Set ℕ
  /-- The graph maps `Φ_{V,j}`, of general regular norm at most `min ε 1`. -/
  graph : graphIndex → GeneralRegularVerticalGraph n k (min ε 1)
  /-- The traces `F_{V,j}`. -/
  trace : graphIndex → Set (Space n)
  measurableSet_trace : ∀ j, MeasurableSet (trace j)
  trace_subset : ∀ j, trace j ⊆ K ∩ (graph j).image
  pairwise_disjoint_trace : Pairwise fun i j => Disjoint (trace i) (trace j)
  trace_cover : hausdorffP n k (K \ ⋃ j, trace j) = 0
  /-- The trace preimages `D_{V,j} = Φ_{V,j}⁻¹(F_{V,j})` are Borel in the full bases. -/
  measurableSet_tracePreimage : ∀ j, MeasurableSet ((graph j).map ⁻¹' trace j)
  /-- Patch indices `α`. -/
  patchIndex : Set ℕ
  /-- The graph `j(α)` assigned to each patch. -/
  patchGraph : patchIndex → graphIndex
  /-- The patch centre `p_α ∈ W_{j(α)} × ℝ`. -/
  center : ∀ α, SubspaceSpace (graph (patchGraph α)).direction
  /-- `p_α ∈ D_{V,j(α)}`. -/
  center_mem_tracePreimage : ∀ α,
    center α ∈ (graph (patchGraph α)).map ⁻¹' trace (patchGraph α)
  /-- `z_α = Φ_{V,j(α)}(p_α) ∈ K_V`. -/
  centerPoint_mem : ∀ α, (graph (patchGraph α)).map (center α) ∈ K
  /-- The patch radius `ρ_α`. -/
  radius : patchIndex → ℝ
  radius_pos : ∀ α, 0 < radius α
  radius_le : ∀ α, radius α ≤ δ
  measurableSet_patch : ∀ α,
    MeasurableSet (verticalPatch (graph (patchGraph α)) (center α) (radius α))
  patch_cover : hausdorffP n k
    (K \ ⋃ α, verticalPatch (graph (patchGraph α)) (center α) (radius α)) = 0

namespace HorizontalDomainData

variable {ε δ : ℝ} {K : Set (Space n)} (D : HorizontalDomainData n k ε δ K)

/-- The patch centre `z_α = Φ(p_α)` in `X`. -/
def centerPoint (α : D.patchIndex) : Space n :=
  horizontalGraphMap (D.graph (D.patchGraph α)) (D.center α)

/-- The Euclidean base ball `B_α = B_U(p_α, ρ_α)`. -/
def baseBall (α : D.patchIndex) : Set (D.graph (D.patchGraph α)).direction :=
  Metric.ball (D.center α : (D.graph (D.patchGraph α)).direction) (D.radius α)

/-- The patch `P_α = Φ(D ∩ B_α)`. -/
def patch (α : D.patchIndex) : Set (Space n) :=
  horizontalPatch (D.graph (D.patchGraph α)) (D.trace (D.patchGraph α)) (D.center α)
    (D.radius α)

/-- The charge `c_α = ρ_α^k + λ(B_α) + H_P^k(P_α)`, with Euclidean base volume. -/
def charge (α : D.patchIndex) : ℝ≥0∞ :=
  ENNReal.ofReal (D.radius α) ^ k + volume (D.baseBall α) + hausdorffP n k (D.patch α)

/-- `Σ_j λ_j(D_j ∩ Φ_j⁻¹(U))` over the horizontal graphs. -/
def traceVolume (U : Set (Space n)) : ℝ≥0∞ :=
  ∑' j : D.graphIndex,
    volume (horizontalPreimage (D.graph j) (D.trace j) ∩ horizontalPreimage (D.graph j) U)

/-- `I(q,R) = {α : z_α ∈ P(q,R), ρ_α ≤ R}` among the horizontal patches. -/
def localIndex (q : Space n) (R : ℝ) : Set D.patchIndex :=
  {α | D.centerPoint α ∈ Metric.ball q R ∧ D.radius α ≤ R}

/-- `Σ_α c_α` over the horizontal patches. -/
def totalCharge : ℝ≥0∞ := ∑' α : D.patchIndex, D.charge α

/-- `Σ_{α ∈ I(q,R)} c_α` over the horizontal patches. -/
def localCharge (q : Space n) (R : ℝ) : ℝ≥0∞ := ∑' α : D.localIndex q R, D.charge α

end HorizontalDomainData

namespace VerticalDomainData

variable {ε δ : ℝ} {K : Set (Space n)} (D : VerticalDomainData n k ε δ K)

/-- The patch centre `z_α = Φ(p_α)` in `X`. -/
def centerPoint (α : D.patchIndex) : Space n :=
  (D.graph (D.patchGraph α)).map (D.center α)

/-- The max-parabolic base ball `B_α = B_{W×ℝ}(p_α, ρ_α)`. -/
def baseBall (α : D.patchIndex) : Set (SubspaceSpace (D.graph (D.patchGraph α)).direction) :=
  Metric.ball (D.center α) (D.radius α)

/-- The patch `P_α = Φ(B_α)`. -/
def patch (α : D.patchIndex) : Set (Space n) :=
  verticalPatch (D.graph (D.patchGraph α)) (D.center α) (D.radius α)

/-- The charge `c_α = ρ_α^k + λ(B_α) + H_P^k(P_α)`, with intrinsic product base volume. -/
def charge (α : D.patchIndex) : ℝ≥0∞ :=
  ENNReal.ofReal (D.radius α) ^ k +
    intrinsicParabolicVolume (D.graph (D.patchGraph α)).direction (D.baseBall α) +
      hausdorffP n k (D.patch α)

/-- `Σ_j λ_j(D_j ∩ Φ_j⁻¹(U))` over the vertical graphs. -/
def traceVolume (U : Set (Space n)) : ℝ≥0∞ :=
  ∑' j : D.graphIndex, intrinsicParabolicVolume (D.graph j).direction
    ((D.graph j).map ⁻¹' D.trace j ∩ (D.graph j).map ⁻¹' U)

/-- `I(q,R) = {α : z_α ∈ P(q,R), ρ_α ≤ R}` among the vertical patches. -/
def localIndex (q : Space n) (R : ℝ) : Set D.patchIndex :=
  {α | D.centerPoint α ∈ Metric.ball q R ∧ D.radius α ≤ R}

/-- `Σ_α c_α` over the vertical patches. -/
def totalCharge : ℝ≥0∞ := ∑' α : D.patchIndex, D.charge α

/-- `Σ_{α ∈ I(q,R)} c_α` over the vertical patches. -/
def localCharge (q : Space n) (R : ℝ) : ℝ≥0∞ := ∑' α : D.localIndex q R, D.charge α

end VerticalDomainData

/-! ## The cover and its estimates -/

/-- A graph-domain cover of `(K_H, K_V)` with bound `C`, tolerance `ε` and mesh `δ`,
with `K = K_H ∪ K_V`:
the typed data, the trace estimate for every Borel `U`, and the global and local patch
bounds for the whole family and for each typed subfamily, with the same right-hand
sides. -/
structure GraphDomainCover (n k : ℕ) (C ε δ : ℝ) (KH KV : Set (Space n)) where
  horizontal : HorizontalDomainData n k ε δ KH
  vertical : VerticalDomainData n k ε δ KV
  /-- `Σ_{T,j} λ_{T,j}(D_{T,j} ∩ Φ_{T,j}⁻¹(U)) ≤ C H_P^k(K ∩ U)` for every Borel `U`. -/
  trace_le : ∀ U : Set (Space n), MeasurableSet U →
    horizontal.traceVolume U + vertical.traceVolume U ≤
      ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ U)
  /-- `Σ_α c_α ≤ C H_P^k(K)`. -/
  totalCharge_le : horizontal.totalCharge + vertical.totalCharge ≤
    ENNReal.ofReal C * hausdorffP n k (KH ∪ KV)
  horizontal_totalCharge_le : horizontal.totalCharge ≤
    ENNReal.ofReal C * hausdorffP n k (KH ∪ KV)
  vertical_totalCharge_le : vertical.totalCharge ≤
    ENNReal.ofReal C * hausdorffP n k (KH ∪ KV)
  /-- `Σ_{α ∈ I(q,R)} c_α ≤ C H_P^k(K ∩ P(q,2R))` for every `q` and `R > 0`. -/
  localCharge_le : ∀ (q : Space n) (R : ℝ), 0 < R →
    horizontal.localCharge q R + vertical.localCharge q R ≤
      ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q (2 * R))
  horizontal_localCharge_le : ∀ (q : Space n) (R : ℝ), 0 < R →
    horizontal.localCharge q R ≤
      ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q (2 * R))
  vertical_localCharge_le : ∀ (q : Space n) (R : ℝ), 0 < R →
    vertical.localCharge q R ≤
      ENNReal.ofReal C * hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q (2 * R))

/-- `(K_H, K_V)` admits a graph-domain cover with bound `C`, tolerance `ε` and mesh `δ`. The standing assumptions of the
definition are part of the notion: compact carriers, `H_P^k(K_H ∪ K_V) < ∞`, and omitted
(empty) carriers for unavailable types. -/
structure HasGraphDomainCover {n : ℕ} (k : ℕ) (KH KV : Set (Space n)) (C ε δ : ℝ) : Prop where
  isCompact_horizontal : IsCompact KH
  isCompact_vertical : IsCompact KV
  hausdorff_lt_top : hausdorffP n k (KH ∪ KV) < ⊤
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) → KH = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) → KV = ∅
  cover : Nonempty (GraphDomainCover n k C ε δ KH KV)

end ParabolicRectifiability.Foundations
