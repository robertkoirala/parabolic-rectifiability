import ParabolicRectifiability.Geometry.Graphs
import ParabolicRectifiability.Geometry.Neck.CoherentData
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Definitions for the regular vertical carrier

Predicates and maps used by the intermediate statements behind
`vertical_core_graph_cover`, the construction of a regular vertical graph
carrying a retained set with small vertical square tail. Nothing here is an
estimate: the retained piece, the growth bound and the net-and-fitted-plane
family are hypotheses or constructions whose properties are proved elsewhere.

* `verticalPlaneModel L` is the vertical model `L × ℝ` of a spatial `m`-plane,
  as an element of the vertical model family of dimension `m + 2`.
* `verticalLift W g` is the lift `q ↦ (q.1 + g q, q.2)` from the intrinsic base
  `W × ℝ` (offset zero), the same map as in the regular-extension hubs.
* `baseSimilarity W p₀ a` is the parabolic similarity `p ↦ δ_{1/a}(p - p₀)` of
  the intrinsic base.
* `HasUpperGrowthUpTo η k U T` is the upper growth `η(P(q,r)) ≤ U r^k`, `r ≤ T`.
* `IsCarrierPiece η k a b T F` is a retained compact set with small square tail:
  lower mass `a r^k` and square tail at most `b` below `T`.
* `IsCarrierFamily η F Λ Φ` records the maximal nets, parents and best fitted
  planes of the carrier construction as a `CoherentFamily` indexed by the centers
  themselves. Coherence, square bounds and center heights are separate
  statements about such a family.

The last section proves small laws used in assembling the carrier: the same-time
distance, tolerance monotonicity of regular functions and covers, the same-base
cover conversion, level limits of the nets, and the split of the full-scale square
at a radius `R`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

variable {n m : ℕ}

/-- The vertical model `L × ℝ` of a spatial affine `m`-plane, in the vertical
family of dimension `m + 2`. Every vertical model of that dimension has spatial
rank `m`. -/
def verticalPlaneModel (L : AffineSpatialPlane n m) : Models n (m + 2) .vertical :=
  (⟨m, by omega, rfl, L⟩ : VerticalModel n (m + 2))

/-- The lift `q ↦ (q.1 + g q, q.2)` of a normal-valued function on the intrinsic
base `W × ℝ`; it is the image map of a regular vertical graph with offset zero. -/
abbrev verticalLift (W : Submodule ℝ (Spatial n)) (g : SubspaceSpace W → W.orthogonal)
    (q : SubspaceSpace W) : Space n :=
  (((q.1 : Spatial n) + (g q : Spatial n), q.2) : Space n)

/-- The parabolic similarity `p ↦ δ_{1/a}(p - p₀)` of the intrinsic base:
`(u,t) ↦ (a⁻¹ (u - u₀), a⁻² (t - t₀))`. -/
def baseSimilarity (W : Submodule ℝ (Spatial n)) (p₀ : SubspaceSpace W) (a : ℝ)
    (p : SubspaceSpace W) : SubspaceSpace W :=
  (a⁻¹ • (p.1 - p₀.1), Metric.Snowflaking.toSnowflaking (a⁻¹ ^ 2 * (p.2.val - p₀.2.val)))

/-- Upper `k`-growth `η(P(q,r)) ≤ U r^k` at every center and every radius `0 < r ≤ T`. -/
def HasUpperGrowthUpTo (η : Measure (Space n)) (k : ℕ) (U T : ℝ) : Prop :=
  ∀ (q : Space n) (r : ℝ), 0 < r → r ≤ T →
    η (Metric.ball q r) ≤ ENNReal.ofReal (U * r ^ k)

/-- A retained compact set with small square tail for the unchanged source `η`: lower mass `a r^k` on every ball of radius `0 < r ≤ T`
centered in `F`, and vertical square tail `∫_0^T β² dr/r ≤ b` at every point. -/
structure IsCarrierPiece (η : Measure (Space n)) (k : ℕ) (a b T : ℝ)
    (F : Set (Space n)) : Prop where
  compact : IsCompact F
  lower_mass : ∀ z ∈ F, ∀ r : ℝ, 0 < r → r ≤ T →
    ENNReal.ofReal (a * r ^ k) ≤ η (Metric.ball z r)
  small_tail : ∀ z ∈ F, squareEnergy η k .vertical T z ≤ ENNReal.ofReal b

/-- The net-and-fitted-plane family of the carrier construction for a retained set `F`, the unchanged source `η` and the fitting enlargement `Λ`.

The indices are the centers themselves. At level `j` (scale `r_j = 10^{-j} r_0`,
`r_0 = Φ.initialRadius`) the centers form a maximal `r_j`-separated subset of `F`;
each center of level `j + 1` has a parent of level `j` within `r_j`; the initial
plane is the plane of the level-zero centers; and each plane is a best affine
spatial `m`-plane for `η` on `P(z, Λ r_j)`, i.e. its vertical model attains the
fitting infimum that defines the natural vertical beta there. -/
structure IsCarrierFamily (η : Measure (Space n)) (F : Set (Space n)) (Λ : ℝ)
    (Φ : CoherentFamily n m (Space n)) : Prop where
  center_eq : ∀ j z, Φ.center j z = z
  index_subset : ∀ j, (↑(Φ.index j) : Set (Space n)) ⊆ F
  separated : ∀ j, ∀ z ∈ Φ.index j, ∀ w ∈ Φ.index j, z ≠ w → Φ.scale j ≤ dist z w
  covering : ∀ j, ∀ z ∈ F, ∃ w ∈ Φ.index j, dist z w < Φ.scale j
  parent_mem : ∀ j, ∀ z ∈ Φ.index (j + 1), Φ.parent (j + 1) z ∈ Φ.index j
  parent_dist : ∀ j, ∀ z ∈ Φ.index (j + 1), dist z (Φ.parent (j + 1) z) ≤ Φ.scale j
  initial_plane : ∀ z ∈ Φ.index 0, Φ.plane 0 z = Φ.initialPlane
  best_fit : ∀ j, ∀ z ∈ Φ.index j,
    fit η (verticalPlaneModel (Φ.plane j z)) z (Λ * Φ.scale j) =
      ⨅ L : Models n (m + 2) .vertical, fit η L z (Λ * Φ.scale j)

/-! ## Basic laws used in the carrier construction

Each law below follows directly from the definitions; none is an estimate of the
carrier argument. -/

/-- Two points at the same time are at the spatial Euclidean distance. -/
theorem dist_point_same_time (x y : Spatial n) (t : ℝ) :
    dist (point x t) (point y t) = ‖x - y‖ := by
  rw [dist_point, sub_self, abs_zero, Real.sqrt_zero]
  exact max_eq_left (norm_nonneg _)

/-- Regular vertical functions are monotone in their tolerance. -/
theorem IsRegularVerticalFunction.mono {W : Submodule ℝ (Spatial n)}
    {G : SubspaceSpace W → W.orthogonal} {ε ε' : ℝ}
    (h : IsRegularVerticalFunction W G ε) (hε : ε ≤ ε') :
    IsRegularVerticalFunction W G ε' := by
  obtain ⟨c, H, g, L, B, hG, hH, hL, hB, hrep, hsum⟩ := h
  exact ⟨c, H, g, L, B, hG, hH, hL, hB, hrep, hsum.trans hε⟩

/-- Regular vertical graph covers are monotone in their tolerance; the graphs and
their images are unchanged. -/
theorem HasRegularVerticalGraphCover.mono {k : ℕ} {S : Set (Space n)} {ε ε' : ℝ}
    (h : HasRegularVerticalGraphCover k S ε) (hε : ε ≤ ε') :
    HasRegularVerticalGraphCover k S ε' := by
  obtain ⟨I, G, hnull⟩ := h
  exact ⟨I, fun j =>
    { vertical_dimension := (G j).vertical_dimension
      direction := (G j).direction
      rank_eq := (G j).rank_eq
      offset := (G j).offset
      function := (G j).function
      regular := (G j).regular.mono hε }, hnull⟩

/-- Same-base regular functions with a Hausdorff-null remainder form a
`HasRegularVerticalGraphCover`: direction `W`, offset zero, rank guard `m + 2`. -/
theorem hasRegularVerticalGraphCover_of_sameBase (W : Submodule ℝ (Spatial n))
    (hm : Module.finrank ℝ W = m) (S : Set (Space n)) (ε : ℝ) (I : Set ℕ)
    (G : I → SubspaceSpace W → W.orthogonal)
    (hG : ∀ j, IsRegularVerticalFunction W (G j) ε)
    (hnull : hausdorffP n (m + 2) (S \ ⋃ j, Set.range (verticalLift W (G j))) = 0) :
    HasRegularVerticalGraphCover (m + 2) S ε := by
  refine ⟨I, fun j =>
    { vertical_dimension := by omega
      direction := W
      rank_eq := by rw [hm]
      offset := 0
      function := G j
      regular := hG j }, ?_⟩
  simpa only [RegularVerticalGraph.image, zero_add] using hnull

/-- Every point of the retained set is a limit of net centers whose levels tend to
infinity, because the level-`j` nets cover it at scale `r_j → 0`. -/
theorem IsCarrierFamily.isLevelLimit {η : Measure (Space n)} {F : Set (Space n)} {Λ : ℝ}
    {Φ : CoherentFamily n m (Space n)} (hΦ : IsCarrierFamily η F Λ Φ) {z : Space n}
    (hz : z ∈ F) : Φ.IsLevelLimit z := by
  choose w hw hd using fun j => hΦ.covering j z hz
  refine ⟨fun j => j, w, hw, Filter.tendsto_id, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hs : Filter.Tendsto (fun j : ℕ => Φ.scale j) Filter.atTop (nhds 0) := by
    simp only [CoherentFamily.scale, coherentScale]
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hs
  rw [hΦ.center_eq, dist_comm]
  exact (hd j).le

/-- The full-scale square splits into the square below `R` and the tail from `R`. -/
theorem lintegral_Ioi_betaSq_le (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (z : Space n) {R : ℝ} :
    ∫⁻ s in Ioi 0, betaSq μ k T z s ∂scaleMeasure ≤
      squareEnergy μ k T R z + ∫⁻ s in Ici R, betaSq μ k T z s ∂scaleMeasure := by
  have hsub : Ioi (0 : ℝ) ⊆ Ioo 0 R ∪ Ici R := by
    intro s hs
    rcases lt_or_ge s R with h | h
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr h
  exact (lintegral_mono_set hsub).trans (lintegral_union_le _ _ _)

end ParabolicRectifiability
