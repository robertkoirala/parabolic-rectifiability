import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Geometry.Horizontal.SpatialPieces
import ParabolicRectifiability.Geometry.Horizontal.TimeFlatten
import ParabolicRectifiability.Geometry.Horizontal.CoreDensity

/-! # The horizontal core graph cover

Proves `horizontal_core_graph_cover_proof`, with the type of `horizontal_core_graph_cover`
of the `Decomposition` development. The proof assembles three ingredients:
`exists_spatial_graph_pieces_proof` (spatial graph pieces),
`exists_time_flat_compact_pieces_proof` (time-flat compact pieces) and
`horizontalChart_coreDensity_proof` (density of the core).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability


/-- The parabolic distance of two arbitrary points: the maximum of the Euclidean
spatial distance and the square root of the time separation. -/
theorem dist_space_eq_max {n : ℕ} (z w : Space n) :
    dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) :=
  dist_point z.1 w.1 z.2.val w.2.val

/-- The coefficient clause of the time-flattening lemma: if `√|t_z - t_w| ≤ c d_P(z,w)` with `c < 1`, the maximum defining
`d_P(z,w)` is the spatial distance, and the time modulus with respect to spatial
distance is at most `c`. -/
theorem sqrt_time_le_of_coefficient_lt_one {n : ℕ} {z w : Space n} {c : ℝ} (hc : c < 1)
    (h : Real.sqrt |z.2.val - w.2.val| ≤ c * dist z w) :
    dist z w = ‖z.1 - w.1‖ ∧ Real.sqrt |z.2.val - w.2.val| ≤ c * ‖z.1 - w.1‖ := by
  have hd := dist_space_eq_max z w
  have hx : 0 ≤ ‖z.1 - w.1‖ := norm_nonneg _
  rcases le_or_gt (Real.sqrt |z.2.val - w.2.val|) ‖z.1 - w.1‖ with hle | hlt
  · have he : dist z w = ‖z.1 - w.1‖ := by rw [hd, max_eq_left hle]
    refine ⟨he, ?_⟩
    rw [← he]
    exact h
  · exfalso
    rw [hd, max_eq_right hlt.le] at h
    nlinarith [mul_pos (sub_pos.mpr hc) (hx.trans_lt hlt)]

/-- A set of points whose spatial parts have
normal slope at most `s` over a rank-`k` subspace `W`, and whose times satisfy
`|t_z - t_w|^{1/2} ≤ ε₀ |x_z - x_w|`, lies in the image of one horizontal subset graph
with constant `ε`, provided `s ≤ ε` and `ε₀ (1 + s) ≤ ε`. The domain is the projection
of the set to `W`; projection is injective on the set. -/
theorem exists_horizontalGraph_of_flat_slope {n k : ℕ} {ε s ε₀ : ℝ}
    (W : Submodule ℝ (Spatial n)) (hW : Module.finrank ℝ W = k) (Z : Set (Space n))
    (hsε : s ≤ ε) (hε₀ : 0 ≤ ε₀) (hε₀s : ε₀ * (1 + s) ≤ ε)
    (hslope : ∀ z ∈ Z, ∀ w ∈ Z,
      ‖Wᗮ.starProjection (z.1 - w.1)‖ ≤ s * ‖W.starProjection (z.1 - w.1)‖)
    (hflat : ∀ z ∈ Z, ∀ w ∈ Z, Real.sqrt |z.2.val - w.2.val| ≤ ε₀ * ‖z.1 - w.1‖) :
    ∃ G : HorizontalGraph n k ε, Z ⊆ G.image := by
  classical
  -- Points of `Z` are determined by their projection to `W`.
  have key : ∀ z ∈ Z, ∀ w ∈ Z, W.starProjection (z.1 - w.1) = 0 → z = w := by
    intro z hz w hw h0
    have h1 : Wᗮ.starProjection (z.1 - w.1) = 0 := by
      have h := hslope z hz w hw
      rw [h0, norm_zero, mul_zero] at h
      exact norm_le_zero_iff.mp h
    have hx : z.1 = w.1 := by
      have h := Submodule.starProjection_add_starProjection_orthogonal (K := W) (z.1 - w.1)
      rw [h0, h1, add_zero] at h
      exact sub_eq_zero.mp h.symm
    have ht : z.2.val = w.2.val := by
      have h := hflat z hz w hw
      rw [hx, sub_self, norm_zero, mul_zero] at h
      have h2 : Real.sqrt |z.2.val - w.2.val| = 0 := le_antisymm h (Real.sqrt_nonneg _)
      rw [Real.sqrt_eq_zero (abs_nonneg _), abs_eq_zero, sub_eq_zero] at h2
      exact h2
    calc z = point z.1 z.2.val := rfl
      _ = point w.1 w.2.val := by rw [hx, ht]
      _ = w := rfl
  let D : Set W := (fun z : Space n => W.orthogonalProjectionOnto z.1) '' Z
  have hmem : ∀ p : D, ∃ z, z ∈ Z ∧ W.orthogonalProjectionOnto z.1 = (p : W) :=
    fun p => p.2
  choose pt hpt using hmem
  refine ⟨{ direction := W
            rank_eq := hW
            domain := D
            offset := 0
            normal := fun p => Wᗮ.orthogonalProjectionOnto (pt p).1
            time := fun p => (pt p).2.val
            small_slope := ?_ }, ?_⟩
  · intro u v
    obtain ⟨hzu, hpu⟩ := hpt u
    obtain ⟨hzv, hpv⟩ := hpt v
    have hbase : ((u : W) : Spatial n) - ((v : W) : Spatial n) =
        W.starProjection ((pt u).1 - (pt v).1) := by
      rw [map_sub, Submodule.starProjection_apply, Submodule.starProjection_apply, hpu, hpv]
    have hnormal : ‖Wᗮ.orthogonalProjectionOnto (pt u).1 - Wᗮ.orthogonalProjectionOnto (pt v).1‖ =
        ‖Wᗮ.starProjection ((pt u).1 - (pt v).1)‖ := by
      rw [← map_sub, ← Submodule.norm_coe, ← Submodule.starProjection_apply]
    have hsl := hslope _ hzu _ hzv
    have hfl := hflat _ hzu _ hzv
    have hN0 : 0 ≤ ‖W.starProjection ((pt u).1 - (pt v).1)‖ := norm_nonneg _
    have hsplit : ‖(pt u).1 - (pt v).1‖ ≤
        (1 + s) * ‖W.starProjection ((pt u).1 - (pt v).1)‖ := by
      calc ‖(pt u).1 - (pt v).1‖
          = ‖W.starProjection ((pt u).1 - (pt v).1) +
              Wᗮ.starProjection ((pt u).1 - (pt v).1)‖ := by
            rw [Submodule.starProjection_add_starProjection_orthogonal]
        _ ≤ ‖W.starProjection ((pt u).1 - (pt v).1)‖ +
              ‖Wᗮ.starProjection ((pt u).1 - (pt v).1)‖ := norm_add_le _ _
        _ ≤ ‖W.starProjection ((pt u).1 - (pt v).1)‖ +
              s * ‖W.starProjection ((pt u).1 - (pt v).1)‖ := by linarith
        _ = (1 + s) * ‖W.starProjection ((pt u).1 - (pt v).1)‖ := by ring
    rw [hbase, hnormal]
    refine max_le ?_ ?_
    · calc ‖Wᗮ.starProjection ((pt u).1 - (pt v).1)‖
          ≤ s * ‖W.starProjection ((pt u).1 - (pt v).1)‖ := hsl
        _ ≤ ε * ‖W.starProjection ((pt u).1 - (pt v).1)‖ :=
            mul_le_mul_of_nonneg_right hsε hN0
    · calc Real.sqrt |(pt u).2.val - (pt v).2.val|
          ≤ ε₀ * ‖(pt u).1 - (pt v).1‖ := hfl
        _ ≤ ε₀ * ((1 + s) * ‖W.starProjection ((pt u).1 - (pt v).1)‖) :=
            mul_le_mul_of_nonneg_left hsplit hε₀
        _ = (ε₀ * (1 + s)) * ‖W.starProjection ((pt u).1 - (pt v).1)‖ := by ring
        _ ≤ ε * ‖W.starProjection ((pt u).1 - (pt v).1)‖ :=
            mul_le_mul_of_nonneg_right hε₀s hN0
  · intro z hz
    have hzD : W.orthogonalProjectionOnto z.1 ∈ D := ⟨z, hz, rfl⟩
    have hpz : pt ⟨_, hzD⟩ = z := by
      apply key _ (hpt ⟨_, hzD⟩).1 z hz
      rw [map_sub, Submodule.starProjection_apply, Submodule.starProjection_apply,
        (hpt ⟨_, hzD⟩).2]
      exact sub_self _
    simp only [HorizontalGraph.image, Set.mem_range]
    refine ⟨⟨_, hzD⟩, ?_⟩
    dsimp only
    rw [hpz, zero_add, ← Submodule.starProjection_apply, ← Submodule.starProjection_apply,
      Submodule.starProjection_add_starProjection_orthogonal]
    rfl

/-- **The horizontal core graph cover**, with the type of `horizontal_core_graph_cover`.
It is proved from `horizontalChart_coreDensity_proof`, `exists_time_flat_compact_pieces_proof` with `ε₀ = ε/2`, and
`exists_spatial_graph_pieces_proof` with slope `s = min ε 1`, by
`exists_horizontalGraph_of_flat_slope` on each intersection of a spatial piece with a time-flat
piece. The exceptional set is contained in the `H^k`-null complement of the time-flat pieces
together with the Lipschitz image of a `μH[k]`-null parameter set. The core and its measure do
not depend on `ε`. -/
theorem horizontal_core_graph_cover_proof {n k : ℕ} {K : Set (Space n)}
    (hK : IsHorizontalCore k K) (ε : ℝ) (hε : 0 < ε) :
    HasHorizontalGraphCover k K ε := by
  classical
  obtain ⟨hKc, ⟨C⟩, hsq⟩ := hK
  have himage := C.image
  have hLip := C.chart_lipschitz
  have hAnti := C.chart_antilipschitz
  set φ : C.domain → Space n := fun u => point (C.spatial u) (C.time u)
  obtain ⟨hfin, -, hdens⟩ := horizontalChart_coreDensity_proof C.compact_domain hLip hAnti
  rw [himage] at hfin hdens
  obtain ⟨P, -, -, hPflat, hPnull⟩ :=
    exists_time_flat_compact_pieces_proof hKc hfin hdens hsq (half_pos hε)
  obtain ⟨S, W, -, hW, hslope, hSnull⟩ :=
    exists_spatial_graph_pieces_proof C.spatial_lipschitz C.spatial_antilipschitz
      (lt_min hε one_pos)
  have hε₀s : ε / 2 * (1 + min ε 1) ≤ ε := by
    have h1 : 1 + min ε 1 ≤ 2 := by linarith [min_le_right ε 1]
    calc ε / 2 * (1 + min ε 1) ≤ ε / 2 * 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = ε := by ring
  -- One graph for each pair of a spatial piece and a time-flat piece.
  have hgraph : ∀ m i : ℕ, ∃ G : HorizontalGraph n k ε,
      (φ '' {u : C.domain | (u : Spatial k) ∈ S m} ∩ P i) ⊆ G.image := by
    intro m i
    refine exists_horizontalGraph_of_flat_slope (W m) (hW m) _ (min_le_left ε 1)
      (half_pos hε).le hε₀s ?_ ?_
    · rintro z ⟨⟨u, hu, rfl⟩, -⟩ w ⟨⟨v, hv, rfl⟩, -⟩
      exact hslope m (u : Spatial k) hu (v : Spatial k) hv
    · rintro z ⟨-, hz⟩ w ⟨-, hw⟩
      exact hPflat i z hz w hw
  choose G hG using hgraph
  refine ⟨Set.univ, fun i => G (Nat.unpair i.1).1 (Nat.unpair i.1).2, ?_⟩
  have hsub : K \ ⋃ i : (Set.univ : Set ℕ), (G (Nat.unpair i.1).1 (Nat.unpair i.1).2).image ⊆
      (K \ ⋃ i, P i) ∪ φ '' {u : C.domain | (u : Spatial k) ∈ (⋃ m, S m)ᶜ} := by
    rintro z ⟨hzK, hzG⟩
    rw [← himage] at hzK
    obtain ⟨u, rfl⟩ := hzK
    by_cases hP : φ u ∈ ⋃ i, P i
    · right
      refine ⟨u, ?_, rfl⟩
      show (u : Spatial k) ∉ ⋃ m, S m
      intro hS
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hS
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hP
      apply hzG
      refine Set.mem_iUnion.mpr ⟨⟨Nat.pair m i, Set.mem_univ _⟩, ?_⟩
      show φ u ∈ (G (Nat.unpair (Nat.pair m i)).1 (Nat.unpair (Nat.pair m i)).2).image
      rw [Nat.unpair_pair]
      exact hG m i ⟨⟨u, hm, rfl⟩, hi⟩
    · left
      exact ⟨himage ▸ Set.mem_range_self u, hP⟩
  have hnull : hausdorffP n k (φ '' {u : C.domain | (u : Spatial k) ∈ (⋃ m, S m)ᶜ}) = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc hausdorffP n k (φ '' {u : C.domain | (u : Spatial k) ∈ (⋃ m, S m)ᶜ})
        ≤ (C.constant : ℝ≥0∞) ^ k * (Measure.hausdorffMeasure (k : ℝ) : Measure (Spatial k))
            (Subtype.val '' {u : C.domain | (u : Spatial k) ∈ (⋃ m, S m)ᶜ}) :=
          hausdorffMeasure_subtype_image_le hLip k _
      _ ≤ (C.constant : ℝ≥0∞) ^ k * (Measure.hausdorffMeasure (k : ℝ) : Measure (Spatial k))
            (⋃ m, S m)ᶜ := by
          gcongr
          rintro x ⟨u, hu, rfl⟩
          exact hu
      _ = 0 := by rw [hSnull, mul_zero]
  exact measure_mono_null hsub (measure_union_null hPnull hnull)

end ParabolicRectifiability
