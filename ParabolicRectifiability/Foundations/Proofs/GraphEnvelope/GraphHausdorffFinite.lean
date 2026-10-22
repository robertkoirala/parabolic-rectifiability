import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Metric.BaseVolume

/-! # Local Hausdorff finiteness of graphs

Proves the statements of `fgenv_horizontal_hausdorffP_inter_ball_lt_top` and
`fgenv_vertical_hausdorffP_inter_ball_lt_top`:

* `fgenv_horizontal_hausdorffP_inter_ball_lt_top_proof`: for every horizontal graph
  of slope at most `ε` over an **arbitrary** domain, `H_P^k(G.image ∩ P(q,R)) < ∞`. This is an
  outer-measure statement; no measurability of the domain or image is used.
* `fgenv_vertical_hausdorffP_inter_ball_lt_top_proof`: the same for every full
  general regular vertical graph. Only the Lipschitz component of regularity is used.

Route: projection of the graph points in `P(q,R)` to a bounded set of base points
(orthogonality of the normal part), a Lipschitz bound for the graph map, the Lipschitz image
bound for Hausdorff measure and the base comparison of Hausdorff measure with volume, finite on
balls. At horizontal `k = 0` a point has `H_P^0` mass one; the bound is finite without a
separate case.

Helpers carry the prefix `bf1genv3_`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace ParabolicRectifiability.Foundations

/-- Orthogonal decomposition bound: if `u ∈ W` and `y ∈ Wᗮ`, then `‖u‖ ≤ ‖u + y + w‖ + ‖w‖`
for every `w`. -/
theorem bf1genv3_norm_le_of_orthogonal {n : ℕ} (W : Submodule ℝ (Spatial n))
    {u y : Spatial n} (hu : u ∈ W) (hy : y ∈ Wᗮ) (w : Spatial n) :
    ‖u‖ ≤ ‖u + y + w‖ + ‖w‖ := by
  have h1 : ⟪u, y⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hy
  have h2 : ⟪u, u + y + w⟫ = ‖u‖ ^ 2 + ⟪u, w⟫ := by
    rw [inner_add_right, inner_add_right, h1, real_inner_self_eq_norm_sq, add_zero]
  have h3 : ⟪u, u + y + w⟫ ≤ ‖u‖ * ‖u + y + w‖ := real_inner_le_norm _ _
  have h4 : -⟪u, w⟫ ≤ ‖u‖ * ‖w‖ := (neg_le_abs _).trans (abs_real_inner_le_norm u w)
  have key : ‖u‖ * ‖u‖ ≤ ‖u‖ * (‖u + y + w‖ + ‖w‖) := by
    rw [mul_add]
    nlinarith
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_left key hpos

/-- Horizontal core: the graph of `u ↦ (a + u + g u, h u)` over an arbitrary `D ⊆ U`, with the
slope bound of a horizontal graph, has finite `H^{dim U}` measure in every parabolic ball. -/
theorem bf1genv3_horizontal_core {n : ℕ} (U : Submodule ℝ (Spatial n)) (D : Set U)
    (a : Spatial n) (g : D → U.orthogonal) (h : D → ℝ) (ε : ℝ)
    (hs : ∀ u v : D, max ‖g u - g v‖ (Real.sqrt |h u - h v|) ≤
      ε * ‖((u.val : U) : Spatial n) - ((v.val : U) : Spatial n)‖)
    (q : Space n) (R : ℝ) :
    (Measure.hausdorffMeasure (Module.finrank ℝ U : ℝ) : Measure (Space n))
        ((Set.range fun u : D =>
            point (a + ((u.val : U) : Spatial n) + ((g u : U.orthogonal) : Spatial n)) (h u)) ∩
          Metric.ball q R) < ⊤ := by
  set F : D → Space n := fun u =>
    point (a + ((u.val : U) : Spatial n) + ((g u : U.orthogonal) : Spatial n)) (h u) with hFdef
  -- Lipschitz bound for the graph map.
  have hF : LipschitzWith (Real.toNNReal (1 + |ε|)) F := by
    apply LipschitzWith.of_dist_le'
    intro u v
    have huv : dist u v = ‖((u.val : U) : Spatial n) - ((v.val : U) : Spatial n)‖ := by
      rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm]
    rw [huv]
    set d := ‖((u.val : U) : Spatial n) - ((v.val : U) : Spatial n)‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    have hsl := hs u v
    have hg : ‖((g u : U.orthogonal) : Spatial n) - ((g v : U.orthogonal) : Spatial n)‖ ≤ ε * d :=
      (le_max_left _ _).trans hsl
    have ht : Real.sqrt |h u - h v| ≤ ε * d := (le_max_right _ _).trans hsl
    have hεd : ε * d ≤ |ε| * d := mul_le_mul_of_nonneg_right (le_abs_self ε) hd0
    change dist (point _ (h u)) (point _ (h v)) ≤ _
    rw [dist_point]
    apply max_le
    · have heq : (a + ((u.val : U) : Spatial n) + ((g u : U.orthogonal) : Spatial n)) -
          (a + ((v.val : U) : Spatial n) + ((g v : U.orthogonal) : Spatial n)) =
          (((u.val : U) : Spatial n) - ((v.val : U) : Spatial n)) +
            (((g u : U.orthogonal) : Spatial n) - ((g v : U.orthogonal) : Spatial n)) := by
        abel
      rw [heq]
      calc _ ≤ d + ‖((g u : U.orthogonal) : Spatial n) - ((g v : U.orthogonal) : Spatial n)‖ :=
            norm_add_le _ _
        _ ≤ (1 + |ε|) * d := by nlinarith
    · nlinarith [abs_nonneg ε]
  -- The intersection is the image of the preimage.
  set E : Set D := F ⁻¹' Metric.ball q R with hEdef
  have himg : (Set.range F ∩ Metric.ball q R) = F '' E := by
    rw [hEdef, Set.image_preimage_eq_inter_range, Set.inter_comm]
  -- The base points of `E` lie in a ball of `U`.
  set r : ℝ := |R| + ‖a - q.1‖ + 1 with hr
  have hsub : (Subtype.val : D → U) '' E ⊆ Metric.ball (0 : U) r := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : dist (F u) q < R := hu
    rw [Prod.dist_eq] at hu'
    have h1 : dist (a + ((u.val : U) : Spatial n) + ((g u : U.orthogonal) : Spatial n)) q.1 < R :=
      (le_max_left _ _).trans_lt hu'
    rw [dist_eq_norm] at h1
    have hb := bf1genv3_norm_le_of_orthogonal U (u.val : U).2 (g u : U.orthogonal).2 (a - q.1)
    have heq : ((u.val : U) : Spatial n) + ((g u : U.orthogonal) : Spatial n) + (a - q.1) =
        a + ((u.val : U) : Spatial n) + ((g u : U.orthogonal) : Spatial n) - q.1 := by
      abel
    rw [heq] at hb
    rw [mem_ball_zero_iff]
    change ‖((u.val : U) : Spatial n)‖ < r
    have := le_abs_self R
    linarith
  have hvol : (volume : Measure U) ((Subtype.val : D → U) '' E) < ⊤ :=
    (measure_mono hsub).trans_lt measure_ball_lt_top
  have himage := hausdorffMeasure_subtype_image_le hF (Module.finrank ℝ U) E
  have hcomp := (horizontal_base_hausdorff_comparison U ((Subtype.val : D → U) '' E)).2
  rw [himg]
  calc _ ≤ ((Real.toNNReal (1 + |ε|) : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ U) *
        (Measure.hausdorffMeasure (Module.finrank ℝ U : ℝ) : Measure U)
          ((Subtype.val : D → U) '' E) := himage
    _ ≤ ((Real.toNNReal (1 + |ε|) : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ U) *
        (horizontalHausdorffConstant (Module.finrank ℝ U) *
          (volume : Measure U) ((Subtype.val : D → U) '' E)) := by gcongr
    _ < ⊤ := ENNReal.mul_lt_top (by finiteness)
        (ENNReal.mul_lt_top (horizontalHausdorffConstant_lt_top _) hvol)

/-- Local Hausdorff finiteness of a horizontal graph (the type of
`fgenv_horizontal_hausdorffP_inter_ball_lt_top`). -/
theorem fgenv_horizontal_hausdorffP_inter_ball_lt_top_proof (n k : ℕ) (ε : ℝ)
    (G : HorizontalGraph n k ε) (q : Space n) (R : ℝ) :
    hausdorffP n k (G.image ∩ Metric.ball q R) < ⊤ := by
  obtain ⟨U, rfl, D, a, g, h, hs⟩ := G
  exact bf1genv3_horizontal_core U D a g h ε hs q R

/-- Vertical core: the full graph of a Lipschitz `Gf : W × Time → Wᗮ` has finite
`H^{dim W + 2}` measure in every parabolic ball. -/
theorem bf1genv3_vertical_core {n : ℕ} (W : Submodule ℝ (Spatial n)) (a : Spatial n)
    (Gf : SubspaceSpace W → W.orthogonal) (L : ℝ≥0) (hL : LipschitzWith L Gf)
    (q : Space n) (R : ℝ) :
    (Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) : Measure (Space n))
        ((Set.range fun p : SubspaceSpace W =>
            ((a + (p.1 : Spatial n) + (Gf p : Spatial n), p.2) : Space n)) ∩
          Metric.ball q R) < ⊤ := by
  set Φ : SubspaceSpace W → Space n := fun p =>
    ((a + (p.1 : Spatial n) + (Gf p : Spatial n), p.2) : Space n) with hΦdef
  -- Lipschitz bound for the graph map.
  have hΦ : LipschitzWith (1 + L) Φ := by
    apply LipschitzWith.of_dist_le_mul
    intro p p'
    have hp1 : dist p.1 p'.1 ≤ dist p p' := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hp2 : dist p.2 p'.2 ≤ dist p p' := by rw [Prod.dist_eq]; exact le_max_right _ _
    have hG : dist (Gf p) (Gf p') ≤ L * dist p p' := hL.dist_le_mul p p'
    have hpp : 0 ≤ dist p p' := dist_nonneg
    have hL0 : (0 : ℝ) ≤ L := L.2
    push_cast
    change max (dist (a + (p.1 : Spatial n) + (Gf p : Spatial n))
      (a + (p'.1 : Spatial n) + (Gf p' : Spatial n))) (dist p.2 p'.2) ≤ _
    apply max_le
    · have heq : dist (a + (p.1 : Spatial n) + (Gf p : Spatial n))
          (a + (p'.1 : Spatial n) + (Gf p' : Spatial n)) =
          ‖((p.1 : Spatial n) - (p'.1 : Spatial n)) +
            ((Gf p : Spatial n) - (Gf p' : Spatial n))‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      rw [heq]
      have e1 : ‖(p.1 : Spatial n) - (p'.1 : Spatial n)‖ = dist p.1 p'.1 := by
        rw [Subtype.dist_eq, dist_eq_norm]
      have e2 : ‖(Gf p : Spatial n) - (Gf p' : Spatial n)‖ = dist (Gf p) (Gf p') := by
        rw [Subtype.dist_eq, dist_eq_norm]
      calc _ ≤ ‖(p.1 : Spatial n) - (p'.1 : Spatial n)‖ +
            ‖(Gf p : Spatial n) - (Gf p' : Spatial n)‖ := norm_add_le _ _
        _ ≤ (1 + (L : ℝ)) * dist p p' := by rw [e1, e2]; nlinarith
    · nlinarith
  -- The intersection is the image of the preimage.
  set E : Set (SubspaceSpace W) := Φ ⁻¹' Metric.ball q R with hEdef
  have himg : (Set.range Φ ∩ Metric.ball q R) = Φ '' E := by
    rw [hEdef, Set.image_preimage_eq_inter_range, Set.inter_comm]
  -- The base points of `E` lie in a parabolic ball of `W × Time`.
  set r : ℝ := |R| + ‖a - q.1‖ + 1 with hr
  have hrpos : 0 < r := by positivity
  have hsub : E ⊆ Metric.ball (((0 : W), q.2) : SubspaceSpace W) r := by
    intro p hp
    have hp' : dist (Φ p) q < R := hp
    rw [Prod.dist_eq] at hp'
    have h1 : dist (a + (p.1 : Spatial n) + (Gf p : Spatial n)) q.1 < R :=
      (le_max_left _ _).trans_lt hp'
    have h2 : dist p.2 q.2 < R := (le_max_right _ _).trans_lt hp'
    rw [dist_eq_norm] at h1
    have hb := bf1genv3_norm_le_of_orthogonal W p.1.2 (Gf p).2 (a - q.1)
    have heq : (p.1 : Spatial n) + (Gf p : Spatial n) + (a - q.1) =
        a + (p.1 : Spatial n) + (Gf p : Spatial n) - q.1 := by
      abel
    rw [heq] at hb
    have hR := le_abs_self R
    have hn : 0 ≤ ‖a - q.1‖ := norm_nonneg _
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [dist_zero_right]
      change ‖(p.1 : Spatial n)‖ < r
      linarith
    · change dist p.2 q.2 < r
      linarith
  have hvol : intrinsicParabolicVolume W E < ⊤ := by
    refine (measure_mono hsub).trans_lt ?_
    rw [intrinsicParabolicVolume_ball W _ r hrpos]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by finiteness) (omega_lt_top _))
      (by finiteness)
  have himage := hausdorffMeasure_image_le_of_subset (hΦ.lipschitzOnWith (s := univ))
    (subset_univ E) (Module.finrank ℝ W + 2)
  have hcomp := (vertical_base_hausdorff_comparison W E).2
  rw [himg]
  calc _ ≤ ((1 + L : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ W + 2) *
        (Measure.hausdorffMeasure ((Module.finrank ℝ W + 2 : ℕ) : ℝ) :
          Measure (SubspaceSpace W)) E := himage
    _ ≤ ((1 + L : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ W + 2) *
        (verticalHausdorffConstant (Module.finrank ℝ W) * intrinsicParabolicVolume W E) := by
        gcongr
    _ < ⊤ := ENNReal.mul_lt_top (by finiteness)
        (ENNReal.mul_lt_top (verticalHausdorffConstant_lt_top _) hvol)

/-- Local Hausdorff finiteness of a vertical graph (the type of
`fgenv_vertical_hausdorffP_inter_ball_lt_top`). -/
theorem fgenv_vertical_hausdorffP_inter_ball_lt_top_proof (n k : ℕ) (ε : ℝ)
    (G : GeneralRegularVerticalGraph n k ε) (q : Space n) (R : ℝ) :
    hausdorffP n k (G.image ∩ Metric.ball q R) < ⊤ := by
  obtain ⟨_, W, rfl, a, Gf, hreg⟩ := G
  obtain ⟨_, L, _, hL, _, _, _⟩ := hreg
  exact bf1genv3_vertical_core W a Gf L hL q R

end ParabolicRectifiability.Foundations
