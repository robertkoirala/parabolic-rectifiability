import ParabolicRectifiability.Geometry.Chart.Construction
import ParabolicRectifiability.Geometry.ProjectionReset
import ParabolicRectifiability.Analysis.QuantitativeInverse

/-!
# Induction estimates and parent patch for the coherent chart

Two auxiliary statements used in the proof of `vertical_coherent_chart`, for the
construction of the chart (`CoherentChart.stage`):

* `induction_estimates_proof` (the induction estimates): rank of every `D_u F_j`, `j ≤ N + 1`, the cross-index tangent and
  height estimate `α_j + H_j ≤ A h⁻¹ e_j(q_j)` for `j ≤ N`, and the displacement
  `|F_{j+1} - F_j| ≤ ε r_j`. No path-energy hypothesis is used.
* `parent_patch_proof` (the parent patch). Its extra first argument is the statement of the
  recurrence estimates (speed and curvature bounds of the recursion), of which only the
  speed and curvature bounds are used.

The inputs are the smooth partition (`isSmoothParabolicPartition_parabolicWeight`),
the one-step estimate (`CoherentProjection.one_step`), the reset
(`ProjectionReset.reset`) and the quantitative inverse function theorem
(`QuantitativeInverse.exists_mem_closedBall_eq`).

**Mathematical route of the induction estimates.** At level `0` the tangent is the direction of `L_*` and
`F_0 ∈ L_*`; the root comparisons give `α_0 + H_0 ≤ 4 e_0`. At level `k + 1` with an
active index `a₀`, the predecessor `q⁻ = (F_k, t)` lies within `(ε + 3h + 1) r_k < 2 r_k` of
the parent `z_{k,p(a₀)}`, so the level-`k` weights have full weight near `q⁻`. Some index
`c₀` has positive weight at `q⁻`; it serves as the reference plane of the reset (`B = 3`),
with incoming tangent within `ε` of `L_{k,c₀}` by the previous level. The same-level
comparisons with `c₀` and the adjacent comparisons `(a', c₀)` all occur in `e_{k+1}(q)`,
which gives `α + H ≤ (8(1 + 3C₀) + 1 + 70) e_{k+1} ≤ A h⁻¹ e_{k+1}`. The one-step
quadratic estimate with `α + H ≤ ε` keeps the rank and gives the displacement.
-/

noncomputable section

namespace ParabolicRectifiability

open scoped ENNReal ContDiff RealInnerProductSpace
open Filter Topology

variable {n m : ℕ} {ι : Type*}

/-! ## Affine planes: anchor change and nearest points -/

namespace AffineSpatialPlane

/-- A point of the plane is its own nearest point. -/
theorem projection_eq_self_of_mem (L : AffineSpatialPlane n m) {y : Spatial n}
    (hy : y ∈ L.toSet) : L.projection y = y := by
  have h1 : L.direction.starProjection (y - L.anchor) = y - L.anchor :=
    L.direction.starProjection_eq_self_iff.mpr ((L.mem_toSet y).mp hy)
  have h2 : L.direction.starProjection L.anchor = 0 := L.linearProjection_anchor
  rw [map_sub, h2, sub_zero] at h1
  show L.anchor + L.direction.starProjection y = y
  rw [h1]
  abel

/-- Moving the anchor from `x` to `y` changes the gap of the nearest points of
two planes by at most `‖P_L - P_{L'}‖ ‖y - x‖`. -/
theorem norm_projection_sub_projection_le (L L' : AffineSpatialPlane n m) (x y : Spatial n) :
    ‖L.projection y - L'.projection y‖ ≤
      ‖L.projection x - L'.projection x‖ +
        ‖L.linearProjection - L'.linearProjection‖ * ‖y - x‖ := by
  have h : L.projection y - L'.projection y = (L.projection x - L'.projection x) +
      (L.linearProjection - L'.linearProjection) (y - x) := by
    have h1 : (L.linearProjection - L'.linearProjection) (y - x) =
        L.linearProjection (y - x) - L'.linearProjection (y - x) := rfl
    rw [h1]
    simp only [projection, map_sub]
    abel
  rw [h]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl ((L.linearProjection - L'.linearProjection).le_opNorm _))

/-- The distance to one plane is at most the distance to another plus the gap of the two
nearest points. -/
theorem infDist_le_infDist_add (K L : AffineSpatialPlane n m) (x : Spatial n) :
    Metric.infDist x L.toSet ≤ Metric.infDist x K.toSet + ‖L.projection x - K.projection x‖ := by
  rw [← ProjectionReset.residual_eq_infDist, ← ProjectionReset.residual_eq_infDist]
  calc ‖x - L.projection x‖ = ‖(x - K.projection x) - (L.projection x - K.projection x)‖ := by
        congr 1; abel
    _ ≤ _ := norm_sub_le _ _

end AffineSpatialPlane

/-- The direction part of a plane comparison. -/
theorem norm_linearProjection_sub_le_planeComparison {x : Spatial n} {r : ℝ} (hr : 0 < r)
    (L L' : AffineSpatialPlane n m) :
    ‖L.linearProjection - L'.linearProjection‖ ≤ planeComparison x r L L' :=
  le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hr.le) (norm_nonneg _))

/-- A plane comparison at scale `r` and anchor `x` bounds the gap of the nearest points at
any `y` with `‖y - x‖ ≤ c r`, `c ≥ 1`, by `c r` times the comparison. -/
theorem norm_projection_sub_le_of_planeComparison {L L' : AffineSpatialPlane n m}
    {x y : Spatial n} {r c e : ℝ} (hr : 0 < r) (hc : 1 ≤ c) (hxy : ‖y - x‖ ≤ c * r)
    (he : planeComparison x r L L' ≤ e) :
    ‖L.projection y - L'.projection y‖ ≤ c * r * e := by
  have h1 := L.norm_projection_sub_projection_le L' x y
  unfold planeComparison at he
  set D₁ := ‖L.linearProjection - L'.linearProjection‖ with hD₁
  set D := ‖L.projection x - L'.projection x‖ with hD
  have hD₁0 : 0 ≤ D₁ := norm_nonneg _
  have hD0 : 0 ≤ D := norm_nonneg _
  have hrD : 0 ≤ r⁻¹ * D := mul_nonneg (inv_nonneg.mpr hr.le) hD0
  have hD₁e : D₁ ≤ e := by linarith
  have hDle : D ≤ r * (e - D₁) := by
    calc D = r * (r⁻¹ * D) := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
      _ ≤ r * (e - D₁) := mul_le_mul_of_nonneg_left (by linarith) hr.le
  have h2 : D₁ * ‖y - x‖ ≤ D₁ * (c * r) := mul_le_mul_of_nonneg_left hxy hD₁0
  have hk : 0 ≤ (c - 1) * r * (e - D₁) :=
    mul_nonneg (mul_nonneg (by linarith) hr.le) (by linarith)
  calc ‖L.projection y - L'.projection y‖ ≤ D + D₁ * ‖y - x‖ := h1
    _ ≤ r * (e - D₁) + D₁ * (c * r) := add_le_add hDle h2
    _ = c * r * e - (c - 1) * r * (e - D₁) := by ring
    _ ≤ c * r * e := sub_le_self _ hk

namespace CoherentChart

/-! ## Parabolic distances and smooth sections -/

/-- The spatial gap is at most the parabolic distance. -/
theorem norm_fst_sub_le_dist (z w : Space n) : ‖z.1 - w.1‖ ≤ dist z w := by
  rw [← dist_eq_norm, Prod.dist_eq]
  exact le_max_left _ _

/-- At equal times the parabolic distance is the spatial distance. -/
theorem dist_point_point_same (x y : Spatial n) (t : ℝ) :
    dist (point x t) (point y t) = ‖x - y‖ := by
  rw [dist_point, sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)]

theorem point_fst_val (c : Space n) : point c.1 c.2.val = c := rfl

section Sections

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {f : E × ℝ → G}

theorem differentiableAt_left (hf : ContDiff ℝ ∞ f) (x : E) (t : ℝ) :
    DifferentiableAt ℝ (fun y => f (y, t)) x :=
  ((hf.differentiable (by simp)) (x, t)).comp x
    (differentiableAt_id.prodMk (differentiableAt_const t))

theorem differentiableAt_right (hf : ContDiff ℝ ∞ f) (x : E) (t : ℝ) :
    DifferentiableAt ℝ (fun s => f (x, s)) t :=
  ((hf.differentiable (by simp)) (x, t)).comp t
    ((differentiableAt_const x).prodMk differentiableAt_id)

theorem contDiff_left (hf : ContDiff ℝ ∞ f) (t : ℝ) : ContDiff ℝ ∞ (fun y => f (y, t)) :=
  hf.comp (contDiff_id.prodMk contDiff_const)

end Sections

/-- Orthogonal projections onto equal subspaces are equal. -/
theorem starProjection_congr {T T' : Submodule ℝ (Spatial n)} (h : T = T')
    [T.HasOrthogonalProjection] [T'.HasOrthogonalProjection] :
    T.starProjection = T'.starProjection := by
  subst h
  rfl

/-! ## The level weights -/

section Family

variable {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ}

/-- The smooth partition at every level `j ≤ N`. -/
theorem partition_level (hσ : 0 < σ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) :
    IsSmoothParabolicPartition n (F.index j) (F.center j) (F.scale j) (chartC₀ n σ)
      (parabolicWeight (F.scale j) (F.index j) (F.center j)) := by
  refine isSmoothParabolicPartition_parabolicWeight hσ (scale_pos F j) (F.index j)
    (F.center j) ?_
  intro a ha b hb hab
  have hsep := hF.separated j hj a ha b hb hab
  have hpos : 0 < σ * F.scale j := mul_pos hσ (scale_pos F j)
  exact Metric.ball_disjoint_ball (by linarith)

theorem differentiableAt_weight_spatial (F : CoherentFamily n m ι) (j : ℕ) (a : ι)
    (x : Spatial n) (t : ℝ) : DifferentiableAt ℝ (fun y => weight F j a y t) x :=
  differentiableAt_left (contDiff_weight F j a) x t

theorem differentiableAt_weight_time (F : CoherentFamily n m ι) (j : ℕ) (a : ι)
    (x : Spatial n) (t : ℝ) : DifferentiableAt ℝ (weight F j a x) t :=
  differentiableAt_right (contDiff_weight F j a) x t

/-- The quantitative weight hypotheses of the one-step estimate at every level `j ≤ N`. -/
theorem weightBounds_level (hσ : 0 < σ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N)
    (x : Spatial n) (t : ℝ) :
    CoherentProjection.WeightBounds (F.index j) (weight F j) x t (chartC₀ n σ) (F.scale j) := by
  have hP := partition_level hσ hF hj
  refine ⟨fun a _ => hP.nonneg a (x, t), hP.sum_le_one (x, t), hP.first x t, ?_⟩
  refine le_trans (Finset.sum_le_sum fun a _ => ?_) (hP.second x t)
  exact le_add_of_nonneg_left (by positivity)

/-- An active index has its center within `3 r_j` (closed supports in the open balls). -/
theorem dist_lt_of_isActive (hσ : 0 < σ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N)
    {a : ι} {x : Spatial n} {t : ℝ} (h : IsActive F j a x t) :
    dist (point x t) (F.center j a) < 3 * F.scale j := by
  have hP := partition_level hσ hF hj
  rcases h with h | h | h | h
  · exact hP.tsupport_subset a (x, t) (subset_tsupport _ h)
  · exact hP.tsupport_fderiv_subset a (x, t) (subset_tsupport _ h)
  · exact hP.tsupport_fderiv_fderiv_subset a (x, t) (subset_tsupport _ h)
  · exact hP.tsupport_deriv_subset a (x, t) (subset_tsupport _ h)

/-- Within `2 r_j` of a center the level-`j` weights have full weight on a spatial
neighbourhood (at the same time). -/
theorem eventually_sum_weight_eq_one (hσ : 0 < σ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ}
    (hj : j ≤ N) {b : ι} (hb : b ∈ F.index j) {x : Spatial n} {t : ℝ}
    (hx : dist (point x t) (F.center j b) < 2 * F.scale j) :
    ∀ᶠ y in 𝓝 x, ∑ a ∈ F.index j, weight F j a y t = 1 := by
  have hP := partition_level hσ hF hj
  have hc : Continuous fun y : Spatial n => point y t :=
    continuous_id.prodMk continuous_const
  have hopen : IsOpen ((fun y => point y t) ⁻¹' Metric.ball (F.center j b) (2 * F.scale j)) :=
    Metric.isOpen_ball.preimage hc
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact hP.sum_eq_one (y, t) ⟨b, hb, hy⟩

theorem exists_weight_ne_zero {j : ℕ} {x : Spatial n} {t : ℝ}
    (h : ∑ a ∈ F.index j, weight F j a x t = 1) : ∃ c ∈ F.index j, weight F j c x t ≠ 0 :=
  Finset.exists_ne_zero_of_sum_ne_zero (by rw [h]; exact one_ne_zero)

/-! ## Derivatives of the stages and their tangent spaces -/

theorem hasFDerivAt_stageMap (F : CoherentFamily n m ι) (j : ℕ) (x : Spatial n) (t : ℝ) :
    HasFDerivAt (fun y => stageMap F j y t)
      (CoherentProjection.spatialDerivative (F.index j) (F.plane j) (weight F j) x t) x :=
  CoherentProjection.hasFDerivAt_sigma _ _ _ x t
    (fun a _ => differentiableAt_weight_spatial F j a x t)

theorem differentiableAt_stage (P : InitialChart F) (j : ℕ) (u : Spatial m) (t : ℝ) :
    DifferentiableAt ℝ (fun v => stage F P j v t) u :=
  differentiableAt_left (contDiff_stage F P j) u t

/-- The chain rule for `F_{k+1} = σ_k(F_k, t)`. -/
theorem fderiv_stage_succ (P : InitialChart F) (k : ℕ) (u : Spatial m) (t : ℝ) :
    fderiv ℝ (fun v => stage F P (k + 1) v t) u =
      (fderiv ℝ (fun y => stageMap F k y t) (stage F P k u t)).comp
        (fderiv ℝ (fun v => stage F P k v t) u) := by
  show fderiv ℝ ((fun y => stageMap F k y t) ∘ (fun v => stage F P k v t)) u = _
  exact fderiv_comp u (hasFDerivAt_stageMap F k _ t).differentiableAt
    (differentiableAt_stage P k u t)

theorem fderiv_stage_zero (P : InitialChart F) (u : Spatial m) (t : ℝ) :
    fderiv ℝ (fun v => stage F P 0 v t) u = P.isometry.toContinuousLinearMap :=
  ((P.isometry.toContinuousLinearMap.hasFDerivAt).const_add P.origin).fderiv

/-- `T_{k+1}` is the image of `T_k` under `D_x σ_k`. -/
theorem tangent_succ (P : InitialChart F) (k : ℕ) (u : Spatial m) (t : ℝ) :
    tangent F P (k + 1) u t = ProjectionReset.restrictedRange
      (fderiv ℝ (fun y => stageMap F k y t) (stage F P k u t)) (tangent F P k u t) := by
  unfold tangent ProjectionReset.restrictedRange ProjectionReset.restrictedMap
  rw [fderiv_stage_succ]
  ext y
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨⟨_, LinearMap.mem_range_self _ v⟩, rfl⟩
  · rintro ⟨⟨z, hz⟩, rfl⟩
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hz
    exact ⟨v, rfl⟩

theorem tangent_zero (P : InitialChart F) (u : Spatial m) (t : ℝ) :
    tangent F P 0 u t = F.initialPlane.direction := by
  unfold tangent
  rw [fderiv_stage_zero]
  exact P.range_eq

theorem stage_zero_mem (P : InitialChart F) (u : Spatial m) (t : ℝ) :
    stage F P 0 u t ∈ F.initialPlane.toSet := by
  have h1 : P.origin - F.initialPlane.anchor ∈ F.initialPlane.direction := P.origin_mem
  have h2 : P.isometry u ∈ F.initialPlane.direction := by
    rw [← P.range_eq]
    exact LinearMap.mem_range_self _ u
  show P.origin + P.isometry u - F.initialPlane.anchor ∈ F.initialPlane.direction
  have h3 : P.origin + P.isometry u - F.initialPlane.anchor =
      (P.origin - F.initialPlane.anchor) + P.isometry u := by abel
  rw [h3]
  exact F.initialPlane.direction.add_mem h1 h2

/-! ## The local comparison coefficient -/

/-- `e_j ≤ δ` for `j ≤ N`. -/
theorem localError_le_ofReal (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N)
    (q : Space n) : localError F j q ≤ ENNReal.ofReal δ := by
  cases j with
  | zero =>
    simp only [localError]
    refine iSup_le fun _ => iSup₂_le fun a ha => iSup_le fun _ => ?_
    exact ENNReal.ofReal_le_ofReal (hF.root a ha)
  | succ k =>
    have hr := scale_pos F k
    simp only [localError]
    refine iSup_le fun _ => max_le ?_ ?_
    · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
      refine ENNReal.ofReal_le_ofReal (hF.same k (by omega) a ha b hb ?_)
      calc dist (F.center k a) (F.center k b) ≤ dist (F.center k a) q + dist (F.center k b) q :=
            dist_triangle_right _ _ _
        _ ≤ 8 * F.scale k + 8 * F.scale k := add_le_add h.1 h.2
        _ ≤ 20 * F.scale k := by linarith
    · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun h => ?_
      refine ENNReal.ofReal_le_ofReal (hF.adjacent k (by omega) a ha b hb ?_)
      calc dist (F.center (k + 1) a) (F.center k b)
          ≤ dist (F.center (k + 1) a) q + dist (F.center k b) q := dist_triangle_right _ _ _
        _ ≤ 8 * F.scale k + 8 * F.scale k := add_le_add h.1 h.2
        _ ≤ 20 * F.scale k := by linarith

theorem localError_ne_top (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) (q : Space n) :
    localError F j q ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (localError_le_ofReal hF hj q)

/-- A root comparison counted in `e_0(q)`. -/
theorem le_localError_zero {q : Space n} {a : ι} (ha : a ∈ F.index 0)
    (hqa : dist q (F.center 0 a) < 3 * F.scale 0) {b : ι} (hb : b ∈ F.index 0)
    (hbq : dist (F.center 0 b) q ≤ 10 * F.scale 0) :
    ENNReal.ofReal (planeComparison (F.center 0 b).1 (F.scale 0) (F.plane 0 b) F.initialPlane) ≤
      localError F 0 q := by
  simp only [localError]
  exact le_iSup_of_le ⟨a, ha, hqa⟩ (le_iSup₂_of_le b hb (le_iSup_of_le hbq le_rfl))

/-- A same-level comparison at level `k` counted in `e_{k+1}(q)`. -/
theorem le_localError_succ_same {k : ℕ} {q : Space n} {a₀ : ι} (ha₀ : a₀ ∈ F.index (k + 1))
    (hq : dist q (F.center (k + 1) a₀) < 3 * F.scale (k + 1)) {a b : ι} (ha : a ∈ F.index k)
    (hb : b ∈ F.index k)
    (hab : dist (F.center k a) q ≤ 8 * F.scale k ∧ dist (F.center k b) q ≤ 8 * F.scale k) :
    ENNReal.ofReal (planeComparison (F.center k a).1 (F.scale k) (F.plane k a) (F.plane k b)) ≤
      localError F (k + 1) q := by
  simp only [localError]
  exact le_iSup_of_le ⟨a₀, ha₀, hq⟩ (le_max_of_le_left
    (le_iSup₂_of_le a ha (le_iSup₂_of_le b hb (le_iSup_of_le hab le_rfl))))

/-- An adjacent comparison `(k + 1, k)` counted in `e_{k+1}(q)`. -/
theorem le_localError_succ_adjacent {k : ℕ} {q : Space n} {a₀ : ι}
    (ha₀ : a₀ ∈ F.index (k + 1)) (hq : dist q (F.center (k + 1) a₀) < 3 * F.scale (k + 1))
    {a b : ι} (ha : a ∈ F.index (k + 1)) (hb : b ∈ F.index k)
    (hab : dist (F.center (k + 1) a) q ≤ 8 * F.scale k ∧ dist (F.center k b) q ≤ 8 * F.scale k) :
    ENNReal.ofReal
        (planeComparison (F.center k b).1 (F.scale k) (F.plane (k + 1) a) (F.plane k b)) ≤
      localError F (k + 1) q := by
  simp only [localError]
  exact le_iSup_of_le ⟨a₀, ha₀, hq⟩ (le_max_of_le_right
    (le_iSup₂_of_le a ha (le_iSup₂_of_le b hb (le_iSup_of_le hab le_rfl))))

/-- `A h⁻¹ e_j ≤ ε` for `j ≤ N`. -/
theorem scaledError_le_eps (hσ : 0 < σ) (hδ : 0 ≤ δ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ}
    (hj : j ≤ N) (q : Space n) :
    chartA n σ / ratio * (localError F j q).toReal ≤ chartEps n σ δ := by
  obtain ⟨-, -, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
  have hek := ENNReal.toReal_le_of_le_ofReal hδ (localError_le_ofReal hF hj q)
  have hAh : 0 ≤ chartA n σ / ratio := div_nonneg (by linarith) ratio_pos.le
  calc chartA n σ / ratio * (localError F j q).toReal ≤ chartA n σ / ratio * δ :=
        mul_le_mul_of_nonneg_left hek hAh
    _ = chartEps n σ δ := by unfold chartEps; ring

/-! ## The simultaneous induction -/

/-- The induction estimate at level `j` and parameter `(u, t)`, with the two maxima
replaced by uniform bounds: `X` for the tangent discrepancies, `Y` for the heights in units of
`r_j`, at all active indices, and `X + Y ≤ A h⁻¹ e_j(q_j)`. -/
def InductionBound (σ : ℝ) (P : InitialChart F) (j : ℕ) (u : Spatial m) (t : ℝ) : Prop :=
  ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧
    X + Y ≤ chartA n σ / ratio * (localError F j (pathPoint F P j u t)).toReal ∧
    (∀ a ∈ F.index j, IsActive F j a (stage F P j u t) t →
      ‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ ≤ X) ∧
    (∀ b ∈ F.index j, IsActive F j b (stage F P j u t) t →
      Metric.infDist (stage F P j u t) (F.plane j b).toSet ≤ Y * F.scale j)

/-- Rank and displacement from the level-`k` bound (first paragraph of the proof). -/
theorem step_of_inductionBound (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F) {k : ℕ} (hk : k ≤ N) (u : Spatial m)
    (t : ℝ) (hb : InductionBound σ P k u t) :
    (∀ v ∈ tangent F P k u t,
      ‖v‖ ^ 2 ≤ 2 * ‖fderiv ℝ (fun y => stageMap F k y t) (stage F P k u t) v‖ ^ 2) ∧
    ‖stage F P (k + 1) u t - stage F P k u t‖ ≤ chartEps n σ δ * F.scale k := by
  obtain ⟨X, Y, hX, hY, hXY, hXa, hYb⟩ := hb
  have hXYε := hXY.trans (scaledError_le_eps hσ hδ hF hk _)
  obtain ⟨h0, -, -, -, -, -, -, -⟩ := chartConsts_bounds (n := n) hσ
  have hr := scale_pos F k
  have he : ∀ a ∈ F.index k, CoherentProjection.Active (weight F k) a (stage F P k u t) t →
      ‖(F.plane k a).projection (stage F P k u t) - stage F P k u t‖ ≤ Y * F.scale k := by
    intro a ha hact
    rw [norm_sub_rev, ProjectionReset.residual_eq_infDist]
    exact hYb a ha hact
  obtain ⟨hd, -, -, hq⟩ := CoherentProjection.one_step (F.index k) (F.plane k) (weight F k)
    (stage F P k u t) t (chartC₀ n σ) Y (F.scale k) X hr (by linarith) hY hX
    (fun a _ => differentiableAt_weight_spatial F k a _ t)
    (fun a _ => differentiableAt_weight_time F k a _ t)
    (weightBounds_level hσ hF hk _ t) he (tangent F P k u t) hXa
  refine ⟨fun v hv => ?_, hd.trans (mul_le_mul_of_nonneg_right (by linarith) hr.le)⟩
  have h : |‖fderiv ℝ (fun y => stageMap F k y t) (stage F P k u t) v‖ ^ 2 - ‖v‖ ^ 2| ≤
      10 * (1 + chartC₀ n σ) ^ 2 * (X ^ 2 + Y ^ 2) * ‖v‖ ^ 2 := hq v hv
  have hsq : X ^ 2 + Y ^ 2 ≤ chartEps n σ δ ^ 2 := by
    nlinarith [mul_nonneg hX hY, mul_self_le_mul_self (add_nonneg hX hY) hXYε]
  have hC : 10 * (1 + chartC₀ n σ) ^ 2 * (X ^ 2 + Y ^ 2) ≤ 1 / 2 := by
    have hq2 := hsmall.quadratic
    unfold chartC₁ at hq2
    calc 10 * (1 + chartC₀ n σ) ^ 2 * (X ^ 2 + Y ^ 2)
        ≤ 10 * (1 + chartC₀ n σ) ^ 2 * chartEps n σ δ ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 1 / 2 := hq2
  have hC' := mul_le_mul_of_nonneg_right hC (sq_nonneg ‖v‖)
  have h1 := (abs_le.mp h).1
  linarith

/-- Level `0`: the root comparisons give `X = e_0`, `Y = 3 e_0`. -/
theorem inductionBound_zero (hσ : 0 < σ) (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F)
    (u : Spatial m) (t : ℝ) : InductionBound σ P 0 u t := by
  obtain ⟨-, -, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
  have hr := scale_pos F 0
  have hfin := localError_ne_top hF (Nat.zero_le N) (pathPoint F P 0 u t)
  set e := (localError F 0 (pathPoint F P 0 u t)).toReal with he_def
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have hroot : ∀ a ∈ F.index 0, IsActive F 0 a (stage F P 0 u t) t →
      ‖stage F P 0 u t - (F.center 0 a).1‖ < 3 * F.scale 0 ∧
        planeComparison (F.center 0 a).1 (F.scale 0) (F.plane 0 a) F.initialPlane ≤ e := by
    intro a ha hact
    have h3 := dist_lt_of_isActive hσ hF (Nat.zero_le N) hact
    refine ⟨(norm_fst_sub_le_dist (point (stage F P 0 u t) t) (F.center 0 a)).trans_lt h3, ?_⟩
    have h := le_localError_zero ha h3 ha (by rw [dist_comm]; exact h3.le.trans (by linarith))
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h
  refine ⟨e, 3 * e, he0, mul_nonneg (by norm_num) he0, ?_, ?_, ?_⟩
  · have hAh : 4 ≤ chartA n σ / ratio := by
      rw [le_div_iff₀ ratio_pos]; unfold ratio; linarith
    have := mul_le_mul_of_nonneg_right hAh he0
    linarith
  · intro a ha hact
    rw [starProjection_congr (tangent_zero P u t), norm_sub_rev]
    exact (norm_linearProjection_sub_le_planeComparison hr _ _).trans (hroot a ha hact).2
  · intro b hb hact
    obtain ⟨h3, hc⟩ := hroot b hb hact
    calc Metric.infDist (stage F P 0 u t) (F.plane 0 b).toSet
        ≤ Metric.infDist (stage F P 0 u t) F.initialPlane.toSet +
            ‖(F.plane 0 b).projection (stage F P 0 u t) -
              F.initialPlane.projection (stage F P 0 u t)‖ :=
          AffineSpatialPlane.infDist_le_infDist_add _ _ _
      _ ≤ 0 + 3 * F.scale 0 * e :=
          add_le_add (Metric.infDist_zero_of_mem (stage_zero_mem P u t)).le
            (norm_projection_sub_le_of_planeComparison hr (by norm_num) h3.le hc)
      _ = 3 * e * F.scale 0 := by ring

/-- The induction step `k → k + 1` (second paragraph of the proof). -/
theorem inductionBound_succ (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F) {k : ℕ} (hk : k + 1 ≤ N)
    (u : Spatial m) (t : ℝ) (hb : InductionBound σ P k u t) :
    InductionBound σ P (k + 1) u t := by
  obtain ⟨h0, -, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
  have hε0 := chartEps_nonneg (n := n) hσ hδ
  have hε1 : chartEps n σ δ ≤ 1 / 100 := hsmall.eps_le
  have hr := scale_pos F k
  have hrs := scale_succ F k
  have hAh : 0 ≤ chartA n σ / ratio := div_nonneg (by linarith) ratio_pos.le
  have hfin := localError_ne_top hF hk (pathPoint F P (k + 1) u t)
  have heδ : (localError F (k + 1) (pathPoint F P (k + 1) u t)).toReal ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ (localError_le_ofReal hF hk _)
  set e := (localError F (k + 1) (pathPoint F P (k + 1) u t)).toReal with he_def
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  by_cases hact : ∃ a₀ ∈ F.index (k + 1), IsActive F (k + 1) a₀ (stage F P (k + 1) u t) t
  swap
  · simp only [not_exists, not_and] at hact
    exact ⟨0, 0, le_rfl, le_rfl, by rw [add_zero]; exact mul_nonneg hAh he0,
      fun a ha h => absurd h (hact a ha), fun a ha h => absurd h (hact a ha)⟩
  obtain ⟨a₀, ha₀, hact₀⟩ := hact
  -- the previous level
  have hdisp := (step_of_inductionBound hσ hδ hsmall hF P (by omega : k ≤ N) u t hb).2
  obtain ⟨X, Y, hX, hY, hXY, hXa, -⟩ := hb
  have hXYε := hXY.trans (scaledError_le_eps hσ hδ hF (by omega : k ≤ N) _)
  set xm := stage F P k u t with hxm
  set x := stage F P (k + 1) u t with hx
  have hdpt : dist (point xm t) (point x t) ≤ chartEps n σ δ * F.scale k := by
    rw [dist_point_point_same, norm_sub_rev]
    exact hdisp
  have hεr : chartEps n σ δ * F.scale k ≤ 1 / 100 * F.scale k :=
    mul_le_mul_of_nonneg_right hε1 hr.le
  -- the active fine center and its parent
  have hd₀ : dist (point x t) (F.center (k + 1) a₀) < 3 * F.scale (k + 1) :=
    dist_lt_of_isActive hσ hF hk hact₀
  have hpm : F.parent (k + 1) a₀ ∈ F.index k := hF.parent_mem k hk a₀ ha₀
  have hpd : dist (F.center (k + 1) a₀) (F.center k (F.parent (k + 1) a₀)) ≤ F.scale k :=
    hF.parent_dist k hk a₀ ha₀
  have hxmb : dist (point xm t) (F.center k (F.parent (k + 1) a₀)) < 2 * F.scale k := by
    calc dist (point xm t) (F.center k (F.parent (k + 1) a₀))
        ≤ dist (point xm t) (point x t) + dist (point x t) (F.center (k + 1) a₀) +
            dist (F.center (k + 1) a₀) (F.center k (F.parent (k + 1) a₀)) :=
          dist_triangle4 _ _ _ _
      _ < chartEps n σ δ * F.scale k + 3 * F.scale (k + 1) + F.scale k :=
          add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt hdpt hd₀) hpd
      _ ≤ 2 * F.scale k := by rw [hrs]; unfold ratio; linarith
  -- full weight near the predecessor and a reference index `c₀`
  have hfull := eventually_sum_weight_eq_one hσ hF (by omega : k ≤ N) hpm hxmb
  obtain ⟨c₀, hc₀, hθc₀⟩ := exists_weight_ne_zero hfull.self_of_nhds
  have hactc₀ : IsActive F k c₀ xm t := Or.inl hθc₀
  have hnear : ∀ c ∈ F.index k, IsActive F k c xm t →
      ‖xm - (F.center k c).1‖ < 3 * F.scale k ∧
        dist (F.center k c) (pathPoint F P (k + 1) u t) ≤ 8 * F.scale k := by
    intro c _ hactc
    have h3 := dist_lt_of_isActive hσ hF (by omega : k ≤ N) hactc
    refine ⟨(norm_fst_sub_le_dist (point xm t) (F.center k c)).trans_lt h3, ?_⟩
    calc dist (F.center k c) (point x t)
        ≤ dist (F.center k c) (point xm t) + dist (point xm t) (point x t) :=
          dist_triangle _ _ _
      _ ≤ 3 * F.scale k + chartEps n σ δ * F.scale k :=
          add_le_add (by rw [dist_comm]; exact h3.le) hdpt
      _ ≤ 8 * F.scale k := by linarith
  have hq_fine : dist (pathPoint F P (k + 1) u t) (F.center (k + 1) a₀) <
      3 * F.scale (k + 1) := hd₀
  have hsame : ∀ c ∈ F.index k, IsActive F k c xm t →
      planeComparison (F.center k c).1 (F.scale k) (F.plane k c) (F.plane k c₀) ≤ e := by
    intro c hc hactc
    have h := le_localError_succ_same ha₀ hq_fine hc hc₀
      ⟨(hnear c hc hactc).2, (hnear c₀ hc₀ hactc₀).2⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h
  -- the reset at the predecessor, with reference plane `L_{k,c₀}` and `B = 3`
  have hP := partition_level hσ hF (by omega : k ≤ N)
  have hT : ‖(tangent F P k u t).starProjection - (F.plane k c₀).linearProjection‖ ≤ 1 / 10 :=
    (hXa c₀ hc₀ hactc₀).trans (by linarith)
  have hsm : (1 + 3 * chartC₀ n σ) * e ≤ 1 / 10 := by
    have hreset := hsmall.reset
    unfold chartCr at hreset
    have h1 : (1 + 3 * chartC₀ n σ) * e ≤ (1 + 3 * chartC₀ n σ) * δ :=
      mul_le_mul_of_nonneg_left heδ (by linarith)
    have h2 : (1 + 3 * chartC₀ n σ) * δ ≤ 8 * (1 + 5 * chartC₀ n σ) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ
    linarith
  obtain ⟨hR1, -, -, -, -, hR6⟩ := ProjectionReset.reset (F.index k) (F.plane k) (weight F k)
    xm t 3 (chartC₀ n σ) (F.scale k) e hr (by norm_num) (by linarith) he0 (F.plane k c₀)
    (fun a _ => hP.nonneg a (xm, t)) (fun a _ => differentiableAt_weight_spatial F k a xm t)
    hfull (hP.first xm t)
    (fun c hc hactc => (norm_linearProjection_sub_le_planeComparison hr _ _).trans
      (hsame c hc hactc))
    (fun c hc hactc => norm_projection_sub_le_of_planeComparison hr (by norm_num)
      (hnear c hc hactc).1.le (hsame c hc hactc))
    (tangent F P k u t) hT hsm
  have hT1 : ‖(tangent F P (k + 1) u t).starProjection - (F.plane k c₀).linearProjection‖ ≤
      8 * (1 + 3 * chartC₀ n σ) * e := by
    rw [starProjection_congr (tangent_succ P k u t)]
    exact hR6
  have hH1 : Metric.infDist x (F.plane k c₀).toSet ≤ 3 * F.scale k * e := hR1
  -- the adjacent comparisons with every active fine index
  have hadj : ∀ a ∈ F.index (k + 1), IsActive F (k + 1) a x t →
      planeComparison (F.center k c₀).1 (F.scale k) (F.plane (k + 1) a) (F.plane k c₀) ≤ e := by
    intro a ha hacta
    have h3 := dist_lt_of_isActive hσ hF hk hacta
    have h := le_localError_succ_adjacent ha₀ hq_fine ha hc₀
      ⟨by rw [dist_comm]; exact h3.le.trans (by rw [hrs]; unfold ratio; linarith),
        (hnear c₀ hc₀ hactc₀).2⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h
  have hxc₀ : ‖x - (F.center k c₀).1‖ ≤ 4 * F.scale k := by
    have h1 : ‖x - xm‖ ≤ chartEps n σ δ * F.scale k := hdisp
    have h2 := (hnear c₀ hc₀ hactc₀).1
    calc ‖x - (F.center k c₀).1‖ ≤ ‖x - xm‖ + ‖xm - (F.center k c₀).1‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 4 * F.scale k := by linarith
  refine ⟨(8 * (1 + 3 * chartC₀ n σ) + 1) * e, 70 * e, mul_nonneg (by linarith) he0,
    mul_nonneg (by norm_num) he0, ?_, ?_, ?_⟩
  · have hc : 8 * (1 + 3 * chartC₀ n σ) + 1 + 70 ≤ chartA n σ / ratio := by
      rw [le_div_iff₀ ratio_pos]; unfold chartA chartCr ratio; linarith
    have := mul_le_mul_of_nonneg_right hc he0
    linarith
  · intro a ha hacta
    calc ‖(tangent F P (k + 1) u t).starProjection - (F.plane (k + 1) a).linearProjection‖
        ≤ ‖(tangent F P (k + 1) u t).starProjection - (F.plane k c₀).linearProjection‖ +
            ‖(F.plane k c₀).linearProjection - (F.plane (k + 1) a).linearProjection‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 8 * (1 + 3 * chartC₀ n σ) * e + e := by
          refine add_le_add hT1 ?_
          rw [norm_sub_rev]
          exact (norm_linearProjection_sub_le_planeComparison hr _ _).trans (hadj a ha hacta)
      _ = (8 * (1 + 3 * chartC₀ n σ) + 1) * e := by ring
  · intro a ha hacta
    have hanch : ‖(F.plane (k + 1) a).projection x - (F.plane k c₀).projection x‖ ≤
        4 * F.scale k * e :=
      norm_projection_sub_le_of_planeComparison hr (by norm_num) hxc₀ (hadj a ha hacta)
    calc Metric.infDist x (F.plane (k + 1) a).toSet
        ≤ Metric.infDist x (F.plane k c₀).toSet +
            ‖(F.plane (k + 1) a).projection x - (F.plane k c₀).projection x‖ :=
          AffineSpatialPlane.infDist_le_infDist_add _ _ _
      _ ≤ 3 * F.scale k * e + 4 * F.scale k * e := add_le_add hH1 hanch
      _ = 70 * e * F.scale (k + 1) := by rw [hrs]; unfold ratio; ring

/-- The level bound holds at every level `j ≤ N` and every parameter. -/
theorem inductionBound_of_le (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F) :
    ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), InductionBound σ P j u t := by
  intro j hj
  induction j with
  | zero => exact fun u t => inductionBound_zero hσ hF P u t
  | succ k ih =>
    exact fun u t => inductionBound_succ hσ hδ hsmall hF P hj u t (ih (by omega) u t)

/-- **Induction estimates.** Rank of every `D_u F_j`, the cross-index tangent and height
estimate `α_j + H_j ≤ A h⁻¹ e_j(q_j)`, and the displacement bound `|F_{j+1} - F_j| ≤ ε r_j`. -/
theorem induction_estimates_proof {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hF : F.IsCoherentUpTo σ δ N)
    (P : InitialChart F) :
    (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
      Function.Injective (fderiv ℝ (fun v => stage F P j v t) u)) ∧
    (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), ∀ a ∈ F.index j, ∀ b ∈ F.index j,
      IsActive F j a (stage F P j u t) t → IsActive F j b (stage F P j u t) t →
        ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
            (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) ≤
          ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t)) ∧
    (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j) := by
  have hbound := inductionBound_of_le hσ hδ hsmall hF P
  refine ⟨?_, ?_, fun j hj u t =>
    (step_of_inductionBound hσ hδ hsmall hF P hj u t (hbound j hj u t)).2⟩
  · intro j hj
    induction j with
    | zero =>
      intro u t
      rw [fderiv_stage_zero]
      exact P.isometry.injective
    | succ k ih =>
      intro u t
      have hinj := ih (by omega) u t
      have hq := (step_of_inductionBound hσ hδ hsmall hF P (by omega) u t
        (hbound k (by omega) u t)).1
      rw [fderiv_stage_succ]
      set S := fderiv ℝ (fun y => stageMap F k y t) (stage F P k u t)
      set D := fderiv ℝ (fun v => stage F P k v t) u
      intro v w hvw
      have hvw' : S (D v) = S (D w) := hvw
      have hz : S (D (v - w)) = 0 := by rw [map_sub, map_sub, hvw', sub_self]
      have h2 := hq (D (v - w)) (LinearMap.mem_range_self _ _)
      rw [hz, norm_zero] at h2
      have h3 : ‖D (v - w)‖ = 0 := by nlinarith [norm_nonneg (D (v - w))]
      have h4 : D (v - w) = D 0 := by rw [norm_eq_zero.mp h3, map_zero]
      exact sub_eq_zero.mp (hinj h4)
  · intro j hj u t a ha b hb hacta hactb
    obtain ⟨-, -, -, -, -, -, -, hA⟩ := chartConsts_bounds (n := n) hσ
    obtain ⟨X, Y, -, -, hXY, hXa, hYb⟩ := hbound j hj u t
    have hfin := localError_ne_top hF hj (pathPoint F P j u t)
    have hr := scale_pos F j
    have hAh : 0 ≤ chartA n σ / ratio := div_nonneg (by linarith) ratio_pos.le
    have h1 : (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet ≤ Y := by
      rw [inv_mul_le_iff₀ hr]
      linarith [hYb b hb hactb]
    calc ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
            (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet)
        ≤ ENNReal.ofReal (chartA n σ / ratio * (localError F j (pathPoint F P j u t)).toReal) :=
          ENNReal.ofReal_le_ofReal (by linarith [hXa a ha hacta])
      _ = ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t) := by
          rw [ENNReal.ofReal_mul hAh, ENNReal.ofReal_toReal hfin]

/-! ## The parent patch -/

/-- `|T v| ≥ 0.98 |v|` between spaces of equal finite dimension gives a continuous linear
equivalence with `‖T⁻¹‖ ≤ 50/49` (a small lemma for the parent patch). -/
theorem exists_equiv_of_norm_lowerBound {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] (hdim : Module.finrank ℝ E = Module.finrank ℝ G)
    (T : E →L[ℝ] G) (hT : ∀ v, 49 / 50 * ‖v‖ ≤ ‖T v‖) :
    ∃ A : E ≃L[ℝ] G, (A : E →L[ℝ] G) = T ∧ ‖(A.symm : G →L[ℝ] E)‖ ≤ 50 / 49 := by
  have hinj : Function.Injective (T : E →ₗ[ℝ] G) := by
    intro x y hxy
    have h := hT (x - y)
    have h0 : T (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    rw [h0, norm_zero] at h
    have h1 : ‖x - y‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h1)
  have hsurj : Function.Surjective (T : E →ₗ[ℝ] G) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let A : E ≃L[ℝ] G := (LinearEquiv.ofBijective (T : E →ₗ[ℝ] G) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨A, ?_, ?_⟩
  · ext v
    rfl
  · refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun y => ?_
    have h := hT (A.symm y)
    have hy : T (A.symm y) = y := A.apply_symm_apply y
    rw [hy] at h
    show ‖A.symm y‖ ≤ 50 / 49 * ‖y‖
    linarith

/-- The reset inside the parent patch (first step of the proof of the parent patch):
if `(F_i(u,t), t)` lies in `P(z_{i,a}, 2 r_i)`, then `F_{i+1}(u,t)` has height at most
`3 δ r_i` above `L_{i,a}` and tangent projection difference at most `C_r δ`. -/
theorem reset_of_mem_parentBall (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F) {i : ℕ} (hi : i ≤ N) {a : ι}
    (ha : a ∈ F.index i) {u : Spatial m} {t : ℝ}
    (hball : dist (point (stage F P i u t) t) (F.center i a) < 2 * F.scale i) :
    Metric.infDist (stage F P (i + 1) u t) (F.plane i a).toSet ≤ 3 * δ * F.scale i ∧
      ‖(tangent F P (i + 1) u t).starProjection - (F.plane i a).linearProjection‖ ≤
        chartCr n σ * δ := by
  obtain ⟨h0, -, -, -, -, -, -, -⟩ := chartConsts_bounds (n := n) hσ
  have hε1 : chartEps n σ δ ≤ 1 / 100 := hsmall.eps_le
  have hr := scale_pos F i
  have hreset := hsmall.reset
  have hδ1 : δ ≤ 1 / 480 := by
    unfold chartCr at hreset
    have : 48 * δ ≤ 8 * (1 + 5 * chartC₀ n σ) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ
    linarith
  set x := stage F P i u t with hx
  have hxa : ‖x - (F.center i a).1‖ ≤ 3 * F.scale i :=
    ((norm_fst_sub_le_dist (point x t) (F.center i a)).trans hball.le).trans (by linarith)
  have hP := partition_level hσ hF hi
  have hfull := eventually_sum_weight_eq_one hσ hF hi ha hball
  -- every active index is a same-level neighbour of `a`
  have hsame : ∀ b ∈ F.index i, IsActive F i b x t →
      planeComparison (F.center i a).1 (F.scale i) (F.plane i a) (F.plane i b) ≤ δ := by
    intro b hb hactb
    have h3 := dist_lt_of_isActive hσ hF hi hactb
    refine hF.same i hi a ha b hb ?_
    calc dist (F.center i a) (F.center i b) ≤ dist (F.center i a) (point x t) +
          dist (point x t) (F.center i b) := dist_triangle _ _ _
      _ ≤ 2 * F.scale i + 3 * F.scale i :=
          add_le_add (by rw [dist_comm]; exact hball.le) h3.le
      _ ≤ 20 * F.scale i := by linarith
  -- the incoming tangent, through an index of positive weight
  obtain ⟨c, hc, hθc⟩ := exists_weight_ne_zero hfull.self_of_nhds
  have hT : ‖(tangent F P i u t).starProjection - (F.plane i a).linearProjection‖ ≤ 1 / 10 := by
    obtain ⟨X, Y, -, hY, hXY, hXa, -⟩ := inductionBound_of_le hσ hδ hsmall hF P i hi u t
    have hXYε := hXY.trans (scaledError_le_eps hσ hδ hF hi _)
    have h1 := hXa c hc (Or.inl hθc)
    have h2 : ‖(F.plane i c).linearProjection - (F.plane i a).linearProjection‖ ≤ δ := by
      rw [norm_sub_rev]
      exact (norm_linearProjection_sub_le_planeComparison hr _ _).trans
        (hsame c hc (Or.inl hθc))
    calc ‖(tangent F P i u t).starProjection - (F.plane i a).linearProjection‖
        ≤ ‖(tangent F P i u t).starProjection - (F.plane i c).linearProjection‖ +
            ‖(F.plane i c).linearProjection - (F.plane i a).linearProjection‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 1 / 10 := by linarith
  have hsm : (1 + 3 * chartC₀ n σ) * δ ≤ 1 / 10 := by
    unfold chartCr at hreset
    have h2 : (1 + 3 * chartC₀ n σ) * δ ≤ 8 * (1 + 5 * chartC₀ n σ) * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ
    linarith
  obtain ⟨hR1, -, -, -, -, hR6⟩ := ProjectionReset.reset (F.index i) (F.plane i) (weight F i)
    x t 3 (chartC₀ n σ) (F.scale i) δ hr (by norm_num) (by linarith) hδ (F.plane i a)
    (fun b _ => hP.nonneg b (x, t)) (fun b _ => differentiableAt_weight_spatial F i b x t)
    hfull (hP.first x t)
    (fun b hb hactb => by
      rw [norm_sub_rev]
      exact (norm_linearProjection_sub_le_planeComparison hr _ _).trans (hsame b hb hactb))
    (fun b hb hactb => by
      rw [norm_sub_rev]
      exact norm_projection_sub_le_of_planeComparison hr (by norm_num) hxa (hsame b hb hactb))
    (tangent F P i u t) hT hsm
  refine ⟨?_, ?_⟩
  · have h : Metric.infDist (stage F P (i + 1) u t) (F.plane i a).toSet ≤
        3 * F.scale i * δ := hR1
    linarith
  · rw [starProjection_congr (tangent_succ P i u t)]
    refine hR6.trans ?_
    unfold chartCr
    exact mul_le_mul_of_nonneg_right (by linarith) hδ

/-! ### Coordinates on a plane direction and the coordinate inverse -/

/-- Coordinates on the direction of a rank-`m` plane: a map `Q : ℝⁿ → ℝᵐ` with
`‖Q w‖ = ‖P_L w‖` (an orthonormal basis of the direction after the orthogonal projection). -/
theorem exists_directionCoordinates (L : AffineSpatialPlane n m) :
    ∃ Q : Spatial n →L[ℝ] Spatial m, ∀ w, ‖Q w‖ = ‖L.linearProjection w‖ := by
  let b := (stdOrthonormalBasis ℝ L.direction).reindex (finCongr L.rank_eq)
  refine ⟨b.repr.toLinearIsometry.toContinuousLinearMap.comp
    L.direction.orthogonalProjectionOnto, fun w => ?_⟩
  show ‖b.repr (L.direction.orthogonalProjectionOnto w)‖ =
    ‖(L.direction.orthogonalProjectionOnto w : Spatial n)‖
  rw [LinearIsometryEquiv.norm_map]
  rfl

theorem linearProjection_eq_of_coordinates {L : AffineSpatialPlane n m}
    {Q : Spatial n →L[ℝ] Spatial m} (hQ : ∀ w, ‖Q w‖ = ‖L.linearProjection w‖)
    {y z : Spatial n} (h : Q y = Q z) : L.linearProjection y = L.linearProjection z := by
  have h0 : ‖L.linearProjection (y - z)‖ = 0 := by
    rw [← hQ, map_sub, h, sub_self, norm_zero]
  rw [map_sub] at h0
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

theorem norm_coordinates_le {L : AffineSpatialPlane n m} {Q : Spatial n →L[ℝ] Spatial m}
    (hQ : ∀ w, ‖Q w‖ = ‖L.linearProjection w‖) : ‖Q‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [hQ, one_mul]
    exact L.direction.norm_starProjection_apply_le w

/-- The numerical margin `0.99 √0.99 > 0.98`, in squared form: if `|w|² = |Pw|² + |w - Pw|²`,
`|w - Pw| ≤ |w|/10` and `|w| ≥ 0.99 |v|`, then `|Pw| ≥ 0.98 |v|`. -/
theorem lowerBound_of_pythagoras {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hpyth : c * c = a * a + b * b) (hbc : b ≤ 1 / 10 * c) (hcd : 99 / 100 * d ≤ c) :
    49 / 50 * d ≤ a := by
  have hc : 0 ≤ c := le_trans (mul_nonneg (by norm_num) hd) hcd
  have h1 : b * b ≤ 1 / 10 * c * (1 / 10 * c) := mul_le_mul hbc hbc hb (by positivity)
  have h2 : 99 / 100 * d * (99 / 100 * d) ≤ c * c := mul_le_mul hcd hcd (by positivity) hc
  have h3 : 49 / 50 * d * (49 / 50 * d) ≤ a * a := by nlinarith [mul_self_nonneg d]
  nlinarith

/-- The mean value bound from a uniform operator bound on the derivative. -/
theorem norm_sub_le_of_fderiv_le {G : Spatial m → Spatial n}
    (hG : ∀ u, DifferentiableAt ℝ G u) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u v, ‖fderiv ℝ G u v‖ ≤ C * ‖v‖) (u u₀ : Spatial m) :
    ‖G u - G u₀‖ ≤ C * ‖u - u₀‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (fun w _ => hG w)
    (fun w _ => ContinuousLinearMap.opNorm_le_bound _ hC0 (hC w)) convex_univ
    (Set.mem_univ u₀) (Set.mem_univ u)

/-- Integrating the second derivative bound along segments. -/
theorem norm_fderiv_sub_le {G : Spatial m → Spatial n} (hG : ContDiff ℝ ∞ G) {C : ℝ}
    (hC : ∀ u, ‖fderiv ℝ (fderiv ℝ G) u‖ ≤ C) (u u₀ : Spatial m) :
    ‖fderiv ℝ G u - fderiv ℝ G u₀‖ ≤ C * ‖u - u₀‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => ((contDiff_infty_iff_fderiv.mp hG).2.differentiable (by simp)) w)
    (fun w _ => hC w) convex_univ (Set.mem_univ u₀) (Set.mem_univ u)

/-- The coordinate step of the parent patch, for a general map `G`: if
`|DG(u₀) v| ≥ 0.99 |v|`, the range of `DG(u₀)` is within `1/10` of the direction of `K`, and
`‖DG(u) - DG(u₀)‖ ≤ 1/100` on `B̄(u₀, 1.2 r)`, then the nearest-point projection to `K` of `G`
on that ball attains every point of `K` within `1.05 r` of `π_K G(u₀)`. In coordinates `Q` on
the direction this is the quantitative inverse function theorem for `H = Q ∘ G`, with `‖DH(u₀)⁻¹‖ ≤ 50/49`. -/
theorem projection_surjOn_of_derivative {G : Spatial m → Spatial n}
    (hG : ∀ u, DifferentiableAt ℝ G u) (K : AffineSpatialPlane n m) {u₀ : Spatial m} {r : ℝ}
    (hspeed : ∀ v, 99 / 100 * ‖v‖ ≤ ‖fderiv ℝ G u₀ v‖)
    (htan : ‖(LinearMap.range (fderiv ℝ G u₀ : Spatial m →ₗ[ℝ] Spatial n)).starProjection -
      K.linearProjection‖ ≤ 1 / 10)
    (hvar : ∀ u ∈ Metric.closedBall u₀ (6 / 5 * r),
      ‖fderiv ℝ G u - fderiv ℝ G u₀‖ ≤ 1 / 100) :
    ∀ y ∈ K.toSet, ‖y - K.projection (G u₀)‖ ≤ 21 / 20 * r →
      ∃ u ∈ Metric.closedBall u₀ (6 / 5 * r), K.projection (G u) = y := by
  intro y hy hyd
  obtain ⟨Q, hQ⟩ := exists_directionCoordinates K
  have hQ1 := norm_coordinates_le hQ
  let A₀ : Spatial m →L[ℝ] Spatial m := Q.comp (fderiv ℝ G u₀)
  have hlow : ∀ v, 49 / 50 * ‖v‖ ≤ ‖A₀ v‖ := by
    intro v
    set w := fderiv ℝ G u₀ v with hw
    have hwT : w ∈ LinearMap.range (fderiv ℝ G u₀ : Spatial m →ₗ[ℝ] Spatial n) :=
      LinearMap.mem_range_self _ v
    have hres : ‖w - K.linearProjection w‖ ≤ 1 / 10 * ‖w‖ := by
      have h1 := ((LinearMap.range (fderiv ℝ G u₀ : Spatial m →ₗ[ℝ] Spatial n)).starProjection -
        K.linearProjection).le_opNorm w
      have h2 : ((LinearMap.range (fderiv ℝ G u₀ : Spatial m →ₗ[ℝ] Spatial n)).starProjection -
          K.linearProjection) w = w - K.linearProjection w := by
        show (LinearMap.range (fderiv ℝ G u₀ : Spatial m →ₗ[ℝ] Spatial n)).starProjection w -
          K.linearProjection w = w - K.linearProjection w
        rw [Submodule.starProjection_eq_self_iff.mpr hwT]
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right htan (norm_nonneg _))
    have ho : ⟪K.linearProjection w, w - K.linearProjection w⟫ = 0 :=
      K.direction.sub_starProjection_mem_orthogonal w _ (K.direction.starProjection_apply_mem w)
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
    have hsum : K.linearProjection w + (w - K.linearProjection w) = w := by abel
    rw [hsum] at hpyth
    have hA₀v : ‖A₀ v‖ = ‖K.linearProjection w‖ := hQ w
    rw [hA₀v]
    exact lowerBound_of_pythagoras (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hpyth hres
      (hspeed v)
  obtain ⟨A, hA, hAinv⟩ := exists_equiv_of_norm_lowerBound rfl A₀ hlow
  have hHd : ∀ u, HasFDerivAt (fun u => Q (G u)) (Q.comp (fderiv ℝ G u)) u :=
    fun u => Q.hasFDerivAt.comp u (hG u).hasFDerivAt
  have hnear : ∀ u ∈ Metric.closedBall u₀ (6 / 5 * r),
      ‖fderiv ℝ (fun u => Q (G u)) u - (A : Spatial m →L[ℝ] Spatial m)‖ ≤ 1 / 100 := by
    intro u hu
    rw [hA, (hHd u).fderiv]
    show ‖Q.comp (fderiv ℝ G u) - Q.comp (fderiv ℝ G u₀)‖ ≤ 1 / 100
    rw [← ContinuousLinearMap.comp_sub]
    calc ‖Q.comp (fderiv ℝ G u - fderiv ℝ G u₀)‖
        ≤ ‖Q‖ * ‖fderiv ℝ G u - fderiv ℝ G u₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 / 100) := mul_le_mul hQ1 (hvar u hu) (norm_nonneg _) zero_le_one
      _ = 1 / 100 := one_mul _
  have hyK : K.projection y = y := K.projection_eq_self_of_mem hy
  have hyH : ‖Q y - Q (G u₀)‖ ≤ 21 / 20 * r := by
    rw [← map_sub, hQ]
    have h1 : K.linearProjection (y - G u₀) = y - K.projection (G u₀) := by
      conv_rhs => rw [← hyK]
      simp only [AffineSpatialPlane.projection, map_sub]
      abel
    rw [h1]
    exact hyd
  obtain ⟨u, hu, hHu⟩ := QuantitativeInverse.exists_mem_closedBall_eq (fun u => Q (G u)) u₀ r A
    hAinv (fun u _ => (hHd u).differentiableAt) hnear (Q y) hyH
  refine ⟨u, hu, ?_⟩
  have h2 : K.linearProjection (G u) = K.linearProjection y :=
    linearProjection_eq_of_coordinates hQ hHu
  calc K.projection (G u) = K.anchor + K.linearProjection (G u) := rfl
    _ = K.anchor + K.linearProjection y := by rw [h2]
    _ = K.projection y := rfl
    _ = y := hyK

/-- The previous image of the parameter ball lies in `P(z_{i,a}, 2 r_i)`: its spatial
distance from `x_{i,a}` is at most `(0.01 + 1.01 · 1.2 + 0.01) r_i = 1.232 r_i` and its time
separation at most `(1.5 r_i)²`. -/
theorem dist_lt_of_mem_parentPatch (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F) {i : ℕ} (hi : i ≤ N) {a : ι} {t : ℝ}
    (ht : |t - (F.center i a).2.val| ≤ (3 / 2 * F.scale i) ^ 2) {u₀ : Spatial m} {η' : ℝ}
    (hη' : η' ≤ 1 / 100)
    (hu₀ : ‖stage F P (i + 1) u₀ t - (F.center i a).1‖ ≤ η' * F.scale i)
    (hLip : ∀ u, ‖stage F P (i + 1) u t - stage F P (i + 1) u₀ t‖ ≤ 101 / 100 * ‖u - u₀‖)
    {u : Spatial m} (hu : u ∈ Metric.closedBall u₀ (6 / 5 * F.scale i)) :
    dist (point (stage F P i u t) t) (F.center i a) < 2 * F.scale i := by
  have hr := scale_pos F i
  have hε1 : chartEps n σ δ ≤ 1 / 100 := hsmall.eps_le
  have hu' : ‖u - u₀‖ ≤ 6 / 5 * F.scale i := by rw [← dist_eq_norm]; exact hu
  have h1 : ‖stage F P (i + 1) u t - stage F P i u t‖ ≤ chartEps n σ δ * F.scale i :=
    (induction_estimates_proof hσ hδ hsmall hF P).2.2 i hi u t
  have h2 := hLip u
  have hη : η' * F.scale i ≤ 1 / 100 * F.scale i := mul_le_mul_of_nonneg_right hη' hr.le
  have hεr : chartEps n σ δ * F.scale i ≤ 1 / 100 * F.scale i :=
    mul_le_mul_of_nonneg_right hε1 hr.le
  have hspat : ‖stage F P i u t - (F.center i a).1‖ < 2 * F.scale i := by
    rw [norm_sub_rev] at h1
    have h4 := norm_sub_le_norm_sub_add_norm_sub (stage F P i u t) (stage F P (i + 1) u t)
      (F.center i a).1
    have h5 := norm_sub_le_norm_sub_add_norm_sub (stage F P (i + 1) u t)
      (stage F P (i + 1) u₀ t) (F.center i a).1
    linarith
  have htime : Real.sqrt |t - (F.center i a).2.val| < 2 * F.scale i := by
    calc Real.sqrt |t - (F.center i a).2.val| ≤ Real.sqrt ((3 / 2 * F.scale i) ^ 2) :=
          Real.sqrt_le_sqrt ht
      _ = 3 / 2 * F.scale i := Real.sqrt_sq (by linarith)
      _ < 2 * F.scale i := by linarith
  calc dist (point (stage F P i u t) t) (F.center i a)
      = dist (point (stage F P i u t) t) (point (F.center i a).1 (F.center i a).2.val) := rfl
    _ = max ‖stage F P i u t - (F.center i a).1‖ (Real.sqrt |t - (F.center i a).2.val|) :=
        dist_point _ _ _ _
    _ < 2 * F.scale i := max_lt hspat htime

/-- **Parent patch.** Proved from the recurrence estimates, which enter as the first
hypothesis `hrec`; only its speed and curvature clauses are used.
The hypotheses `1 ≤ m < n` of the statement are not needed by the argument (binders `_hm`,
`_hmn`; binder names are not part of the type). -/
theorem parent_patch_proof
    (hrec : ∀ {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ}, 0 < σ → 0 ≤ δ →
      DeltaSmall n σ δ → EnergySmall n σ E → F.IsCoherentUpTo σ δ N →
      ∀ (P : InitialChart F), PathBoundUpTo F P E N →
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ) (v : Spatial m),
        99 / 100 * ‖v‖ ≤ ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ∧
          ‖fderiv ℝ (fun w => stage F P j w t) u v‖ ≤ 101 / 100 * ‖v‖) ∧
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        ‖fderiv ℝ (fun v => fderiv ℝ (fun w => stage F P j w t) v) u‖ ≤
            chartCa n σ * chartEps n σ δ / F.scale j ∧
          ‖deriv (fun s => stage F P j u s) t‖ ≤ chartCa n σ * chartEps n σ δ / F.scale j) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖deriv (fun s => stage F P (j + 1) u s - stage F P j u s) t‖ ≤
          chartCΔ n σ * chartEps n σ δ / F.scale j))
    {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ} (_hm : 1 ≤ m)
    (_hmn : m < n) (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
    (hEsmall : EnergySmall n σ E) (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F)
    (hpath : PathBoundUpTo F P E N) {i : ℕ} (hi : i ≤ N) {a : ι} (ha : a ∈ F.index i)
    {t : ℝ} (ht : |t - (F.center i a).2.val| ≤ (3 / 2 * F.scale i) ^ 2) {u₀ : Spatial m}
    {η' : ℝ} (hη' : η' ≤ 1 / 100)
    (hu₀ : ‖stage F P (i + 1) u₀ t - (F.center i a).1‖ ≤ η' * F.scale i) :
    (∀ u ∈ Metric.closedBall u₀ (6 / 5 * F.scale i),
      Metric.infDist (stage F P (i + 1) u t) (F.plane i a).toSet ≤ 3 * δ * F.scale i ∧
        ‖(tangent F P (i + 1) u t).starProjection - (F.plane i a).linearProjection‖ ≤
          chartCr n σ * δ) ∧
    (∀ y ∈ (F.plane i a).toSet,
      ‖y - (F.plane i a).projection (stage F P (i + 1) u₀ t)‖ ≤ 21 / 20 * F.scale i →
        ∃ u ∈ Metric.closedBall u₀ (6 / 5 * F.scale i),
          (F.plane i a).projection (stage F P (i + 1) u t) = y) ∧
    (∀ (x : Spatial n) (q : ℝ), ‖x - (F.center i a).1‖ ≤ F.scale i →
      Metric.infDist x (F.plane i a).toSet ≤ q * F.scale i →
        ∃ u ∈ Metric.closedBall u₀ (6 / 5 * F.scale i),
          ‖stage F P (i + 1) u t - x‖ ≤ (q + 3 * δ) * F.scale i) := by
  obtain ⟨hspeed, hcurv, -⟩ := hrec hσ hδ hsmall hEsmall hF P hpath
  obtain ⟨-, -, -, -, hCa, -, -, -⟩ := chartConsts_bounds (n := n) hσ
  have hε0 := chartEps_nonneg (n := n) hσ hδ
  have hr := scale_pos F i
  have hGc : ContDiff ℝ ∞ (fun w => stage F P (i + 1) w t) :=
    contDiff_left (contDiff_stage F P (i + 1)) t
  have hGd : ∀ u, DifferentiableAt ℝ (fun w => stage F P (i + 1) w t) u :=
    fun u => differentiableAt_stage P (i + 1) u t
  have hLip : ∀ u, ‖stage F P (i + 1) u t - stage F P (i + 1) u₀ t‖ ≤ 101 / 100 * ‖u - u₀‖ :=
    fun u => norm_sub_le_of_fderiv_le hGd (by norm_num)
      (fun w v => (hspeed (i + 1) (by omega) w t v).2) u u₀
  -- first assertion: the reset on the whole parameter ball
  have hpatch : ∀ u ∈ Metric.closedBall u₀ (6 / 5 * F.scale i),
      Metric.infDist (stage F P (i + 1) u t) (F.plane i a).toSet ≤ 3 * δ * F.scale i ∧
        ‖(tangent F P (i + 1) u t).starProjection - (F.plane i a).linearProjection‖ ≤
          chartCr n σ * δ :=
    fun u hu => reset_of_mem_parentBall hσ hδ hsmall hF P hi ha
      (dist_lt_of_mem_parentPatch hσ hδ hsmall hF P hi ht hη' hu₀ hLip hu)
  -- second assertion: the derivative varies by at most `1.2 C_a ε / h ≤ 1/100`
  have hvar : ∀ u ∈ Metric.closedBall u₀ (6 / 5 * F.scale i),
      ‖fderiv ℝ (fun w => stage F P (i + 1) w t) u -
        fderiv ℝ (fun w => stage F P (i + 1) w t) u₀‖ ≤ 1 / 100 := by
    intro u hu
    have hu' : ‖u - u₀‖ ≤ 6 / 5 * F.scale i := by rw [← dist_eq_norm]; exact hu
    have hcoef : 0 ≤ chartCa n σ * chartEps n σ δ / F.scale (i + 1) :=
      div_nonneg (mul_nonneg hCa hε0) (scale_pos F (i + 1)).le
    have h1 := norm_fderiv_sub_le hGc (fun w => (hcurv (i + 1) (by omega) w t).1) u u₀
    have hval : chartCa n σ * chartEps n σ δ / F.scale (i + 1) * (6 / 5 * F.scale i) ≤
        1 / 100 := by
      have hh := hsmall.hessian
      rw [div_le_iff₀ ratio_pos] at hh
      rw [scale_succ F i, div_mul_eq_mul_div, div_le_iff₀ (mul_pos ratio_pos hr)]
      have := mul_le_mul_of_nonneg_right hh hr.le
      linarith
    exact h1.trans ((mul_le_mul_of_nonneg_left hu' hcoef).trans hval)
  have htan : ‖(LinearMap.range (fderiv ℝ (fun w => stage F P (i + 1) w t) u₀ :
      Spatial m →ₗ[ℝ] Spatial n)).starProjection - (F.plane i a).linearProjection‖ ≤ 1 / 10 :=
    (hpatch u₀ (Metric.mem_closedBall_self (by linarith))).2.trans hsmall.reset
  have hsurj := projection_surjOn_of_derivative hGd (F.plane i a)
    (fun v => (hspeed (i + 1) (by omega) u₀ t v).1) htan hvar
  refine ⟨hpatch, hsurj, ?_⟩
  -- third assertion: approximate preimages
  intro x q hx hxq
  have hy : (F.plane i a).projection x ∈ (F.plane i a).toSet := (F.plane i a).projection_mem x
  have hyd : ‖(F.plane i a).projection x - (F.plane i a).projection (stage F P (i + 1) u₀ t)‖ ≤
      21 / 20 * F.scale i := by
    have h1 : (F.plane i a).projection x - (F.plane i a).projection (stage F P (i + 1) u₀ t) =
        (F.plane i a).linearProjection (x - stage F P (i + 1) u₀ t) := by
      simp only [AffineSpatialPlane.projection, map_sub]
      abel
    have h2 := norm_sub_le_norm_sub_add_norm_sub x (F.center i a).1 (stage F P (i + 1) u₀ t)
    rw [norm_sub_rev (F.center i a).1] at h2
    have hη : η' * F.scale i ≤ 1 / 100 * F.scale i := mul_le_mul_of_nonneg_right hη' hr.le
    rw [h1]
    calc ‖(F.plane i a).linearProjection (x - stage F P (i + 1) u₀ t)‖
        ≤ ‖x - stage F P (i + 1) u₀ t‖ := (F.plane i a).direction.norm_starProjection_apply_le _
      _ ≤ 21 / 20 * F.scale i := by linarith
  obtain ⟨u, hu, hKu⟩ := hsurj _ hy hyd
  refine ⟨u, hu, ?_⟩
  have h1 := (hpatch u hu).1
  calc ‖stage F P (i + 1) u t - x‖
      = ‖(stage F P (i + 1) u t - (F.plane i a).projection (stage F P (i + 1) u t)) -
          (x - (F.plane i a).projection x)‖ := by
        rw [hKu]
        congr 1
        abel
    _ ≤ ‖stage F P (i + 1) u t - (F.plane i a).projection (stage F P (i + 1) u t)‖ +
          ‖x - (F.plane i a).projection x‖ := norm_sub_le _ _
    _ = Metric.infDist (stage F P (i + 1) u t) (F.plane i a).toSet +
          Metric.infDist x (F.plane i a).toSet := by
        rw [ProjectionReset.residual_eq_infDist, ProjectionReset.residual_eq_infDist]
    _ ≤ 3 * δ * F.scale i + q * F.scale i := add_le_add h1 hxq
    _ = (q + 3 * δ) * F.scale i := by ring

end Family

end CoherentChart

end ParabolicRectifiability
