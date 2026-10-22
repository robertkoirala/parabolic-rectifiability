import ParabolicRectifiability.Geometry.Chart.Construction
import ParabolicRectifiability.Geometry.ProjectionReset

/-!
# Level partitions, ambient path bound and coverage for the coherent chart

Proofs of three intermediate statements of the coherent chart theorem
`vertical_coherent_chart`. Each statement `<name>` is proved here as `<name>_proof`.
When a proof needs another intermediate statement, that statement is an explicit
hypothesis:

* `pairwiseDisjoint_level_proof`, `isSmoothParabolicPartition_level_proof`:
  separation gives disjoint `σ r_j / 3`-balls, and the smooth partition theorem
  `isSmoothParabolicPartition_parabolicWeight` gives every weight bound;
* `pathBound_of_verticalSquareBound_proof` (local errors along the path are ambient
  comparisons), with the statement of `induction_estimates` as hypothesis `hA4` (only
  its displacement part is used); the reference point is `w = (F_{N+1}(u,t), t)`;
* `coverage_proof`, with the statements of `induction_estimates` (`hA4`, displacement
  only) and `parent_patch` (`hA9`, used only when `1 ≤ m < n`) as hypotheses.
  Rank zero is a convex-combination argument and full rank is exact
  surjectivity of the initial chart; both are proved here without `parent_patch`.

The coverage proof isolates the one local input as `Leaves.PatchProperty`: near a level-`i`
center covered at time `t`, every nearby point within `q r_i` of the fitted plane is
reached within `(q + 3δ) r_i` by the stage-`(i+1)` chart at time `t`.
-/

noncomputable section

namespace ParabolicRectifiability

namespace CoherentChart

open scoped ENNReal

variable {n m : ℕ} {ι : Type*}

/-! ## The level partitions -/

/-- Separation `σ r_j ≤ d_P` at level `j` makes the
`σ r_j / 3`-balls disjoint. -/
theorem pairwiseDisjoint_level_proof {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) :
    (F.index j : Set ι).PairwiseDisjoint
      (fun a => Metric.ball (F.center j a) (σ * F.scale j / 3)) := by
  intro a ha b hb hab
  have hsep := hF.separated j hj a ha b hb hab
  have hpos : 0 < σ * F.scale j := mul_pos hσ (scale_pos F j)
  exact Metric.ball_disjoint_ball (by linarith)

/-- The level weights form a smooth
parabolic partition with constant `C₀ = partitionConstant n σ`. -/
theorem isSmoothParabolicPartition_level_proof {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hF : F.IsCoherentUpTo σ δ N) {j : ℕ} (hj : j ≤ N) :
    IsSmoothParabolicPartition n (F.index j) (F.center j) (F.scale j) (chartC₀ n σ)
      (parabolicWeight (F.scale j) (F.index j) (F.center j)) :=
  isSmoothParabolicPartition_parabolicWeight hσ (scale_pos F j) (F.index j) (F.center j)
    (pairwiseDisjoint_level_proof hσ hF hj)

namespace Leaves

/-! ## Elementary facts -/

theorem point_fst_snd (z : Space n) : point z.1 z.2.val = z := rfl

theorem dist_space (z w : Space n) :
    dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) := by
  have h := dist_point z.1 w.1 z.2.val w.2.val
  rwa [point_fst_snd, point_fst_snd] at h

theorem norm_fst_sub_le_dist (z w : Space n) : ‖z.1 - w.1‖ ≤ dist z w := by
  rw [dist_space]
  exact le_max_left _ _

theorem abs_time_sub_le_dist_sq (z w : Space n) : |z.2.val - w.2.val| ≤ dist z w ^ 2 := by
  have h : Real.sqrt |z.2.val - w.2.val| ≤ dist z w := by
    rw [dist_space]
    exact le_max_right _ _
  calc |z.2.val - w.2.val| = Real.sqrt |z.2.val - w.2.val| ^ 2 :=
        (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ dist z w ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

theorem dist_point_same_time (x y : Spatial n) (t : ℝ) :
    dist (point x t) (point y t) = ‖x - y‖ := by
  rw [dist_point, sub_self, abs_zero, Real.sqrt_zero]
  exact max_eq_left (norm_nonneg _)

/-- A plane comparison anchored at `x₀` controls the affine projections at every point
within `r` of the anchor. -/
theorem norm_proj_sub_at_le {x₀ : Spatial n} {r δ : ℝ} {L L' : AffineSpatialPlane n m}
    (hr : 0 < r) (h : planeComparison x₀ r L L' ≤ δ) (y : Spatial n) (hy : ‖y - x₀‖ ≤ r) :
    ‖L.projection y - L'.projection y‖ ≤ δ * r := by
  have hid : L.projection y - L'.projection y =
      (L.projection x₀ - L'.projection x₀) +
        (L.linearProjection - L'.linearProjection) (y - x₀) := by
    simp only [AffineSpatialPlane.projection, sub_apply, map_sub]
    abel
  have hP : ‖(L.linearProjection - L'.linearProjection) (y - x₀)‖ ≤
      ‖L.linearProjection - L'.linearProjection‖ * r :=
    ((L.linearProjection - L'.linearProjection).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  unfold planeComparison at h
  have hN : ‖L.projection x₀ - L'.projection x₀‖ =
      r * (r⁻¹ * ‖L.projection x₀ - L'.projection x₀‖) := by
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have hm := mul_le_mul_of_nonneg_left h hr.le
  rw [hid]
  calc _ ≤ ‖L.projection x₀ - L'.projection x₀‖ +
        ‖(L.linearProjection - L'.linearProjection) (y - x₀)‖ := norm_add_le _ _
    _ ≤ ‖L.projection x₀ - L'.projection x₀‖ +
        ‖L.linearProjection - L'.linearProjection‖ * r := add_le_add le_rfl hP
    _ ≤ δ * r := by linarith

theorem infDist_le_add_norm_proj_sub (L L' : AffineSpatialPlane n m) (x : Spatial n) :
    Metric.infDist x L'.toSet ≤ Metric.infDist x L.toSet + ‖L.projection x - L'.projection x‖ := by
  rw [← ProjectionReset.residual_eq_infDist L, ← ProjectionReset.residual_eq_infDist L']
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- A rank-zero affine plane is its anchor point. -/
theorem projection_rank_zero (L : AffineSpatialPlane n 0) (x : Spatial n) :
    L.projection x = L.anchor := by
  have hbot : L.direction = ⊥ := Submodule.finrank_eq_zero.mp L.rank_eq
  have h : L.linearProjection x = 0 :=
    (Submodule.eq_bot_iff _).mp hbot _ (L.direction.starProjection_apply_mem x)
  rw [AffineSpatialPlane.projection, h, add_zero]

/-- A full-rank affine plane projects by the identity. -/
theorem projection_full (L : AffineSpatialPlane n n) (x : Spatial n) : L.projection x = x := by
  have htop := L.direction_eq_top
  have hperp : L.directionᗮ = ⊥ := Submodule.orthogonal_eq_bot_iff.mpr htop
  have ha : L.anchor = 0 := (Submodule.eq_bot_iff _).mp hperp _ L.anchor_orthogonal
  have hx : L.linearProjection x = x := by
    apply L.direction.starProjection_eq_self_iff.mpr
    rw [htop]
    exact Submodule.mem_top
  rw [AffineSpatialPlane.projection, ha, hx, zero_add]

/-- With weights summing to one, the weighted projection minus a point `a₀` is a
weighted combination of the differences. -/
theorem convex_shift {s : Finset ι} (w : ι → ℝ) (A : ι → Spatial n) (y a₀ : Spatial n)
    (hw : ∑ c ∈ s, w c = 1) :
    y + ∑ c ∈ s, w c • (A c - y) - a₀ = ∑ c ∈ s, w c • (A c - a₀) := by
  have h : ∑ c ∈ s, w c • (A c - y) =
      ∑ c ∈ s, w c • (A c - a₀) + ∑ c ∈ s, w c • (a₀ - y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_add]
    congr 1
    abel
  rw [h, ← Finset.sum_smul, hw, one_smul]
  abel

/-! ## Displacement sums -/

theorem norm_stage_sub_le {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (P : InitialChart F)
    (hε : 0 ≤ chartEps n σ δ)
    (hdisp : ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j)
    {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ N + 1) (u : Spatial m) (t : ℝ) :
    ‖stage F P l u t - stage F P k u t‖ ≤ chartEps n σ δ * F.scale k / (1 - ratio) :=
  norm_sub_le_geometric F (fun j => stage F P j u t) _ hε hkl
    (fun i _ hi => hdisp i (by omega) u t)

/-! ## Local errors along the path are ambient comparisons at `w` -/

theorem localError_zero_le {F : CoherentFamily n m ι} {q w : Space n}
    (hqw : dist q w ≤ 2 * F.scale 0) :
    localError F 0 q ≤ F.comparisonEnergy (fun z : Space n => z) 0 w := by
  simp only [localError, CoherentFamily.comparisonEnergy, CoherentFamily.rootComparisonTerm]
  refine iSup_le fun _ => iSup₂_le fun a ha => iSup_le fun hza => ?_
  refine le_iSup₂_of_le a ha (le_iSup_of_le ?_ le_rfl)
  calc dist (F.center 0 a) w ≤ dist (F.center 0 a) q + dist q w := dist_triangle _ _ _
    _ ≤ 10 * F.scale 0 + 2 * F.scale 0 := add_le_add hza hqw
    _ = 12 * F.scale 0 := by ring

theorem localError_succ_le {F : CoherentFamily n m ι} {j : ℕ} {q w : Space n}
    (hqw : dist q w ≤ 2 * F.scale j) :
    localError F (j + 1) q ≤ F.comparisonEnergy (fun z : Space n => z) (j + 1) w := by
  have hr := scale_pos F j
  simp only [localError, CoherentFamily.comparisonEnergy,
    CoherentFamily.sameLevelComparisonTerm, CoherentFamily.adjacentComparisonTerm]
  refine iSup_le fun _ => max_le_max ?_ ?_
  · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun hab => ?_
    refine le_iSup₂_of_le a ha (le_iSup₂_of_le b hb (le_iSup_of_le ⟨?_, ?_, ?_⟩ le_rfl))
    · have h := dist_triangle (F.center j a) q (F.center j b)
      rw [dist_comm q] at h
      linarith [hab.1, hab.2]
    · linarith [dist_triangle (F.center j a) q w, hab.1]
    · linarith [dist_triangle (F.center j b) q w, hab.2]
  · refine iSup₂_le fun a ha => iSup₂_le fun b hb => iSup_le fun hab => ?_
    refine le_iSup₂_of_le a ha (le_iSup₂_of_le b hb (le_iSup_of_le ⟨?_, ?_, ?_⟩ le_rfl))
    · have h := dist_triangle (F.center (j + 1) a) q (F.center j b)
      rw [dist_comm q] at h
      linarith [hab.1, hab.2]
    · linarith [dist_triangle (F.center (j + 1) a) q w, hab.1]
    · linarith [dist_triangle (F.center j b) q w, hab.2]

end Leaves

-- The hypotheses restating other statements keep the binder names of those statements.
set_option linter.unusedVariables false in
/-- **Ambient path bound.** A vertical square bound for the comparison energy gives the
path bound. The hypothesis `hA4` is the statement of `induction_estimates`; only its
displacement part is used. -/
theorem pathBound_of_verticalSquareBound_proof
    (hA4 : ∀ {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (hσ : 0 < σ)
      (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hF : F.IsCoherentUpTo σ δ N)
      (P : InitialChart F),
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        Function.Injective (fderiv ℝ (fun v => stage F P j v t) u)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), ∀ a ∈ F.index j, ∀ b ∈ F.index j,
        IsActive F j a (stage F P j u t) t → IsActive F j b (stage F P j u t) t →
          ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
              (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) ≤
            ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j))
    {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hF : F.IsCoherentUpTo σ δ N)
    (hE : F.VerticalSquareBoundUpTo E N) (P : InitialChart F) :
    PathBoundUpTo F P E N := by
  intro u t
  have hdisp := (hA4 hσ hδ hsmall hF P).2.2
  have hε0 := chartEps_nonneg (n := n) hσ hδ
  have hε1 := hsmall.eps_le
  have hnear : ∀ j ≤ N,
      dist (pathPoint F P j u t) (pathPoint F P (N + 1) u t) ≤ F.scale j / 90 := by
    intro j hj
    have h := Leaves.norm_stage_sub_le P hε0 hdisp (show j ≤ N + 1 by omega) le_rfl u t
    have hr := scale_pos F j
    have hm : chartEps n σ δ * F.scale j ≤ 1 / 100 * F.scale j :=
      mul_le_mul_of_nonneg_right hε1 hr.le
    have hq : chartEps n σ δ * F.scale j / (1 - ratio) =
        chartEps n σ δ * F.scale j * (10 / 9) := by
      unfold ratio
      ring
    rw [hq] at h
    simp only [pathPoint]
    rw [Leaves.dist_point_same_time, norm_sub_rev]
    linarith
  unfold pathSquareSum
  calc ∑ j ∈ Finset.range (N + 1), localError F j (pathPoint F P j u t) ^ 2
      ≤ ∑ j ∈ Finset.range (N + 1),
          F.comparisonEnergy (fun z : Space n => z) j (pathPoint F P (N + 1) u t) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        apply pow_le_pow_left₀ (by positivity)
        have hd := hnear j hjN
        cases j with
        | zero =>
          have := scale_pos F 0
          exact Leaves.localError_zero_le (by linarith)
        | succ j =>
          apply Leaves.localError_succ_le
          have hs := scale_succ F j
          have := scale_pos F j
          unfold ratio at hs
          rw [hs] at hd
          linarith
    _ ≤ ENNReal.ofReal E := hE (pathPoint F P (N + 1) u t)

namespace Leaves

/-! ## Coverage from the local patch property -/

/-- The local patch property: near a level-`i` center covered at time `t` by the
stage-`(i+1)` chart, every point within `r_i` of the center and within `q r_i` of the
fitted plane is reached within `(q + 3δ) r_i` at the same time. -/
def PatchProperty (F : CoherentFamily n m ι) (P : InitialChart F) (σ δ κ : ℝ) (N : ℕ) :
    Prop :=
  ∀ i ≤ N, ∀ b ∈ F.index i, ∀ t : ℝ, |t - (F.center i b).2.val| ≤ (3 / 2 * F.scale i) ^ 2 →
    ∀ u₀ : Spatial m,
      ‖stage F P (i + 1) u₀ t - (F.center i b).1‖ ≤ coverageCoeff n σ κ δ * F.scale i →
    ∀ (x : Spatial n) (q : ℝ), ‖x - (F.center i b).1‖ ≤ F.scale i →
      Metric.infDist x (F.plane i b).toSet ≤ q * F.scale i →
      ∃ u : Spatial m, ‖stage F P (i + 1) u t - x‖ ≤ (q + 3 * δ) * F.scale i

/-- Every point of the initial plane is a value of the initial chart. -/
theorem exists_stage_zero_eq {F : CoherentFamily n m ι} (P : InitialChart F) {y : Spatial n}
    (hy : y ∈ F.initialPlane.toSet) : ∃ u : Spatial m, ∀ t : ℝ, stage F P 0 u t = y := by
  have hv : y - P.origin ∈ LinearMap.range P.isometry.toLinearMap := by
    rw [P.range_eq]
    have h1 : y - F.initialPlane.anchor ∈ F.initialPlane.direction := hy
    have h2 : P.origin - F.initialPlane.anchor ∈ F.initialPlane.direction := P.origin_mem
    have h3 := F.initialPlane.direction.sub_mem h1 h2
    have he : y - F.initialPlane.anchor - (P.origin - F.initialPlane.anchor) = y - P.origin := by
      abel
    rwa [he] at h3
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv
  refine ⟨u, fun t => ?_⟩
  have hu' : P.isometry u = y - P.origin := hu
  show P.origin + P.isometry u = y
  rw [hu']
  abel

/-- Coverage from the displacement estimate and the patch property. -/
theorem coverage_of_patch {F : CoherentFamily n m ι} {σ δ κ : ℝ} {N : ℕ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hF : F.IsCoherentUpTo σ δ N) (hheight : F.HasCenterHeightUpTo κ N)
    (P : InitialChart F)
    (hdisp : ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j)
    (hPP : PatchProperty F P σ δ κ N) :
    (∀ j ≤ N, ∀ a ∈ F.index j, ∀ t : ℝ, |t - (F.center j a).2.val| ≤ (3 / 2 * F.scale j) ^ 2 →
      ∃ u : Spatial m,
        ‖stage F P (j + 1) u t - (F.center j a).1‖ ≤ coverageCoeff n σ κ δ * F.scale j ∧
        ∀ l, j + 1 ≤ l → l ≤ N + 1 →
          ‖stage F P l u t - (F.center j a).1‖ ≤
            coverageCoeff n σ κ δ * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio)) ∧
    (∀ j ≤ N, ∀ a ∈ F.index j, ∀ (c : Space n) (θ : ℝ), dist c (F.center j a) ≤ F.scale j →
      Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j →
      ∃ u : Spatial m,
        ‖stage F P (j + 1) u c.2.val - c.1‖ ≤ (θ + 3 * δ) * F.scale j ∧
        ∀ l, j + 1 ≤ l → l ≤ N + 1 →
          ‖stage F P l u c.2.val - c.1‖ ≤
            (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio)) := by
  have hε := chartEps_nonneg (n := n) hσ hδ
  have hη : coverageCoeff n σ κ δ = κ + 50 * δ + chartEps n σ δ := by
    unfold coverageCoeff chartEps ratio
    ring
  -- Level coverage at every center and every time of its window.
  have hC : ∀ j, j ≤ N → ∀ a ∈ F.index j, ∀ t : ℝ,
      |t - (F.center j a).2.val| ≤ (3 / 2 * F.scale j) ^ 2 →
      ∃ u : Spatial m, ‖stage F P (j + 1) u t - (F.center j a).1‖ ≤
        coverageCoeff n σ κ δ * F.scale j := by
    intro j
    induction j with
    | zero =>
      intro _ a ha t _
      have hr := scale_pos F 0
      obtain ⟨u, hu⟩ := exists_stage_zero_eq P
        (F.initialPlane.projection_mem (F.center 0 a).1)
      refine ⟨u, ?_⟩
      have hh := hheight 0 (Nat.zero_le _) a ha
      rw [← ProjectionReset.residual_eq_infDist] at hh
      have hroot := norm_proj_sub_at_le hr (hF.root a ha) (F.center 0 a).1
        (by rw [sub_self, norm_zero]; exact hr.le)
      have h0 : ‖stage F P 0 u t - (F.center 0 a).1‖ ≤ κ * F.scale 0 + δ * F.scale 0 := by
        rw [hu t, norm_sub_rev]
        calc _ ≤ ‖(F.center 0 a).1 - (F.plane 0 a).projection (F.center 0 a).1‖ +
              ‖(F.plane 0 a).projection (F.center 0 a).1 -
                F.initialPlane.projection (F.center 0 a).1‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ κ * F.scale 0 + δ * F.scale 0 := add_le_add hh hroot
      have h1 := hdisp 0 (Nat.zero_le _) u t
      have hδr : 0 ≤ δ * F.scale 0 := mul_nonneg hδ hr.le
      calc ‖stage F P (0 + 1) u t - (F.center 0 a).1‖
          ≤ ‖stage F P (0 + 1) u t - stage F P 0 u t‖ + ‖stage F P 0 u t - (F.center 0 a).1‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ coverageCoeff n σ κ δ * F.scale 0 := by
            rw [hη]
            linarith
    | succ j ih =>
      intro hj1 a ha t ht
      have hjN : j ≤ N := by omega
      have hr := scale_pos F j
      have hs : F.scale (j + 1) = 1 / 10 * F.scale j := scale_succ F j
      have hb : F.parent (j + 1) a ∈ F.index j := hF.parent_mem j hj1 a ha
      have hab : dist (F.center (j + 1) a) (F.center j (F.parent (j + 1) a)) ≤ F.scale j :=
        hF.parent_dist j hj1 a ha
      have htb : |t - (F.center j (F.parent (j + 1) a)).2.val| ≤ (3 / 2 * F.scale j) ^ 2 := by
        have h1 := abs_time_sub_le_dist_sq (F.center (j + 1) a) (F.center j (F.parent (j + 1) a))
        have h2 : dist (F.center (j + 1) a) (F.center j (F.parent (j + 1) a)) ^ 2 ≤
            F.scale j ^ 2 := pow_le_pow_left₀ dist_nonneg hab 2
        have h3 := abs_sub_le t (F.center (j + 1) a).2.val
          (F.center j (F.parent (j + 1) a)).2.val
        rw [hs] at ht
        linarith [sq_nonneg (F.scale j)]
      obtain ⟨u₀, hu₀⟩ := ih hjN (F.parent (j + 1) a) hb t htb
      have hx : ‖(F.center (j + 1) a).1 - (F.center j (F.parent (j + 1) a)).1‖ ≤ F.scale j :=
        (norm_fst_sub_le_dist _ _).trans hab
      have hadj := hF.adjacent j hj1 a ha (F.parent (j + 1) a) hb (by linarith)
      have hπ := norm_proj_sub_at_le hr hadj (F.center (j + 1) a).1 hx
      have hq : Metric.infDist (F.center (j + 1) a).1 (F.plane j (F.parent (j + 1) a)).toSet ≤
          (κ * (1 / 10) + δ) * F.scale j := by
        have h1 := infDist_le_add_norm_proj_sub (F.plane (j + 1) a)
          (F.plane j (F.parent (j + 1) a)) (F.center (j + 1) a).1
        have h2 := hheight (j + 1) hj1 a ha
        rw [hs] at h2
        linarith
      obtain ⟨u, hu⟩ := hPP j hjN (F.parent (j + 1) a) hb t htb u₀ hu₀
        (F.center (j + 1) a).1 (κ * (1 / 10) + δ) hx hq
      refine ⟨u, ?_⟩
      have h1 := hdisp (j + 1) hj1 u t
      rw [hs] at h1
      have hδr : 0 ≤ δ * F.scale j := mul_nonneg hδ hr.le
      calc ‖stage F P (j + 1 + 1) u t - (F.center (j + 1) a).1‖
          ≤ ‖stage F P (j + 1 + 1) u t - stage F P (j + 1) u t‖ +
              ‖stage F P (j + 1) u t - (F.center (j + 1) a).1‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ coverageCoeff n σ κ δ * F.scale (j + 1) := by
            rw [hη, hs]
            linarith
  -- Stopping points at their own times.
  have hS : ∀ j ≤ N, ∀ a ∈ F.index j, ∀ (c : Space n) (θ : ℝ), dist c (F.center j a) ≤ F.scale j →
      Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j →
      ∃ u : Spatial m, ‖stage F P (j + 1) u c.2.val - c.1‖ ≤ (θ + 3 * δ) * F.scale j := by
    intro j hj a ha c θ hc1 hc2
    have hr := scale_pos F j
    have ht : |c.2.val - (F.center j a).2.val| ≤ (3 / 2 * F.scale j) ^ 2 := by
      have h1 := abs_time_sub_le_dist_sq c (F.center j a)
      have h2 : dist c (F.center j a) ^ 2 ≤ F.scale j ^ 2 := pow_le_pow_left₀ dist_nonneg hc1 2
      linarith [sq_nonneg (F.scale j)]
    obtain ⟨u₀, hu₀⟩ := hC j hj a ha c.2.val ht
    exact hPP j hj a ha c.2.val ht u₀ hu₀ c.1 θ ((norm_fst_sub_le_dist _ _).trans hc1) hc2
  -- Later stages move the chosen parameter by at most `ε r_{j+1}/(1-h)`.
  have hlater : ∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ) (x : Spatial n) (B : ℝ),
      ‖stage F P (j + 1) u t - x‖ ≤ B → ∀ l, j + 1 ≤ l → l ≤ N + 1 →
      ‖stage F P l u t - x‖ ≤ B + chartEps n σ δ * F.scale (j + 1) / (1 - ratio) := by
    intro j _ u t x B hB l hl1 hl2
    have h := norm_stage_sub_le P hε hdisp hl1 hl2 u t
    calc ‖stage F P l u t - x‖ ≤ ‖stage F P l u t - stage F P (j + 1) u t‖ +
          ‖stage F P (j + 1) u t - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B + chartEps n σ δ * F.scale (j + 1) / (1 - ratio) := by linarith
  refine ⟨fun j hj a ha t ht => ?_, fun j hj a ha c θ hc1 hc2 => ?_⟩
  · obtain ⟨u, hu⟩ := hC j hj a ha t ht
    exact ⟨u, hu, hlater j hj u t _ _ hu⟩
  · obtain ⟨u, hu⟩ := hS j hj a ha c θ hc1 hc2
    exact ⟨u, hu, hlater j hj u _ _ _ hu⟩

-- The hypotheses restating other statements keep the binder names of those statements.
set_option linter.unusedVariables false in
/-- The patch property in the intermediate ranks `1 ≤ m < n`, from the statement of
`parent_patch`. -/
theorem patchProperty_of_parent_patch
    (hA9 : ∀ {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ} (hm : 1 ≤ m)
      (hmn : m < n) (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
      (hEsmall : EnergySmall n σ E) (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F)
      (hpath : PathBoundUpTo F P E N) {i : ℕ} (hi : i ≤ N) {a : ι} (ha : a ∈ F.index i)
      {t : ℝ} (ht : |t - (F.center i a).2.val| ≤ (3 / 2 * F.scale i) ^ 2) {u₀ : Spatial m}
      {η' : ℝ} (hη' : η' ≤ 1 / 100)
      (hu₀ : ‖stage F P (i + 1) u₀ t - (F.center i a).1‖ ≤ η' * F.scale i),
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
            ‖stage F P (i + 1) u t - x‖ ≤ (q + 3 * δ) * F.scale i))
    (hm : 1 ≤ m) (hmn : m < n) {F : CoherentFamily n m ι} {σ δ E κ : ℝ} {N : ℕ}
    (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hEsmall : EnergySmall n σ E)
    (hcov : CoverageSmall n σ κ δ) (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F)
    (hpath : PathBoundUpTo F P E N) : PatchProperty F P σ δ κ N := by
  intro i hi b hb t ht u₀ hu₀ x q hx hq
  have hc : coverageCoeff n σ κ δ ≤ 1 / 100 := hcov
  obtain ⟨u, -, hu⟩ :=
    (hA9 hm hmn hσ hδ hsmall hEsmall hF P hpath hi hb ht hc hu₀).2.2 x q hx hq
  exact ⟨u, hu⟩

/-- The patch property in rank zero: a convex combination of fitted points. -/
theorem patchProperty_rank_zero {F : CoherentFamily n 0 ι} {σ δ κ : ℝ} {N : ℕ}
    (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hcov : CoverageSmall n σ κ δ)
    (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F)
    (hdisp : ∀ j ≤ N, ∀ (u : Spatial 0) (t : ℝ),
      ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j) :
    PatchProperty F P σ δ κ N := by
  intro i hi b hb t ht u₀ hu₀ x q _ hq
  refine ⟨u₀, ?_⟩
  have hr := scale_pos F i
  have hε1 := hsmall.eps_le
  have hc : coverageCoeff n σ κ δ ≤ 1 / 100 := hcov
  have hstage : stage F P (i + 1) u₀ t = stage F P i u₀ t +
      ∑ c ∈ F.index i, weight F i c (stage F P i u₀ t) t •
        ((F.plane i c).anchor - stage F P i u₀ t) := by
    show CoherentProjection.sigma (F.index i) (F.plane i) (weight F i) (stage F P i u₀ t) t = _
    simp only [CoherentProjection.sigma, projection_rank_zero]
  -- The predecessor is close to the center, so the level weights sum to one there.
  have hy : ‖stage F P i u₀ t - (F.center i b).1‖ ≤
      (coverageCoeff n σ κ δ + chartEps n σ δ) * F.scale i := by
    have h1 := hdisp i hi u₀ t
    rw [norm_sub_rev] at h1
    calc _ ≤ ‖stage F P i u₀ t - stage F P (i + 1) u₀ t‖ +
          ‖stage F P (i + 1) u₀ t - (F.center i b).1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith
  have hball : point (stage F P i u₀ t) t ∈ Metric.ball (F.center i b) (2 * F.scale i) := by
    rw [← point_fst_snd (F.center i b), mem_ball_point _ _ _ _ _ (by linarith)]
    constructor
    · have h1 : (coverageCoeff n σ κ δ + chartEps n σ δ) * F.scale i ≤ 1 / 50 * F.scale i :=
        mul_le_mul_of_nonneg_right (by linarith) hr.le
      linarith
    · linarith [mul_pos hr hr]
  have hsum : ∑ c ∈ F.index i, weight F i c (stage F P i u₀ t) t = 1 :=
    sum_parabolicWeight_eq_one (p := (stage F P i u₀ t, t)) hr (F.index i) (F.center i)
      ⟨b, hb, hball⟩
  have hclose : ∀ c ∈ F.index i, weight F i c (stage F P i u₀ t) t ≠ 0 →
      ‖(F.plane i c).anchor - (F.plane i b).anchor‖ ≤ δ * F.scale i := by
    intro c hc' hne
    have hsupp : point (stage F P i u₀ t) t ∈ Metric.ball (F.center i c) (3 * F.scale i) :=
      tsupport_parabolicWeight_subset (p := (stage F P i u₀ t, t)) hr (F.index i) (F.center i) c
        (subset_tsupport _ (Function.mem_support.mpr hne))
    have hdist : dist (F.center i c) (F.center i b) ≤ 20 * F.scale i := by
      have h1 := Metric.mem_ball.mp hsupp
      have h2 := Metric.mem_ball.mp hball
      have h3 := dist_triangle_left (F.center i c) (F.center i b) (point (stage F P i u₀ t) t)
      linarith
    have hcmp := hF.same i hi c hc' b hb hdist
    have h := norm_proj_sub_at_le hr hcmp (F.center i c).1 (by rw [sub_self, norm_zero]; exact hr.le)
    rwa [projection_rank_zero, projection_rank_zero] at h
  have hnorm : ‖stage F P (i + 1) u₀ t - (F.plane i b).anchor‖ ≤ δ * F.scale i := by
    rw [hstage, convex_shift _ _ _ _ hsum]
    have h : ‖∑ c ∈ F.index i, weight F i c (stage F P i u₀ t) t •
          ((F.plane i c).anchor - (F.plane i b).anchor)‖ ≤
        (∑ c ∈ F.index i, |weight F i c (stage F P i u₀ t) t|) * (δ * F.scale i) :=
      CoherentProjection.norm_sum_smul_le (F.index i)
        (fun c => weight F i c (stage F P i u₀ t) t)
        (fun c => (F.plane i c).anchor - (F.plane i b).anchor) (δ * F.scale i) hclose
    have habs : ∑ c ∈ F.index i, |weight F i c (stage F P i u₀ t) t| = 1 := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun c _ => abs_of_nonneg (parabolicWeight_nonneg _ _ _ _ _)
    rw [habs, one_mul] at h
    exact h
  have hxb : ‖x - (F.plane i b).anchor‖ ≤ q * F.scale i := by
    have h := ProjectionReset.residual_eq_infDist (F.plane i b) x
    rw [projection_rank_zero] at h
    linarith
  have hδr : 0 ≤ δ * F.scale i := mul_nonneg hδ hr.le
  calc ‖stage F P (i + 1) u₀ t - x‖ ≤ ‖stage F P (i + 1) u₀ t - (F.plane i b).anchor‖ +
        ‖(F.plane i b).anchor - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ * F.scale i + q * F.scale i := by rw [norm_sub_rev (F.plane i b).anchor]; linarith
    _ ≤ (q + 3 * δ) * F.scale i := by linarith

/-- In full rank every stage map is the identity. -/
theorem stage_full {F : CoherentFamily n n ι} (P : InitialChart F) (j : ℕ) (u : Spatial n)
    (t : ℝ) : stage F P j u t = P.origin + P.isometry u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show CoherentProjection.sigma (F.index j) (F.plane j) (weight F j) (stage F P j u t) t = _
    simp only [CoherentProjection.sigma, projection_full, sub_self, smul_zero,
      Finset.sum_const_zero, add_zero, ih]

/-- The patch property in full rank: every point is attained exactly. -/
theorem patchProperty_full {F : CoherentFamily n n ι} {σ δ κ : ℝ} {N : ℕ} (hδ : 0 ≤ δ)
    (P : InitialChart F) : PatchProperty F P σ δ κ N := by
  intro i _ b _ t _ u₀ _ x q _ hq
  have hv : x - P.origin ∈ LinearMap.range P.isometry.toLinearMap := by
    rw [P.range_eq, F.initialPlane.direction_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hv
  have hu' : P.isometry u = x - P.origin := hu
  refine ⟨u, ?_⟩
  have hr := scale_pos F i
  have hq0 : 0 ≤ q * F.scale i := Metric.infDist_nonneg.trans hq
  have hx : stage F P (i + 1) u t = x := by
    rw [stage_full, hu']
    abel
  rw [hx, sub_self, norm_zero]
  linarith [mul_nonneg hδ hr.le]

end Leaves

-- The hypotheses restating other statements keep the binder names of those statements.
set_option linter.unusedVariables false in
/-- **Coverage** in every rank `0 ≤ m ≤ n`. The hypotheses `hA4` and `hA9` are the
statements of `induction_estimates` (only its displacement part is used) and
`parent_patch` (used only for `1 ≤ m < n`). -/
theorem coverage_proof
    (hA4 : ∀ {F : CoherentFamily n m ι} {σ δ : ℝ} {N : ℕ} (hσ : 0 < σ)
      (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hF : F.IsCoherentUpTo σ δ N)
      (P : InitialChart F),
      (∀ j ≤ N + 1, ∀ (u : Spatial m) (t : ℝ),
        Function.Injective (fderiv ℝ (fun v => stage F P j v t) u)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ), ∀ a ∈ F.index j, ∀ b ∈ F.index j,
        IsActive F j a (stage F P j u t) t → IsActive F j b (stage F P j u t) t →
          ENNReal.ofReal (‖(tangent F P j u t).starProjection - (F.plane j a).linearProjection‖ +
              (F.scale j)⁻¹ * Metric.infDist (stage F P j u t) (F.plane j b).toSet) ≤
            ENNReal.ofReal (chartA n σ / ratio) * localError F j (pathPoint F P j u t)) ∧
      (∀ j ≤ N, ∀ (u : Spatial m) (t : ℝ),
        ‖stage F P (j + 1) u t - stage F P j u t‖ ≤ chartEps n σ δ * F.scale j))
    (hA9 : ∀ {F : CoherentFamily n m ι} {σ δ E : ℝ} {N : ℕ} (hm : 1 ≤ m)
      (hmn : m < n) (hσ : 0 < σ) (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ)
      (hEsmall : EnergySmall n σ E) (hF : F.IsCoherentUpTo σ δ N) (P : InitialChart F)
      (hpath : PathBoundUpTo F P E N) {i : ℕ} (hi : i ≤ N) {a : ι} (ha : a ∈ F.index i)
      {t : ℝ} (ht : |t - (F.center i a).2.val| ≤ (3 / 2 * F.scale i) ^ 2) {u₀ : Spatial m}
      {η' : ℝ} (hη' : η' ≤ 1 / 100)
      (hu₀ : ‖stage F P (i + 1) u₀ t - (F.center i a).1‖ ≤ η' * F.scale i),
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
            ‖stage F P (i + 1) u t - x‖ ≤ (q + 3 * δ) * F.scale i))
    {F : CoherentFamily n m ι} {σ δ E κ : ℝ} {N : ℕ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hsmall : DeltaSmall n σ δ) (hEsmall : EnergySmall n σ E) (hκ : 0 ≤ κ)
    (hcov : CoverageSmall n σ κ δ) (hF : F.IsCoherentUpTo σ δ N)
    (hheight : F.HasCenterHeightUpTo κ N) (P : InitialChart F)
    (hpath : PathBoundUpTo F P E N) :
    (∀ j ≤ N, ∀ a ∈ F.index j, ∀ t : ℝ, |t - (F.center j a).2.val| ≤ (3 / 2 * F.scale j) ^ 2 →
      ∃ u : Spatial m,
        ‖stage F P (j + 1) u t - (F.center j a).1‖ ≤ coverageCoeff n σ κ δ * F.scale j ∧
        ∀ l, j + 1 ≤ l → l ≤ N + 1 →
          ‖stage F P l u t - (F.center j a).1‖ ≤
            coverageCoeff n σ κ δ * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio)) ∧
    (∀ j ≤ N, ∀ a ∈ F.index j, ∀ (c : Space n) (θ : ℝ), dist c (F.center j a) ≤ F.scale j →
      Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j →
      ∃ u : Spatial m,
        ‖stage F P (j + 1) u c.2.val - c.1‖ ≤ (θ + 3 * δ) * F.scale j ∧
        ∀ l, j + 1 ≤ l → l ≤ N + 1 →
          ‖stage F P l u c.2.val - c.1‖ ≤
            (θ + 3 * δ) * F.scale j + chartEps n σ δ * F.scale (j + 1) / (1 - ratio)) := by
  have hdisp := (hA4 hσ hδ hsmall hF P).2.2
  have hPP : Leaves.PatchProperty F P σ δ κ N := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      exact Leaves.patchProperty_rank_zero hδ hsmall hcov hF P hdisp
    · rcases Nat.lt_or_ge m n with hlt | hge
      · exact Leaves.patchProperty_of_parent_patch hA9 hmpos hlt hσ hδ hsmall hEsmall hcov hF P
          hpath
      · have hle : m ≤ n := AffineSpatialPlane.nonempty_iff.mp ⟨F.initialPlane⟩
        have hmn : m = n := le_antisymm hle hge
        subst hmn
        exact Leaves.patchProperty_full hδ P
  exact Leaves.coverage_of_patch hσ hδ hF hheight P hdisp hPP

end CoherentChart

end ParabolicRectifiability
