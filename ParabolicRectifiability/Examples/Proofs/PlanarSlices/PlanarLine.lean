import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # Unit-normal equations and distance for affine lines in the Euclidean plane -/

noncomputable section

namespace ParabolicRectifiability.Examples

open Module
open ParabolicRectifiability.BetaP (Plane)
open scoped InnerProductSpace

private lemma planar_inner_coordinates (x n : Plane) :
    ⟪x, n⟫_ℝ = n 0 * x 0 + n 1 * x 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]

/-- The nearest-point residual lies on the normal line, so its norm is the
absolute value of its signed normal coordinate. -/
private lemma planarLine_infEDist (L : AffineSpatialPlane 2 1) (n : Plane)
    (hn : ‖n‖ = 1) (hspan : L.directionᗮ = ℝ ∙ n) (w : Plane) :
    Metric.infEDist w L.toSet = ENNReal.ofReal |⟪w, n⟫_ℝ - ⟪L.anchor, n⟫_ℝ| := by
  have hnormal : n ∈ L.directionᗮ := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self n
  have hp : ⟪L.direction.starProjection w, n⟫_ℝ = 0 :=
    (L.direction.mem_orthogonal n).mp hnormal _ (L.direction.starProjection_apply_mem w)
  have hr : w - L.projection w ∈ ℝ ∙ n := by
    rw [← hspan]
    exact L.residual_orthogonal w
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hr
  have hnorm : ‖w - L.projection w‖ = |⟪w - L.projection w, n⟫_ℝ| := by
    rw [← ht, norm_smul, real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
    simp
  have hdist : Metric.infEDist w L.toSet = ENNReal.ofReal ‖w - L.projection w‖ := by
    apply le_antisymm
    · simpa [edist_dist, dist_eq_norm] using
        Metric.infEDist_le_edist_of_mem (L.projection_mem w)
    · apply Metric.le_infEDist.mpr
      intro y hy
      rw [edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal (L.nearest w hy)
  rw [hdist, hnorm, inner_sub_left]
  simp [AffineSpatialPlane.projection, AffineSpatialPlane.linearProjection, inner_add_left, hp]

/-- Every affine Euclidean line has a normalized equation, and every normalized
linear equation is realized by an affine line, with the exact distance formula. -/
theorem e2_planarLine_proof : E2PlanarLine := by
  constructor
  · intro L
    have hrank : finrank ℝ L.directionᗮ = 1 := by
      have h := L.direction.finrank_add_finrank_orthogonal
      rw [L.rank_eq, finrank_euclideanSpace_fin] at h
      omega
    let : Nontrivial L.directionᗮ := Module.nontrivial_of_finrank_eq_succ hrank
    obtain ⟨n, hn⟩ := exists_norm_eq L.directionᗮ (show (0 : ℝ) ≤ 1 by norm_num)
    have hn' : ‖(n : Plane)‖ = 1 := hn
    have hn0 : (n : Plane) ≠ 0 := by
      intro h
      simp [h] at hn'
    have hspan : L.directionᗮ = ℝ ∙ (n : Plane) :=
      eq_span_singleton_of_mem_of_finrank_eq_one hrank n.property hn0
    refine ⟨n.val 0, n.val 1, ⟪L.anchor, (n : Plane)⟫_ℝ, ?_, ?_⟩
    · have h := real_inner_self_eq_norm_sq (n : Plane)
      rw [hn', planar_inner_coordinates] at h
      nlinarith [h]
    · intro w
      simpa [planar_inner_coordinates] using planarLine_infEDist L n hn' hspan w
  · intro a b c hab
    let n : Plane := !₂[a, b]
    have hn : ‖n‖ = 1 := by
      have h : ‖n‖ ^ 2 = 1 := by
        simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, n] using hab
      nlinarith [norm_nonneg n]
    have hn0 : n ≠ 0 := by
      intro h
      simp [h] at hn
    let U : Submodule ℝ Plane := (ℝ ∙ n)ᗮ
    have hU : finrank ℝ U = 1 := by
      have h := (ℝ ∙ n).finrank_add_finrank_orthogonal
      rw [finrank_span_singleton hn0, finrank_euclideanSpace_fin] at h
      dsimp [U]
      omega
    let L : AffineSpatialPlane 2 1 :=
      { direction := U
        rank_eq := hU
        anchor := c • n
        anchor_orthogonal := by
          dsimp [U]
          rw [Submodule.orthogonal_orthogonal]
          exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self n) }
    refine ⟨L, fun w => ?_⟩
    have hspan : L.directionᗮ = ℝ ∙ n := by
      exact Submodule.orthogonal_orthogonal (ℝ ∙ n)
    have hc : ⟪L.anchor, n⟫_ℝ = c := by
      change ⟪c • n, n⟫_ℝ = c
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
      ring
    rw [planarLine_infEDist L n hn hspan w, hc, planar_inner_coordinates]
    rfl

end ParabolicRectifiability.Examples
