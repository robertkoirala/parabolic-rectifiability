import ParabolicRectifiability.Basic

/-!
# A quantitative inverse on a ball

A quantitative inverse function lemma: if `H` is differentiable on the closed ball
`closedBall u₀ (1.2 r)`, its derivative stays within `0.01` of an invertible
operator `A` with `‖A⁻¹‖ ≤ 1/0.98`, then every `y` with `‖y - H u₀‖ ≤ 1.05 r` is a
value of `H` on that ball. The decimals are written as the exact fractions
`6/5`, `50/49`, `1/100` and `21/20`.

The proof uses Mathlib: the mean value inequality
`Convex.norm_image_sub_le_of_norm_fderiv_le'` gives `ApproximatesLinearOn H A`
with constant `1/100` on the ball, and
`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` (whose proof is the
contraction/Newton iteration) gives surjectivity onto the ball of
radius `(‖A⁻¹‖⁻¹ - 1/100) * (6/5) r ≥ (21/20) r`. A trivial target space (for instance
dimension zero, where `‖A⁻¹‖ = 0`) is treated separately. The operator `A` need not be
`DH(u₀)`; the usual choice `A = DH(u₀)` is a special case.
-/

noncomputable section

namespace ParabolicRectifiability.QuantitativeInverse

open Metric Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
/-- The derivative bound on the convex ball gives a linear approximation with constant `1/100`. -/
theorem approximatesLinearOn_of_fderiv_near (H : E → F) (u₀ : E) (ρ : ℝ) (A : E →L[ℝ] F)
    (hdiff : ∀ u ∈ closedBall u₀ ρ, DifferentiableAt ℝ H u)
    (hnear : ∀ u ∈ closedBall u₀ ρ, ‖fderiv ℝ H u - A‖ ≤ 1 / 100) :
    ApproximatesLinearOn H A (closedBall u₀ ρ) ⟨1 / 100, by norm_num⟩ := by
  intro x hx y hy
  exact (convex_closedBall u₀ ρ).norm_image_sub_le_of_norm_fderiv_le' hdiff hnear hy hx

/-- **Quantitative inverse on a ball.** Every `y` with `‖y - H u₀‖ ≤ (21/20) r` is attained on
`closedBall u₀ ((6/5) r)`. -/
theorem exists_mem_closedBall_eq (H : E → F) (u₀ : E) (r : ℝ) (A : E ≃L[ℝ] F)
    (hAinv : ‖(A.symm : F →L[ℝ] E)‖ ≤ 50 / 49)
    (hdiff : ∀ u ∈ closedBall u₀ (6 / 5 * r), DifferentiableAt ℝ H u)
    (hnear : ∀ u ∈ closedBall u₀ (6 / 5 * r), ‖fderiv ℝ H u - (A : E →L[ℝ] F)‖ ≤ 1 / 100)
    (y : F) (hy : ‖y - H u₀‖ ≤ 21 / 20 * r) :
    ∃ u ∈ closedBall u₀ (6 / 5 * r), H u = y := by
  have hr : 0 ≤ r := by
    have := norm_nonneg (y - H u₀)
    linarith
  have hmem : u₀ ∈ closedBall u₀ (6 / 5 * r) := mem_closedBall_self (by positivity)
  set N : ℝ := ‖(A.symm : F →L[ℝ] E)‖ with hNdef
  rcases (norm_nonneg (A.symm : F →L[ℝ] E)).eq_or_lt with hN | hN
  · -- `A⁻¹ = 0`, so the target is trivial and `y = H u₀`.
    have hzero : (A.symm : F →L[ℝ] E) = 0 := norm_eq_zero.mp hN.symm
    have hsub : ∀ z : F, z = 0 := by
      intro z
      have hz : A.symm z = 0 := by
        change (A.symm : F →L[ℝ] E) z = 0
        rw [hzero]
        rfl
      calc z = A (A.symm z) := (A.apply_symm_apply z).symm
        _ = 0 := by rw [hz, map_zero]
    exact ⟨u₀, hmem, by rw [hsub (H u₀), hsub y]⟩
  · have happrox := approximatesLinearOn_of_fderiv_near H u₀ (6 / 5 * r)
      (A : E →L[ℝ] F) hdiff hnear
    have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse
      A.toNonlinearRightInverse (by positivity) subset_rfl
    have hnn : ((A.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ) = N := rfl
    have hinv : 49 / 50 ≤ N⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hN]
      calc N ≤ 50 / 49 := hAinv
        _ = (49 / 50)⁻¹ := by norm_num
    have hyr : y ∈ closedBall (H u₀) ((((A.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ)⁻¹ -
        (1 / 100 : ℝ)) * (6 / 5 * r)) := by
      rw [hnn, mem_closedBall, dist_eq_norm]
      have hX : 49 / 50 * r ≤ N⁻¹ * r := mul_le_mul_of_nonneg_right hinv hr
      linarith
    obtain ⟨u, hu, hHu⟩ := hsurj hyr
    exact ⟨u, hu, hHu⟩

/-- The same statement under the hypothesis that `H` is continuously
differentiable on an open neighbourhood `U` of the closed ball. -/
theorem exists_mem_closedBall_eq_of_contDiffOn (H : E → F) (u₀ : E) (r : ℝ) (A : E ≃L[ℝ] F)
    (U : Set E) (hU : IsOpen U) (hsub : closedBall u₀ (6 / 5 * r) ⊆ U)
    (hH : ContDiffOn ℝ 1 H U)
    (hAinv : ‖(A.symm : F →L[ℝ] E)‖ ≤ 50 / 49)
    (hnear : ∀ u ∈ closedBall u₀ (6 / 5 * r), ‖fderiv ℝ H u - (A : E →L[ℝ] F)‖ ≤ 1 / 100)
    (y : F) (hy : ‖y - H u₀‖ ≤ 21 / 20 * r) :
    ∃ u ∈ closedBall u₀ (6 / 5 * r), H u = y :=
  exists_mem_closedBall_eq H u₀ r A hAinv
    (fun u hu => (hH.differentiableOn one_ne_zero u (hsub hu)).differentiableAt
      (hU.mem_nhds (hsub hu))) hnear y hy

end ParabolicRectifiability.QuantitativeInverse
