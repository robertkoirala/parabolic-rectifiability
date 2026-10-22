import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion

/-! # Second-order spatial affine Poincaré on a Euclidean ball

Proof of `d1e_spatial_secondPoincare_proof`, in implication form
`d1e_SpatialPoincareStatement → d1e_SpatialSecondPoincareStatement`. The first-order spatial
Poincaré statement enters only as the hypothesis.

Route: with the first-order constant `C₁ = C₁(m)`, apply the hypothesis with
`Y = ℝ^m →L[ℝ] ℝ^d` to `Df` (`C¹` by `ContDiff.fderiv_right`): a constant `L` with
`∫_B ‖Df - L‖² ≤ C₁ r² ∫_B ‖D²f‖²`. Apply it again with `Y = ℝ^d` to `g = f - L(·)`, whose
derivative is `Df - L` (`fderiv_fun_sub`, `ContinuousLinearMap.fderiv`): a constant `a` with
`∫_B |f - L u - a|² ≤ C₁ r² ∫_B ‖Df - L‖²`. Take `B = L`, `C = C₁²` and rewrite
`f u - (a + L u) = (f u - L u) - a`. Rank zero is included (no case split is needed).

Helpers carry the prefix `d1esecondp_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- The derivative of `u ↦ f u - L u` is `Df - L`. -/
theorem d1esecondp_fderiv_sub_clm {m d : ℕ} {f : Spatial m → Spatial d}
    (hf : Differentiable ℝ f) (L : Spatial m →L[ℝ] Spatial d) (u : Spatial m) :
    fderiv ℝ (fun v => f v - L v) u = fderiv ℝ f u - L := by
  rw [fderiv_fun_sub (hf u) L.differentiableAt, ContinuousLinearMap.fderiv]

-- The instance `CompleteSpace (Spatial m →L[ℝ] Spatial d)` exceeds the default
-- type-class heartbeat budget; only the search budget is raised.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Second-order spatial affine Poincaré**: implication
type `d1e_SpatialPoincareStatement → d1e_SpatialSecondPoincareStatement`. -/
theorem d1e_spatial_secondPoincare_proof :
    d1e_SpatialPoincareStatement → d1e_SpatialSecondPoincareStatement := by
  intro hP m
  obtain ⟨C₁, hC₁, hP₁⟩ := hP m
  refine ⟨C₁ ^ 2, sq_nonneg _, ?_⟩
  intro d f hf u₀ r hr
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) one_add_one_eq_two.le
  obtain ⟨L, hL⟩ :=
    @hP₁ (Spatial m →L[ℝ] Spatial d) _ _ _ (fderiv ℝ f) hDf u₀ r hr
  have hfd : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hg : ContDiff ℝ 1 (fun v => f v - L v) :=
    (hf.of_le one_le_two).sub L.contDiff
  obtain ⟨a, ha⟩ := @hP₁ (Spatial d) _ _ _ (fun v => f v - L v) hg u₀ r hr
  refine ⟨a, L, ?_⟩
  have hK : 0 ≤ C₁ * r ^ 2 := mul_nonneg hC₁ (sq_nonneg r)
  calc ∫⁻ u in Metric.ball u₀ r, ‖f u - (a + L u)‖ₑ ^ 2
      = ∫⁻ u in Metric.ball u₀ r, ‖(fun v => f v - L v) u - a‖ₑ ^ 2 := by
        refine lintegral_congr fun u => ?_
        show ‖f u - (a + L u)‖ₑ ^ 2 = ‖f u - L u - a‖ₑ ^ 2
        rw [sub_sub, add_comm (L u) a]
    _ ≤ ENNReal.ofReal (C₁ * r ^ 2) *
          ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ (fun v => f v - L v) u‖ₑ ^ 2 := ha
    _ = ENNReal.ofReal (C₁ * r ^ 2) *
          ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ f u - L‖ₑ ^ 2 := by
        congr 1
        exact lintegral_congr fun u => by rw [d1esecondp_fderiv_sub_clm hfd L u]
    _ ≤ ENNReal.ofReal (C₁ * r ^ 2) * (ENNReal.ofReal (C₁ * r ^ 2) *
          ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ (fun v => fderiv ℝ f v) u‖ₑ ^ 2) :=
        mul_le_mul' le_rfl hL
    _ = ENNReal.ofReal (C₁ ^ 2 * r ^ 4) *
          ∫⁻ u in Metric.ball u₀ r, ‖fderiv ℝ (fun v => fderiv ℝ f v) u‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hK,
          show C₁ * r ^ 2 * (C₁ * r ^ 2) = C₁ ^ 2 * r ^ 4 by ring]

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
