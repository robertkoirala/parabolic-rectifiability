import ParabolicRectifiability.Decomposition.Carrier.Transport

/-! # Proof of `fsim_lipschitzWith_baseSimilarity`

`d(σ p, σ q) = R⁻¹ d(p, q)` (`dist_baseSimilarity`) and `‖R • v‖ = R ‖v‖`; the same `L`
works at every base centre. -/

noncomputable section

open scoped NNReal

namespace ParabolicRectifiability.Foundations

theorem fsim_lipschitzWith_baseSimilarity_proof {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (R : ℝ) (hR : 0 < R) (F : SubspaceSpace W → W.orthogonal) (L : ℝ≥0)
    (hF : LipschitzWith L F) :
    LipschitzWith L (fun p => R • F (baseSimilarity W p₀ R p)) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h := hF.dist_le_mul (baseSimilarity W p₀ R p) (baseSimilarity W p₀ R q)
  rw [dist_baseSimilarity W p₀ R hR p q] at h
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]
  calc R * dist (F (baseSimilarity W p₀ R p)) (F (baseSimilarity W p₀ R q))
      ≤ R * (↑L * (R⁻¹ * dist p q)) := mul_le_mul_of_nonneg_left h hR.le
    _ = ↑L * dist p q := by field_simp

end ParabolicRectifiability.Foundations
