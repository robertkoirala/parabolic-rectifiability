import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements

/-! # Uniform beta lower bound for the diffuse base

From a uniform lower bound on the fitting integrals, the normalized beta numbers of the diffuse
base are bounded below by a positive constant on the box and the band of radii `[1/32, 1/16]`
(`e2_diffuse_betaLower_proof`). The proof uses `ENNReal.mul_iInf_of_ne`, `le_iInf`, and the real inequality
`r^{-k-p} · a r^{n+2+p} = a r^α ≥ a 32^{-α}` on `[1/32, 1/16]`; an empty family gives `⊤`. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The real inequality: `a (1/32)^α ≤ r⁻¹^(k+p) · (a r^(n+2+p))` for `r ≥ 1/32`, `α = n+2-k > 0`. -/
theorem e2d5_real_bound (n k : ℕ) (p a r : ℝ) (ha : 0 < a) (hr : 1 / 32 ≤ r) (hα : k < n + 2) :
    a * (1 / 32 : ℝ) ^ ((n : ℝ) + 2 - k) ≤ (r⁻¹) ^ ((k : ℝ) + p) * (a * r ^ ((n : ℝ) + 2 + p)) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hα' : (0 : ℝ) < (n : ℝ) + 2 - k := by
    have : (k : ℝ) < n + 2 := by exact_mod_cast hα
    linarith
  have h1 : (r⁻¹) ^ ((k : ℝ) + p) * r ^ ((n : ℝ) + 2 + p) = r ^ ((n : ℝ) + 2 - k) := by
    rw [Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le, ← Real.rpow_add hr0]
    congr 1; ring
  have h2 : (r⁻¹) ^ ((k : ℝ) + p) * (a * r ^ ((n : ℝ) + 2 + p)) = a * r ^ ((n : ℝ) + 2 - k) := by
    rw [← h1]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) hr hα'.le) ha.le

theorem e2_diffuse_betaLower_proof : E2DiffuseBetaLowerStatement := by
  intro n k T p hk hp ⟨a, ha, hfit⟩
  refine ⟨a * (1 / 32 : ℝ) ^ ((n : ℝ) + 2 - k), by positivity, ?_⟩
  intro z _ r hr
  have hr1 : 1 / 32 ≤ r := hr.1
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  unfold betaPow
  rw [ite_eq_left hr0]
  have hne0 : ((ENNReal.ofReal r)⁻¹) ^ ((k : ℝ) + p) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.rpow_pos
    · exact ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
    · exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr0).ne'
  have hneT : ((ENNReal.ofReal r)⁻¹) ^ ((k : ℝ) + p) ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr0).ne'
  rw [ENNReal.mul_iInf_of_ne hne0 hneT]
  refine le_iInf fun L => ?_
  refine le_trans ?_ (mul_le_mul' (le_refl _) (hfit L z ‹_› r hr))
  have hinv : (ENNReal.ofReal r)⁻¹ = ENNReal.ofReal r⁻¹ := (ENNReal.ofReal_inv_of_pos hr0).symm
  have hk0 : (0 : ℝ) ≤ (k : ℝ) + p := by positivity
  rw [hinv, ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hr0),
    ENNReal.ofReal_rpow_of_pos hr0, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (e2d5_real_bound n k p a r ha hr1 hk)

end ParabolicRectifiability.Examples
