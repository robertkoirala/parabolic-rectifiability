import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Metric.Measure

/-! # Zero densities of the diffuse measures at every point

Proof of `E2DiffuseDensityZeroStatement` (`e2_diffuse_densityZero_proof`): the ratio
`μ_c(P(z,r)) / r^k ≤ 2 c ω_n r^{n+2-k}` tends to `0`; squeeze; `liminf ≤ limsup`. The source ball
bound is the hypothesis `E2DiffuseSourceStatement`. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- Pointwise ratio bound at positive radii. -/
theorem e2e2_ratio_le (n k m : ℕ) (hkm : n + 2 = k + m) (c : ℝ) (z : Space n)
    (hball : ∀ (z : Space n) (r : ℝ), 0 < r →
      e2_diffuseBase n (Metric.ball z r) ≤ 2 * omega n * ENNReal.ofReal r ^ (n + 2))
    (r : ℝ) (hr : 0 < r) :
    densityRatio (ENNReal.ofReal c • e2_diffuseBase n) k z r ≤
      ENNReal.ofReal c * (2 * omega n) * ENNReal.ofReal r ^ m := by
  unfold densityRatio
  apply ENNReal.div_le_of_le_mul
  rw [Measure.smul_apply, smul_eq_mul]
  calc ENNReal.ofReal c * e2_diffuseBase n (Metric.ball z r)
      ≤ ENNReal.ofReal c * (2 * omega n * ENNReal.ofReal r ^ (n + 2)) :=
        by gcongr; exact hball z r hr
    _ = ENNReal.ofReal c * (2 * omega n) * ENNReal.ofReal r ^ m * ENNReal.ofReal r ^ k := by
        rw [hkm, pow_add]; ring

/-- For `m ≥ 1`, the bound `c · 2ω_n · r^m` tends to `0` as `r → 0⁺`. -/
theorem e2e2_tendsto_zero (n m : ℕ) (hm : 1 ≤ m) (c : ℝ) :
    Tendsto (fun r : ℝ => ENNReal.ofReal c * (2 * omega n) * ENNReal.ofReal r ^ m)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hC : ENNReal.ofReal c * (2 * omega n) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by norm_num) (omega_lt_top n).ne)
  have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ m) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => ENNReal.ofReal r ^ m :=
      (ENNReal.continuous_pow m).comp ENNReal.continuous_ofReal
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [ENNReal.ofReal_zero, zero_pow (Nat.pos_iff_ne_zero.mp hm)] using this
  have := ENNReal.Tendsto.const_mul h1 (Or.inr hC)
  simpa using this

/-- For `k < n + 2`, both `k`-densities of `μ_c = c ω` vanish at every point. -/
theorem e2_diffuse_densityZero_proof : E2DiffuseDensityZeroStatement := by
  intro hsrc n k hk c z
  obtain ⟨_, _, hball⟩ := hsrc n
  have hkm : n + 2 = k + (n + 2 - k) := by omega
  have hm : 1 ≤ n + 2 - k := by omega
  have hev : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      densityRatio (ENNReal.ofReal c • e2_diffuseBase n) k z r ≤
        ENNReal.ofReal c * (2 * omega n) * ENNReal.ofReal r ^ (n + 2 - k) :=
    eventually_nhdsWithin_of_forall fun r hr => e2e2_ratio_le n k _ hkm c z hball r hr
  have hup : upperDensity (ENNReal.ofReal c • e2_diffuseBase n) k z = 0 := by
    apply le_zero_iff.mp
    calc upperDensity (ENNReal.ofReal c • e2_diffuseBase n) k z
        ≤ limsup (fun r : ℝ => ENNReal.ofReal c * (2 * omega n) * ENNReal.ofReal r ^ (n + 2 - k))
            (𝓝[>] (0 : ℝ)) := Filter.limsup_le_limsup hev
      _ = 0 := (e2e2_tendsto_zero n _ hm c).limsup_eq
  refine ⟨?_, hup⟩
  apply le_zero_iff.mp
  calc lowerDensity (ENNReal.ofReal c • e2_diffuseBase n) k z
      ≤ upperDensity (ENNReal.ofReal c • e2_diffuseBase n) k z := Filter.liminf_le_limsup
    _ = 0 := hup

end ParabolicRectifiability.Examples
