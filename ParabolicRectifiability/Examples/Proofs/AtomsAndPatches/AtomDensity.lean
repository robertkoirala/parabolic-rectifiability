import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Foundations.Density

/-!
# Densities of an atom

For `k ≥ 1` and `A > 0` the ratio of `A δ_z` at `z` is `A r^{-k}`, which tends to `⊤` as `r → 0⁺`,
so `liminf` and `limsup` are `⊤`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The ratio of the atom `A δ_z` at `z` tends to `⊤` along `𝓝[>] 0`. -/
theorem e2f3_tendsto_top {n k : ℕ} (hk : 1 ≤ k) (z : Space n) {A : ℝ} (hA : 0 < A) :
    Tendsto (densityRatio (ENNReal.ofReal A • Measure.dirac z) k z) (𝓝[>] (0 : ℝ)) (𝓝 ⊤) := by
  have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ k) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => ENNReal.ofReal r ^ k :=
      (ENNReal.continuous_pow k).comp ENNReal.continuous_ofReal
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [ENNReal.ofReal_zero, zero_pow (Nat.pos_iff_ne_zero.mp hk)] using this
  have h1 : Tendsto (fun r : ℝ => (ENNReal.ofReal r ^ k)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 ⊤) := by
    have := tendsto_inv_iff.2 h0
    simpa using this
  have hA' : ENNReal.ofReal A ≠ 0 := by simpa using hA
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal A) h1 (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top hA'] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hball : (Measure.dirac z) (Metric.ball z r) = 1 := by
    rw [Measure.dirac_apply' _ Metric.isOpen_ball.measurableSet]
    simp [Metric.mem_ball, hr']
  simp [densityRatio, hball, div_eq_mul_inv]

/-- **Atom densities.** For `k ≥ 1` and `A > 0`, the atom `A δ_z` has infinite lower and upper
`k`-density at `z`. -/
theorem e2_atom_density_proof : E2AtomDensityStatement := by
  intro n k hk z A hA
  have h := e2f3_tendsto_top hk z hA
  exact ⟨h.liminf_eq, h.limsup_eq⟩

end ParabolicRectifiability.Examples
