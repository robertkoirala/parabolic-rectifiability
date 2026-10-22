import ParabolicRectifiability.Examples.Proofs.DensityTests.DensityTestStatements
import ParabolicRectifiability.Metric.BaseVolume

/-! # Ambient nullity of sets of finite `H_P^k` measure

For `k < n + 2`, a set of finite `H_P^k` measure has `H_P^{n+2}` measure zero
(`hausdorffMeasure_zero_or_top`), hence zero parabolic volume
(`parabolicVolume_smul_le_hausdorff`). Consequently the diffuse measures `μ_c = c ω` are
absolutely continuous with respect to `H_P^k`, vanish on σ-finite `H_P^k` sets, and every
`ν ≤ μ_c` carried by a set of finite `H_P^k` measure is zero (`e2_ambientNull_proof`).
All three consequences hold on arbitrary sets. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- For `k < n + 2`, a set of finite `H_P^k` measure has zero parabolic volume. -/
theorem e2e3_volume_null (n k : ℕ) (hk : k < n + 2) (K : Set (Space n))
    (hK : hausdorffP n k K < ⊤) : parabolicVolume n K = 0 := by
  have hlt : (k : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hk
  have h0 : hausdorffP n (n + 2) K = 0 := by
    rcases Measure.hausdorffMeasure_zero_or_top hlt K with h | h
    · exact h
    · exact absurd hK (by rw [hausdorffP_eq, h]; exact lt_irrefl _)
  have hle := parabolicVolume_smul_le_hausdorff n K
  rw [h0, Measure.smul_apply, smul_eq_mul] at hle
  have hne : (2 * omega n)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top (by norm_num) (omega_lt_top n).ne)
  have : (2 * omega n)⁻¹ * parabolicVolume n K = 0 := le_antisymm hle zero_le
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hne
  · exact h

/-- For `k < n + 2`, the diffuse measure `c ω` vanishes on every set of finite `H_P^k`
measure. -/
theorem e2e3_smul_null (n k : ℕ) (hk : k < n + 2) (c : ℝ) (N : Set (Space n))
    (hN : hausdorffP n k N < ⊤) : (ENNReal.ofReal c • e2_diffuseBase n) N = 0 := by
  have h1 : e2_diffuseBase n N ≤ parabolicVolume n N :=
    Measure.le_iff'.mp (Measure.restrict_le_self) N
  have h2 : e2_diffuseBase n N = 0 := by
    have := e2e3_volume_null n k hk N hN
    rw [this] at h1
    exact le_antisymm h1 zero_le
  rw [Measure.smul_apply, h2, smul_zero]

/-- Ambient nullity of sets of finite `H_P^k` measure and its three consequences for `c ω`. -/
theorem e2e3_ambientNull_core : E2AmbientNullStatement := by
  intro n k hk
  refine ⟨fun K hK => e2e3_volume_null n k hk K hK, fun c => ⟨?_, ?_, ?_⟩⟩
  · intro N hN
    exact e2e3_smul_null n k hk c N (by rw [hN]; exact ENNReal.zero_lt_top)
  · intro A hA
    exact measure_iUnion_null fun i => e2e3_smul_null n k hk c (A i) (hA i)
  · intro ν hν K hK hKc
    have hK0 : ν K = 0 := by
      have h1 : ν K ≤ (ENNReal.ofReal c • e2_diffuseBase n) K := hν K
      rw [e2e3_smul_null n k hk c K hK] at h1
      exact le_antisymm h1 zero_le
    have : ν univ = 0 := by
      refine le_antisymm ?_ zero_le
      calc ν univ ≤ ν K + ν Kᶜ := measure_univ_le_add_compl K
        _ = 0 := by rw [hK0, hKc, add_zero]
    exact Measure.measure_univ_eq_zero.mp this

/-- **Ambient nullity.** For `k < n + 2`, sets of finite `H_P^k` measure are null for the
parabolic volume, and the diffuse measures `c ω` are absolutely continuous with respect to
`H_P^k` and charge no σ-finite `H_P^k` set. -/
theorem e2_ambientNull_proof : E2AmbientNullStatement := e2e3_ambientNull_core

end ParabolicRectifiability.Examples
