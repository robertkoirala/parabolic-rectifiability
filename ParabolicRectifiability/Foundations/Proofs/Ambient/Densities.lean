import ParabolicRectifiability.Characterization.Proofs.GraphSource.DensityBounds
import ParabolicRectifiability.Foundations.Proofs.AmbientCover
import ParabolicRectifiability.Metric.BaseVolume

/-! # Differentiation with respect to volume

Proof of `AmbientAbsolutelyContinuousDensityStatement`:

1. `μ ≪ L^{n+1}` and `(2 ω_n)⁻¹ • L^{n+1} ≤ H_P^{n+2}` (`parabolicVolume_smul_le_hausdorff`)
   give `μ ≪ H_P^{n+2}`;
2. the zero graph of `ambient_zero_graph_cover_all_proof` is a full general regular vertical
   graph of dimension `n + 2` with image `univ`;
3. `b2_graph_density_bounds` on that graph gives `0 < Θ_*` and `Θ^* < ∞` `μ`-a.e.;
4. `lowerDensity_le_upperDensity` gives the other two bounds.

Neither the main characterization theorem nor the absolute-continuity bridge is used. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.Characterization

/-- The parabolic volume is absolutely continuous with respect to `H_P^{n+2}`. -/
theorem f2i_parabolicVolume_ac_hausdorffP (n : ℕ) :
    parabolicVolume n ≪ hausdorffP n (n + 2) := by
  intro s hs
  have hc : (2 * omega n)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top (by norm_num) (omega_lt_top n).ne)
  have hle : ((2 * omega n)⁻¹ • parabolicVolume n) s ≤ hausdorffP n (n + 2) s :=
    Measure.le_iff'.1 (parabolicVolume_smul_le_hausdorff n) s
  rw [hs, nonpos_iff_eq_zero, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at hle
  exact hle.resolve_left hc

/-- Differentiation with respect to volume: exactly
`AmbientAbsolutelyContinuousDensityStatement`. -/
theorem f2i_ambientDensities_proof : AmbientAbsolutelyContinuousDensityStatement := by
  intro n hn μ hfin hreg hac
  have hacH : μ ≪ hausdorffP n (n + 2) := hac.trans (f2i_parabolicVolume_ac_hausdorffP n)
  obtain ⟨G, -, hG⟩ := (ambient_zero_graph_cover_all_proof n hn).1 1 one_pos
  have h := (b2_graph_density_bounds n hn (n + 2) (by omega) le_rfl μ hfin hreg hacH).2 1 G
  filter_upwards [h] with z hz
  obtain ⟨hlow, hup⟩ := hz (by rw [hG]; exact Set.mem_univ z)
  have hle := lowerDensity_le_upperDensity μ (n + 2) z
  exact ⟨⟨hlow, lt_of_le_of_lt hle hup⟩, ⟨lt_of_lt_of_le hlow hle, hup⟩⟩

end ParabolicRectifiability.Foundations
