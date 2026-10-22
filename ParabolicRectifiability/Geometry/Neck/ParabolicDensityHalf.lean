import ParabolicRectifiability.Metric.Measure
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Lebesgue density one half for parabolic balls

The bridge for the vertical core-density statement `vertical_coreLowerDensity_of_parametrization`
(vertical parameter space `ℝ^m × ℝ`).

* `nk5_isUnifLocDoublingMeasure_parabolicVolume`: `parabolicVolume m` is uniformly locally
  doubling with constant `2^(m+2)`, since closed parabolic balls have volume
  `2 ω_m r^(m+2)` (`parabolicVolume_closedBall`).
* `nk5_ae_parabolicVolume_density_half`: at almost every point `p` of an arbitrary set `S`,
  `|P_b(p,r)| ≤ 2 |S ∩ P_b(p,r)|` for every sufficiently small radius `r > 0`.

The differentiation basis is the family of **anisotropic parabolic balls** of the metric
`max(|u-v|, √|t-s|)`, through mathlib's density theorem for uniformly locally doubling
measures (`IsUnifLocDoublingMeasure`); no Euclidean differentiation is substituted. The
theorem gives closed balls along the full filter `𝓝[>] 0`; parabolic spheres are
volume-null (`parabolicVolume_sphere`), so open balls follow.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace NeckHubTree

/-- The parabolic volume is uniformly locally doubling, with constant `2^(m+2)`. Kept as a
theorem (not a global instance); it is installed locally where needed. -/
theorem nk5_isUnifLocDoublingMeasure_parabolicVolume (m : ℕ) :
    IsUnifLocDoublingMeasure (parabolicVolume m) := by
  refine ⟨⟨2 ^ (m + 2), eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) x => ?_⟩⟩
  rw [parabolicVolume_closedBall x (2 * ε) (by positivity), parabolicVolume_closedBall x ε hε.le,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow, ENNReal.ofReal_ofNat]
  push_cast
  apply le_of_eq
  ring

/-- **Parabolic density one half.** For an arbitrary set `S ⊆ ℝ^m × ℝ` (not necessarily
measurable), at `parabolicVolume`-almost every point `p` of `S` the relative volume of `S`
in every sufficiently small open parabolic ball about `p` is at least one half. The case
`m = 0` (the snowflaked time line) is included. -/
theorem nk5_ae_parabolicVolume_density_half {m : ℕ} (S : Set (Space m)) :
    ∀ᵐ p ∂(parabolicVolume m).restrict S, ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        parabolicVolume m (Metric.ball p r) ≤ 2 * parabolicVolume m (S ∩ Metric.ball p r) := by
  have := nk5_isUnifLocDoublingMeasure_parabolicVolume m
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (parabolicVolume m) 1).ae_tendsto_measure_inter_div
    S] with p hp
  -- Closed parabolic balls centred at `p`, along the full filter `𝓝[>] 0`.
  have hu : Tendsto (fun r => parabolicVolume m (S ∩ Metric.closedBall p r) /
      parabolicVolume m (Metric.closedBall p r)) (𝓝[>] 0) (𝓝 1) :=
    hp.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (parabolicVolume m) (K := 1)
      (fun _ => p) id tendsto_id
      (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) =>
        Metric.mem_closedBall_self (by simpa using hr.le)))
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (2 : ℝ≥0∞)⁻¹ < parabolicVolume m (S ∩ Metric.closedBall p r) /
        parabolicVolume m (Metric.closedBall p r) :=
    hu.eventually_const_lt (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  obtain ⟨ε, hε, hεr⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨ε / 2, half_pos hε, fun r hr hrε => ?_⟩
  have hdist : dist r 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    linarith
  have hlt := hεr hdist (show r ∈ Ioi (0 : ℝ) from hr)
  -- Open and closed parabolic balls have the same positive finite volume.
  have hball : parabolicVolume m (Metric.ball p r) = parabolicVolume m (Metric.closedBall p r) := by
    rw [parabolicVolume_ball p r hr, parabolicVolume_closedBall p r hr.le]
  have hpos : parabolicVolume m (Metric.closedBall p r) ≠ 0 := by
    rw [parabolicVolume_closedBall p r hr.le]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos m).ne')
      (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne')
  have hfin : parabolicVolume m (Metric.closedBall p r) ≠ ∞ := by
    rw [parabolicVolume_closedBall p r hr.le]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hpos) (Or.inl hfin)] at hlt
  -- The parabolic sphere is null, so the closed ball can be replaced by the open ball.
  have hsphere : parabolicVolume m (S ∩ Metric.closedBall p r) ≤
      parabolicVolume m (S ∩ Metric.ball p r) := by
    calc parabolicVolume m (S ∩ Metric.closedBall p r)
        ≤ parabolicVolume m ((S ∩ Metric.ball p r) ∪ Metric.sphere p r) := by
          refine measure_mono fun y hy => ?_
          rw [← Metric.ball_union_sphere] at hy
          rcases hy.2 with h | h
          · exact Or.inl ⟨hy.1, h⟩
          · exact Or.inr h
      _ ≤ parabolicVolume m (S ∩ Metric.ball p r) + parabolicVolume m (Metric.sphere p r) :=
          measure_union_le _ _
      _ = parabolicVolume m (S ∩ Metric.ball p r) := by
          rw [parabolicVolume_sphere, add_zero]
  calc parabolicVolume m (Metric.ball p r)
      = 2 * ((2 : ℝ≥0∞)⁻¹ * parabolicVolume m (Metric.closedBall p r)) := by
        rw [hball, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * parabolicVolume m (S ∩ Metric.closedBall p r) := by gcongr
    _ ≤ 2 * parabolicVolume m (S ∩ Metric.ball p r) := by gcongr

end NeckHubTree

end ParabolicRectifiability
