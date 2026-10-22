import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements
import ParabolicRectifiability.Geometry.ModelDistance
import ParabolicRectifiability.Metric.BaseVolume

/-! # Horizontal lower fit for the diffuse base

Proof of `E2DiffuseHorizontalLowerStatement` (the lower bound against horizontal models),
`e2_diffuse_horizontalLower_proof`. The half intervals used below are open.

Route. For `z = (x,t) ∈ D`, `r ∈ I` and a horizontal model at time `τ`, take the **open** half
interval `J = (t + r²/2, t + r²)` if `τ ≤ t`, else `J = (t - r², t - r²/2)`. On `B(x,r) × J`,
`|s - t| < r²` (so the rectangle lies in `P(z,r) ⊆ P(0,1/4)`, where `ω = λ`) and
`|s - τ| ≥ r²/2`, so `d_P(w,L) ≥ r 2^{-1/2}` by `HorizontalModel.infEDist_eq_projection` and
`HorizontalModel.dist_projection_sq`. The rectangle has volume `ω_n r^n · r²/2`
(`parabolicVolume_apply`, `Measure.prod_prod`, the spatial ball volume), so the integral is at
least `ω_n 2^{-1-p/2} r^{n+2+p}`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The opposite open half interval of length `r²/2`: inside `(t - r², t + r²)` and at
temporal distance at least `r²/2` from `τ`. -/
theorem e2d3_halfInterval (t τ r : ℝ) :
    ∃ u : ℝ, ∀ s ∈ Ioo u (u + r ^ 2 / 2), |s - t| < r ^ 2 ∧ r ^ 2 / 2 ≤ |s - τ| := by
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  by_cases h : τ ≤ t
  · refine ⟨t + r ^ 2 / 2, fun s hs => ⟨abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      le_abs.mpr (Or.inl (by linarith [hs.1]))⟩⟩
  · push Not at h
    refine ⟨t - r ^ 2, fun s hs => ⟨abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      le_abs.mpr (Or.inr (by linarith [hs.2]))⟩⟩

/-- A point at temporal distance at least `r²/2` from the model time is at parabolic distance
at least `r 2^{-1/2}` from the horizontal model. -/
theorem e2d3_le_infEDist {n k : ℕ} (L : HorizontalModel n k) (w : Space n) {r : ℝ}
    (hr : 0 < r) (hw : r ^ 2 / 2 ≤ |w.2.val - L.time|) :
    ENNReal.ofReal (r * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Metric.infEDist w L.toSet := by
  rw [L.infEDist_eq_projection, edist_dist]
  apply ENNReal.ofReal_le_ofReal
  have hsq := L.dist_projection_sq w.1 w.2.val
  have hw' : point w.1 w.2.val = w := rfl
  rw [hw'] at hsq
  have h2 : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 2⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hd : 0 ≤ dist w (L.projection w) := dist_nonneg
  have hc : 0 ≤ r * (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hr.le (Real.rpow_nonneg (by norm_num) _)
  have hle : (r * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 ≤ dist w (L.projection w) ^ 2 := by
    rw [hsq, mul_pow, h2]
    exact le_trans (by linarith) (le_max_right _ _)
  exact (pow_le_pow_iff_left₀ hc hd two_ne_zero).mp hle

/-- The real identity `ω 2^{-1-p/2} r^{n+2+p} = (r 2^{-1/2})^p · (ω r^n · r²/2)`. -/
theorem e2d3_real_identity (ω0 r p : ℝ) (n : ℕ) (hr : 0 < r) :
    ω0 * (2 : ℝ) ^ (-1 - p / 2) * r ^ ((n : ℝ) + 2 + p) =
      (r * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ p * (ω0 * r ^ n * (r ^ 2 / 2)) := by
  have h2 : (0 : ℝ) < 2 := two_pos
  rw [Real.mul_rpow hr.le (Real.rpow_nonneg h2.le _), ← Real.rpow_mul h2.le,
    Real.rpow_add hr, Real.rpow_add hr, Real.rpow_natCast, Real.rpow_two,
    show (-1 - p / 2 : ℝ) = -1 + (-(1 / 2) * p) by ring, Real.rpow_add h2, Real.rpow_neg_one]
  ring

/-- The same identity after `ENNReal.ofReal`. -/
theorem e2d3_ennreal_identity (ω0 r p : ℝ) (n : ℕ) (hω : 0 ≤ ω0) (hr : 0 < r)
    (hp : 0 ≤ p) :
    ENNReal.ofReal (ω0 * (2 : ℝ) ^ (-1 - p / 2)) * ENNReal.ofReal r ^ ((n : ℝ) + 2 + p) =
      ENNReal.ofReal (r * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ p *
        (ENNReal.ofReal ω0 * ENNReal.ofReal r ^ n * ENNReal.ofReal (r ^ 2 / 2)) := by
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  rw [ENNReal.ofReal_rpow_of_pos hr, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hr.le h2) hp,
    ← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_mul (mul_nonneg hω (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)),
    ← ENNReal.ofReal_mul hω, ← ENNReal.ofReal_mul (mul_nonneg hω (pow_nonneg hr.le _)),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg hr.le h2) _),
    e2d3_real_identity ω0 r p n hr]

/-- Horizontal lower fit for the diffuse base (`E2DiffuseHorizontalLowerStatement`). -/
theorem e2_diffuse_horizontalLower_proof : E2DiffuseHorizontalLowerStatement := by
  intro n k p hp
  obtain ⟨ω0, hω0, hωe⟩ : ∃ ω0 : ℝ, 0 < ω0 ∧ omega n = ENNReal.ofReal ω0 :=
    ⟨(omega n).toReal, ENNReal.toReal_pos (omega_pos n).ne' (omega_lt_top n).ne,
      (ENNReal.ofReal_toReal (omega_lt_top n).ne).symm⟩
  refine ⟨ω0 * (2 : ℝ) ^ (-1 - p / 2), mul_pos hω0 (Real.rpow_pos_of_pos two_pos _), ?_⟩
  intro L z hz r hr
  have hr0 : 0 < r := by linarith [hr.1]
  obtain ⟨u, hu⟩ := e2d3_halfInterval z.2.val L.time r
  -- the coordinate rectangle `B(x,r) × J` and its preimage in parabolic space
  have hSm : MeasurableSet ((coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball z.1 r ×ˢ Ioo u (u + r ^ 2 / 2))) :=
    (coordinatesMeasurableEquiv n).measurable (measurableSet_ball.prod measurableSet_Ioo)
  have hSball : (coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball z.1 r ×ˢ Ioo u (u + r ^ 2 / 2)) ⊆ Metric.ball z r := by
    rw [← coordinates_preimage_ball_rectangle z r hr0]
    refine preimage_mono (prod_mono subset_rfl fun s hs => ?_)
    have h := abs_lt.mp (hu s hs).1
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hball : Metric.ball z r ⊆ Metric.ball (point 0 0) (1 / 4) := by
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    have hz' : dist z (point 0 0) < 1 / 16 := Metric.mem_ball.mp hz
    have hr1 : r ≤ 1 / 16 := hr.2
    calc dist w (point 0 0) ≤ dist w z + dist z (point 0 0) := dist_triangle _ _ _
      _ < 1 / 4 := by linarith
  have hvolS : e2_diffuseBase n ((coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball z.1 r ×ˢ Ioo u (u + r ^ 2 / 2))) =
      ENNReal.ofReal ω0 * ENNReal.ofReal r ^ n * ENNReal.ofReal (r ^ 2 / 2) := by
    rw [Measure.restrict_apply hSm, inter_eq_left.mpr (hSball.trans hball), parabolicVolume_apply,
      MeasurableEquiv.symm_preimage_preimage, coordinateVolume, Measure.prod_prod,
      Real.volume_Ioo, volume_spatial_ball z.1 hr0, hωe, show u + r ^ 2 / 2 - u = r ^ 2 / 2 by ring]
  have hc : ∀ w ∈ (coordinatesMeasurableEquiv n) ⁻¹'
      (Metric.ball z.1 r ×ˢ Ioo u (u + r ^ 2 / 2)),
      ENNReal.ofReal (r * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ p ≤ Metric.infEDist w L.toSet ^ p := by
    intro w hw
    simp only [mem_preimage, coordinatesMeasurableEquiv_apply, mem_prod] at hw
    exact ENNReal.rpow_le_rpow (e2d3_le_infEDist L w hr0 (hu w.2.val hw.2).2) hp.le
  calc ENNReal.ofReal (ω0 * (2 : ℝ) ^ (-1 - p / 2)) * ENNReal.ofReal r ^ ((n : ℝ) + 2 + p)
      = ENNReal.ofReal (r * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ p *
          e2_diffuseBase n ((coordinatesMeasurableEquiv n) ⁻¹'
            (Metric.ball z.1 r ×ˢ Ioo u (u + r ^ 2 / 2))) := by
        rw [hvolS]
        exact e2d3_ennreal_identity ω0 r p n hω0.le hr0 hp.le
    _ = ∫⁻ _ in (coordinatesMeasurableEquiv n) ⁻¹'
          (Metric.ball z.1 r ×ˢ Ioo u (u + r ^ 2 / 2)),
          ENNReal.ofReal (r * (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ p ∂(e2_diffuseBase n) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ w in (coordinatesMeasurableEquiv n) ⁻¹'
          (Metric.ball z.1 r ×ˢ Ioo u (u + r ^ 2 / 2)),
          Metric.infEDist w L.toSet ^ p ∂(e2_diffuseBase n) :=
        setLIntegral_mono' hSm hc
    _ ≤ ∫⁻ w in Metric.ball z r, Metric.infEDist w L.toSet ^ p ∂(e2_diffuseBase n) :=
        lintegral_mono_set hSball

end ParabolicRectifiability.Examples
