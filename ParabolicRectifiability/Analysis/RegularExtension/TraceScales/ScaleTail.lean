import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Geometry.SubspaceCoordinates
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! # The zero comparison above the density radius

`lintegral_Ioi_traceErrorSq_le_of_subset_closedBall_proof` bounds the integral of the trace
error over the scales above the density radius, for a set contained in a closed ball.

Route: the constant competitor `(f p, 0)` gives, for `r > 0`,
`γ_P(p,r)^2 ≤ r^(-(k+2)) (L·2ρ)^2 |P|`, `k = m + 2`, and `|P| ≤ |P_b(x,2ρ)| = 2ω_m (2ρ)^k`.
The exact inverse-power integral `∫_ρ^∞ r^(-(k+2)) dr/r = ρ^(-(k+2))/(k+2)` then gives the
constant `C = 2 ω_m 2^(m+4)/(m+4)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability

variable {n : ℕ}

/-- The pointwise zero comparison: the constant competitor `f p` on a piece of diameter
at most `2ρ`. -/
theorem rx1_traceErrorSq_le_of_subset_closedBall (W : Submodule ℝ (Spatial n))
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (P : Set (SubspaceSpace W)) (f : SubspaceSpace W → Y) (L : ℝ≥0)
    (x : SubspaceSpace W) (ρ : ℝ) (hP : IsCompact P) (hρ : 0 < ρ)
    (hPx : P ⊆ Metric.closedBall x ρ) (hf : LipschitzOnWith L f P)
    {p : SubspaceSpace W} (hp : p ∈ P) {r : ℝ} (hr : 0 < r) :
    traceErrorSq (intrinsicParabolicVolume W) P f p r ≤
      (ENNReal.ofReal r)⁻¹ ^ (baseDimension W + 2) *
        ENNReal.ofReal (((L : ℝ) * (2 * ρ)) ^ 2 *
          (2 * (omega (Module.finrank ℝ W)).toReal * (2 * ρ) ^ (Module.finrank ℝ W + 2))) := by
  have hmeas : MeasurableSet P := hP.isClosed.measurableSet
  have hpt : ∀ q ∈ P, ‖f q - (f p + (0 : W →L[ℝ] Y) q.1)‖ₑ ^ 2 ≤
      ENNReal.ofReal (((L : ℝ) * (2 * ρ)) ^ 2) := by
    intro q hq
    rw [zero_apply, add_zero, ← edist_eq_enorm_sub]
    have h1 : edist (f q) (f p) ≤ L * edist q p := hf hq hp
    have hxq := hPx hq
    have hxp := hPx hp
    rw [Metric.mem_closedBall] at hxq hxp
    have h2 : dist q p ≤ 2 * ρ := by
      have := dist_triangle_right q p x
      linarith
    have h3 : edist q p ≤ ENNReal.ofReal (2 * ρ) := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal h2
    calc edist (f q) (f p) ^ 2 ≤ ((L : ℝ≥0∞) * ENNReal.ofReal (2 * ρ)) ^ 2 := by
          gcongr
          exact h1.trans (by gcongr)
      _ = ENNReal.ofReal (((L : ℝ) * (2 * ρ)) ^ 2) := by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (NNReal.coe_nonneg L),
            ENNReal.ofReal_coe_nnreal]
  have hfit : affineFitIntegral ((intrinsicParabolicVolume W).restrict P) f (f p) 0 p r ≤
      ENNReal.ofReal (((L : ℝ) * (2 * ρ)) ^ 2) * intrinsicParabolicVolume W P := by
    unfold affineFitIntegral
    calc ∫⁻ q in Metric.ball p r, ‖f q - (f p + (0 : W →L[ℝ] Y) q.1)‖ₑ ^ 2
          ∂(intrinsicParabolicVolume W).restrict P
        ≤ ∫⁻ q, ‖f q - (f p + (0 : W →L[ℝ] Y) q.1)‖ₑ ^ 2
          ∂(intrinsicParabolicVolume W).restrict P := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ _ in P, ENNReal.ofReal (((L : ℝ) * (2 * ρ)) ^ 2) ∂intrinsicParabolicVolume W :=
          setLIntegral_mono' hmeas hpt
      _ = _ := setLIntegral_const _ _
  have hvol : intrinsicParabolicVolume W P ≤
      ENNReal.ofReal (2 * (omega (Module.finrank ℝ W)).toReal *
        (2 * ρ) ^ (Module.finrank ℝ W + 2)) := by
    calc intrinsicParabolicVolume W P
        ≤ intrinsicParabolicVolume W (Metric.ball x (2 * ρ)) :=
          measure_mono (hPx.trans (Metric.closedBall_subset_ball (by linarith)))
      _ = 2 * omega (Module.finrank ℝ W) * ENNReal.ofReal (2 * ρ) ^ (Module.finrank ℝ W + 2) :=
          intrinsicParabolicVolume_ball W x (2 * ρ) (by positivity)
      _ = _ := by
          rw [ENNReal.ofReal_mul
              (show (0 : ℝ) ≤ 2 * (omega (Module.finrank ℝ W)).toReal by positivity),
            ENNReal.ofReal_pow (by positivity)]
          congr 1
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_toReal (omega_lt_top _).ne]
  calc traceErrorSq (intrinsicParabolicVolume W) P f p r
      ≤ (ENNReal.ofReal r)⁻¹ ^ (baseDimension W + 2) *
          affineFitIntegral ((intrinsicParabolicVolume W).restrict P) f (f p) 0 p r :=
        affineErrorSq_le_fitIntegral _ _ _ hr _ _
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (baseDimension W + 2) *
          (ENNReal.ofReal (((L : ℝ) * (2 * ρ)) ^ 2) *
            ENNReal.ofReal (2 * (omega (Module.finrank ℝ W)).toReal *
              (2 * ρ) ^ (Module.finrank ℝ W + 2))) := by
        gcongr
        exact hfit.trans (by gcongr)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

/-- **Trace error above the density radius**
(`lintegral_Ioi_traceErrorSq_le_of_subset_closedBall`). The constant is `C = 2 ω_m 2^(m+4)/(m+4)`. -/
theorem lintegral_Ioi_traceErrorSq_le_of_subset_closedBall_proof (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (W : Submodule ℝ (Spatial n)), Module.finrank ℝ W = m →
      ∀ (P : Set (SubspaceSpace W)) (f : SubspaceSpace W → W.orthogonal) (L : ℝ≥0)
        (x : SubspaceSpace W) (ρ : ℝ), IsCompact P → 0 < ρ →
        P ⊆ Metric.closedBall x ρ → LipschitzOnWith L f P → ∀ p ∈ P,
          ∫⁻ r in Ioi ρ, traceErrorSq (intrinsicParabolicVolume W) P f p r ∂scaleMeasure ≤
            ENNReal.ofReal (C * (L : ℝ) ^ 2) := by
  refine ⟨2 * (omega m).toReal * 2 ^ (m + 4) / ((m : ℝ) + 4), by positivity, ?_⟩
  intro n W hW P f L x ρ hP hρ hPx hf p hp
  subst hW
  have hbd : baseDimension W + 2 = Module.finrank ℝ W + 4 := by
    unfold baseDimension
    omega
  set M : ℝ := ((L : ℝ) * (2 * ρ)) ^ 2 *
    (2 * (omega (Module.finrank ℝ W)).toReal * (2 * ρ) ^ (Module.finrank ℝ W + 2)) with hM
  have hM0 : 0 ≤ M := by positivity
  calc ∫⁻ r in Ioi ρ, traceErrorSq (intrinsicParabolicVolume W) P f p r ∂scaleMeasure
      ≤ ∫⁻ r in Ioi ρ, (ENNReal.ofReal r)⁻¹ ^ (baseDimension W + 2) * ENNReal.ofReal M
          ∂scaleMeasure :=
        setLIntegral_mono' measurableSet_Ioi fun r hr =>
          rx1_traceErrorSq_le_of_subset_closedBall W P f L x ρ hP hρ hPx hf hp
            (hρ.trans hr)
    _ = (∫⁻ r in Ioi ρ, (ENNReal.ofReal r)⁻¹ ^ (baseDimension W + 2) ∂scaleMeasure) *
          ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((ρ ^ (baseDimension W + 2))⁻¹ / ((baseDimension W + 2 : ℕ) : ℝ)) *
          ENNReal.ofReal M := by
        rw [lintegral_inv_pow_Ioi_scaleMeasure _ (by omega) hρ]
    _ = ENNReal.ofReal ((ρ ^ (baseDimension W + 2))⁻¹ / ((baseDimension W + 2 : ℕ) : ℝ) *
          M) := (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (2 * (omega (Module.finrank ℝ W)).toReal *
          2 ^ (Module.finrank ℝ W + 4) / ((Module.finrank ℝ W : ℝ) + 4) * (L : ℝ) ^ 2) := by
        congr 1
        rw [hbd, hM]
        have hρ0 : ρ ≠ 0 := hρ.ne'
        push_cast
        field_simp
        ring

end ParabolicRectifiability
