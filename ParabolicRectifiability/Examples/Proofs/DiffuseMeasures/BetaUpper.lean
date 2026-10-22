import ParabolicRectifiability.Examples.Proofs.DensityTests.DiffuseEstimateStatements
import ParabolicRectifiability.Geometry.AdmissibleModels

/-! # Uniform beta upper bound for the diffuse base

The beta numbers of the diffuse base are bounded by a constant multiple of `r^{n+2-k}` at every
centre and radius (`e2_diffuse_betaUpper_proof`). Proof: a model through the centre (`exists_model_mem`); on `P(z,r)` the parabolic distance to the
model is below `r`; constant majorant `r^p` against `ω(P(z,r)) ≤ 2ω_n r^{n+2}`; `iInf_le`; rpow
algebra. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations ParabolicRectifiability

/-- The ball bound `ω(P(z,r)) ≤ 2ω_n r^{n+2}`. -/
theorem e2d2_ball_le (n : ℕ) (z : Space n) (r : ℝ) (hr : 0 < r) :
    e2_diffuseBase n (Metric.ball z r) ≤ 2 * omega n * ENNReal.ofReal r ^ (n + 2) := by
  calc e2_diffuseBase n (Metric.ball z r)
      ≤ parabolicVolume n (Metric.ball z r) := Measure.restrict_le_self _
    _ = _ := parabolicVolume_ball z r hr

/-- The fit of a model through the centre. -/
theorem e2d2_fit_le (n k : ℕ) (T : FamilyKind) (p : ℝ) (hp : 0 < p) (L : Models n k T)
    (z : Space n) (hz : z ∈ modelSet L) (r : ℝ) (hr : 0 < r) :
    fitPow (e2_diffuseBase n) p L z r ≤
      ENNReal.ofReal r ^ p * (2 * omega n * ENNReal.ofReal r ^ (n + 2)) := by
  unfold fitPow
  calc ∫⁻ w in Metric.ball z r, Metric.infEDist w (modelSet L) ^ p ∂(e2_diffuseBase n)
      ≤ ∫⁻ w in Metric.ball z r, ENNReal.ofReal r ^ p ∂(e2_diffuseBase n) := by
        refine setLIntegral_mono measurable_const fun w hw => ?_
        have h1 : Metric.infEDist w (modelSet L) ≤ edist w z := Metric.infEDist_le_edist_of_mem hz
        have h2 : edist w z < ENNReal.ofReal r := by
          rw [edist_dist]
          exact ENNReal.ofReal_lt_ofReal_iff hr |>.2 (Metric.mem_ball.1 hw)
        exact ENNReal.rpow_le_rpow (h1.trans h2.le) hp.le
    _ = ENNReal.ofReal r ^ p * e2_diffuseBase n (Metric.ball z r) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := by gcongr; exact e2d2_ball_le n z r hr

/-- The normalization identity `r^{-(k+p)} · r^p · c r^{n+2} = c r^{n+2-k}`. -/
theorem e2d2_algebra (n k : ℕ) (p : ℝ) (_hp : 0 < p) (r : ℝ) (hr : 0 < r) (c : ℝ≥0∞) :
    (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) *
        (ENNReal.ofReal r ^ p * (c * ENNReal.ofReal r ^ (n + 2))) =
      c * ENNReal.ofReal r ^ ((n : ℝ) + 2 - k) := by
  have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have ht : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  set x := ENNReal.ofReal r with hx
  have hn : x ^ (n + 2) = x ^ ((n : ℝ) + 2) := by
    rw [← ENNReal.rpow_natCast]; norm_num
  have hsub : x ^ ((n : ℝ) + 2 - k) = x ^ ((n : ℝ) + 2) * x ^ p / x ^ ((k : ℝ) + p) := by
    rw [← ENNReal.rpow_add _ _ h0 ht, ← ENNReal.rpow_sub _ _ h0 ht]; congr 1; ring
  rw [hsub, hn, ENNReal.inv_rpow, div_eq_mul_inv]
  ring

/-- **Uniform beta upper bound** for the diffuse base. -/
theorem e2_diffuse_betaUpper_proof : E2DiffuseBetaUpperStatement := by
  intro n k T hne p hp z r hr
  obtain ⟨L, hL⟩ := exists_model_mem hne z
  unfold betaPow
  rw [ite_eq_left hr]
  calc (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) * ⨅ L : Models n k T, fitPow (e2_diffuseBase n) p L z r
      ≤ (ENNReal.ofReal r)⁻¹ ^ ((k : ℝ) + p) *
          (ENNReal.ofReal r ^ p * (2 * omega n * ENNReal.ofReal r ^ (n + 2))) := by
        gcongr
        exact (iInf_le _ L).trans (e2d2_fit_le n k T p hp L z hL r hr)
    _ = _ := e2d2_algebra n k p hp r hr _

end ParabolicRectifiability.Examples
