import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Vanishing lower density of the dispersed digit graph

The marked scales have small ball mass because separation forces every point in the
ball to retain the centre's marked bit. The periodic mass bound then gives a ratio at most
`3 δ_j`. Eventual lower bounds for the density pull back along the positive radii, so the
infinitely many marked scales force the lower density to vanish. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private theorem graph_ball_coordinate {x x₀ r : ℝ}
    (hx : e2_sbGraph x ∈ Metric.ball (e2_sbGraph x₀) r) (i : Fin 2) :
    |e2_sbGraph x i - e2_sbGraph x₀ i| < r := by
  exact (show |e2_sbGraph x i - e2_sbGraph x₀ i| ≤
      dist (e2_sbGraph x) (e2_sbGraph x₀) by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le (e2_sbGraph x) (e2_sbGraph x₀) i).trans_lt hx

private theorem marked_ball_mass (hG : E2sbGrid) (hD : E2sbDigit)
    (hP : E2sbPeriodic) (hM : E2sbMeasurable) {j : ℕ} (hj : 1 ≤ j)
    {x₀ : ℝ} (hx₀ : x₀ ∈ e2_sbMarked j) :
    e2_sbSource (Metric.ball (e2_sbGraph x₀) (e2_sbH j / 4)) ≤
      ENNReal.ofReal (3 * e2_sbDelta j * (e2_sbH j / 4)) := by
  rw [e2_sbSource, Measure.map_apply hM.2.2 measurableSet_ball]
  refine (Measure.restrict_apply_le _ _).trans ((measure_mono ?_).trans
    (hP.2 j hj x₀ (e2_sbH j / 4) le_rfl))
  intro x hx
  have hxcoord : |x - x₀| < e2_sbH j / 4 := by
    simpa [e2_sbGraph] using graph_ball_coordinate hx 0
  have hycoord : |e2_sbHeight x - e2_sbHeight x₀| < e2_sbH j / 4 := by
    simpa [e2_sbGraph] using graph_ball_coordinate hx 1
  have hsep : |e2_sbHeight x - e2_sbHeight x₀| < e2_sbH j / 2 := by
    linarith [hG.2.1 j]
  have hbit := hD.2.2 j x x₀ hsep j hj le_rfl
  have hxmark : x ∈ e2_sbMarked j := by
    by_contra hnot
    simp [e2_sbBit, hnot, hx₀] at hbit
  exact ⟨⟨by linarith [(abs_lt.mp hxcoord).1],
    by linarith [(abs_lt.mp hxcoord).2]⟩, hxmark⟩

private theorem marked_density_ratio (hG : E2sbGrid) (hD : E2sbDigit)
    (hP : E2sbPeriodic) (hM : E2sbMeasurable) {j : ℕ} (hj : 1 ≤ j)
    {x₀ : ℝ} (hx₀ : x₀ ∈ e2_sbMarked j) :
    BetaP.planarDensityRatio e2_sbSource (e2_sbGraph x₀) (e2_sbH j / 4) ≤
      ENNReal.ofReal (3 * e2_sbDelta j) := by
  have hr : 0 < e2_sbH j / 4 := div_pos (hG.2.1 j) (by norm_num)
  rw [BetaP.planarDensityRatio,
    ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul' hr.le]
  exact marked_ball_mass hG hD hP hM hj hx₀

/-- At every real centre with infinitely many marked digits, the lower density is zero. -/
theorem e2_sb_lowerDensity_proof (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit)
    (hP : E2sbPeriodic) (hM : E2sbMeasurable) : E2sbLowerDensity := by
  intro x₀ hmark
  rcases hT with ⟨_, _, _, _, _, _, _, _, hH⟩
  have hr : Tendsto (fun j => e2_sbH j / 4) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div] using hH.div_const 4
    · exact Eventually.of_forall fun j => div_pos (hG.2.1 j) (by norm_num)
  have hδ : Tendsto (fun j => ENNReal.ofReal (3 * e2_sbDelta j)) atTop (𝓝 0) := by
    have hd : Tendsto e2_sbDelta atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hd.const_mul 3)
  apply le_antisymm ?_ bot_le
  unfold BetaP.planarLowerDensity
  refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
  apply ge_of_tendsto_of_frequently hδ
  exact ((hmark.and_eventually (hr.eventually hb)).and_eventually
    (eventually_ge_atTop 1)).mono fun j hj =>
      hj.1.2.trans (marked_density_ratio hG hD hP hM hj.2 hj.1.1)

end ParabolicRectifiability.Examples
