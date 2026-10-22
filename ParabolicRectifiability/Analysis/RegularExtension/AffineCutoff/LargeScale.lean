import ParabolicRectifiability.Analysis.RegularExtension.AffineCutoff.CutoffComparison

/-! # The large-scale integrated tail

For `H = χ (G - c)` as in `CutoffComparison` and `R₀ > 0`,
`∫_V ∫_{(R₀,∞)} κ_H(y,s)^2 ds/s dy ≤ 49 v^2 20^k L^2 R₀^k`, `v = 2ω_m`, `k = m + 2`.

The zero comparison gives `κ_H(y,s)^2 ≤ g(y,s) = 1_{P(z₀,4R₀+s)}(y) M s^{-k-2}`, with
`M = 49 L^2 R₀^2 |P(z₀,4R₀)|`. The majorant `g` is jointly measurable, so Tonelli exchanges the
integrals: `∫_V g(y,s) dy = M s^{-k-2} |P(z₀,4R₀+s)| ≤ M v 5^k s^{-2}` for `s > R₀`, and
`∫_{(R₀,∞)} s^{-2} ds/s = R₀^{-2}/2`. No measurability of the affine errors themselves is
used: only the measurable majorant is integrated (its section integral is measurable, which
the final assembly needs to split the sum of the two scale ranges).
-/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal

namespace ParabolicRectifiability

section LargeScale

variable {m : ℕ}

/-- The measurable large-scale majorant `1_{P(z₀,4R₀+s)}(y) M s^{-k-2}`. -/
def rx4_largeMajorant (m : ℕ) (z₀ : Space m) (R₀ : ℝ) (M : ℝ≥0∞) (y : Space m) (s : ℝ) :
    ℝ≥0∞ :=
  {p : Space m × ℝ | dist p.1 z₀ < 4 * R₀ + p.2}.indicator
    (fun p => M * (ENNReal.ofReal p.2)⁻¹ ^ (m + 4)) (y, s)

theorem rx4_largeMajorant_eq (z₀ : Space m) (R₀ : ℝ) (M : ℝ≥0∞) (y : Space m) (s : ℝ) :
    rx4_largeMajorant m z₀ R₀ M y s =
      (Metric.ball z₀ (4 * R₀ + s)).indicator
        (fun _ => M * (ENNReal.ofReal s)⁻¹ ^ (m + 4)) y := by
  unfold rx4_largeMajorant
  by_cases h : dist y z₀ < 4 * R₀ + s
  · have h1 : (y, s) ∈ {p : Space m × ℝ | dist p.1 z₀ < 4 * R₀ + p.2} := h
    have h2 : y ∈ Metric.ball z₀ (4 * R₀ + s) := Metric.mem_ball.2 h
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : (y, s) ∉ {p : Space m × ℝ | dist p.1 z₀ < 4 * R₀ + p.2} := h
    have h2 : y ∉ Metric.ball z₀ (4 * R₀ + s) := fun h' => h (Metric.mem_ball.1 h')
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

theorem rx4_measurable_largeMajorant (z₀ : Space m) (R₀ : ℝ) (M : ℝ≥0∞) :
    Measurable (uncurry (rx4_largeMajorant m z₀ R₀ M)) := by
  have hd : Measurable fun p : Space m × ℝ => dist p.1 z₀ :=
    (continuous_fst.dist continuous_const).measurable
  have hS : MeasurableSet {p : Space m × ℝ | dist p.1 z₀ < 4 * R₀ + p.2} :=
    measurableSet_lt hd (measurable_const.add measurable_snd)
  exact (((measurable_inv_pow_ofReal (m + 4)).comp measurable_snd).const_mul M).indicator hS

theorem rx4_measurable_lintegral_largeMajorant (z₀ : Space m) (R₀ : ℝ) (M : ℝ≥0∞)
    (ν : Measure ℝ) [SFinite ν] :
    Measurable fun y => ∫⁻ s, rx4_largeMajorant m z₀ R₀ M y s ∂ν :=
  (rx4_measurable_largeMajorant z₀ R₀ M).lintegral_prod_right'

/-- Tonelli for the majorant. -/
theorem rx4_lintegral_largeMajorant_le (z₀ : Space m) {R₀ : ℝ} (hR : 0 < R₀) (M : ℝ) (hM : 0 ≤ M) :
    ∫⁻ y, ∫⁻ s in Ioi R₀, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s ∂scaleMeasure
        ∂parabolicVolume m ≤
      ENNReal.ofReal (M * ((2 * omega m).toReal * 5 ^ (m + 2)) * ((R₀ ^ 2)⁻¹ / 2)) := by
  have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
  rw [lintegral_lintegral_swap (rx4_measurable_largeMajorant z₀ R₀ _).aemeasurable]
  have hpt : ∀ s ∈ Ioi R₀,
      ∫⁻ y, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s ∂parabolicVolume m ≤
        ENNReal.ofReal (M * ((2 * omega m).toReal * 5 ^ (m + 2))) *
          (ENNReal.ofReal s)⁻¹ ^ 2 := by
    intro s hs
    have hs0 : 0 < s := hR.trans hs
    simp_rw [rx4_largeMajorant_eq]
    rw [lintegral_indicator_const measurableSet_ball]
    have hball : parabolicVolume m (Metric.ball z₀ (4 * R₀ + s)) ≤
        ENNReal.ofReal ((2 * omega m).toReal * (5 * s) ^ (m + 2)) := by
      rw [← TraceExtension.parabolicVolume_ball_eq_ofReal z₀ (by positivity : (0 : ℝ) < 5 * s)]
      exact measure_mono (Metric.ball_subset_ball (by linarith [mem_Ioi.1 hs]))
    calc ENNReal.ofReal M * (ENNReal.ofReal s)⁻¹ ^ (m + 4) *
          parabolicVolume m (Metric.ball z₀ (4 * R₀ + s))
        ≤ ENNReal.ofReal M * (ENNReal.ofReal s)⁻¹ ^ (m + 4) *
          ENNReal.ofReal ((2 * omega m).toReal * (5 * s) ^ (m + 2)) := by gcongr
      _ = ENNReal.ofReal (M * ((2 * omega m).toReal * 5 ^ (m + 2))) *
          (ENNReal.ofReal s)⁻¹ ^ 2 := by
        have key : s⁻¹ ^ (m + 4) * s ^ (m + 2) = s⁻¹ ^ 2 := by
          rw [show m + 4 = m + 2 + 2 by omega, pow_add, mul_right_comm, ← mul_pow,
            inv_mul_cancel₀ hs0.ne', one_pow, one_mul]
        have hreal : M * s⁻¹ ^ (m + 4) * ((2 * omega m).toReal * (5 * s) ^ (m + 2)) =
            M * ((2 * omega m).toReal * 5 ^ (m + 2)) * s⁻¹ ^ 2 := by
          rw [mul_pow, ← key]
          ring
        rw [← ENNReal.ofReal_inv_of_pos hs0, ← ENNReal.ofReal_pow (inv_nonneg.2 hs0.le),
          ← ENNReal.ofReal_pow (inv_nonneg.2 hs0.le), ← ENNReal.ofReal_mul hM,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        exact congrArg ENNReal.ofReal hreal
  calc ∫⁻ s in Ioi R₀, ∫⁻ y, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s
          ∂parabolicVolume m ∂scaleMeasure
      ≤ ∫⁻ s in Ioi R₀, ENNReal.ofReal (M * ((2 * omega m).toReal * 5 ^ (m + 2))) *
          (ENNReal.ofReal s)⁻¹ ^ 2 ∂scaleMeasure := setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (M * ((2 * omega m).toReal * 5 ^ (m + 2))) *
          ENNReal.ofReal ((R₀ ^ 2)⁻¹ / 2) := by
        rw [lintegral_const_mul _ (measurable_inv_pow_ofReal 2),
          lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos hR]
        norm_num
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

variable {χ : Space m → ℝ} {K R₀ : ℝ} {z₀ : Space m}
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The affine error of the cutoff is dominated by the large-scale majorant at every
positive scale. -/
theorem rx4_affineErrorSq_cutoff_le_largeMajorant (hR : 0 < R₀)
    (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hsupp : ∀ p, χ p ≠ 0 → p ∈ Metric.ball z₀ (4 * R₀))
    (G : Space m → Y) (c : Y) {L : ℝ} (hL : 0 ≤ L)
    (hc : ∀ q, dist q z₀ ≤ 6 * R₀ → ‖G q - c‖ ≤ 7 * L * R₀)
    (y : Space m) {s : ℝ} (hs : 0 < s) :
    affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s ≤
      rx4_largeMajorant m z₀ R₀
        (ENNReal.ofReal (49 * L ^ 2 * R₀ ^ 2 * ((2 * omega m).toReal * (4 * R₀) ^ (m + 2))))
        y s := by
  rw [rx4_largeMajorant_eq]
  exact rx4_affineErrorSq_cutoff_le_zero hR h01 hsupp G c hL hc y hs

/-- **Large scales, by Tonelli.**
`∫_V ∫_{(R₀,∞)} κ_H(y,s)^2 ds/s dy ≤ 49 v^2 20^k L^2 R₀^k`. -/
theorem rx4_lintegral_large_scale_le (hR : 0 < R₀)
    (h01 : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) (hsupp : ∀ p, χ p ≠ 0 → p ∈ Metric.ball z₀ (4 * R₀))
    (G : Space m → Y) (c : Y) {L : ℝ} (hL : 0 ≤ L)
    (hc : ∀ q, dist q z₀ ≤ 6 * R₀ → ‖G q - c‖ ≤ 7 * L * R₀) :
    ∫⁻ y, ∫⁻ s in Ioi R₀, affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s
        ∂scaleMeasure ∂parabolicVolume m ≤
      ENNReal.ofReal (49 * (2 * omega m).toReal ^ 2 * 20 ^ (m + 2) * L ^ 2 * R₀ ^ (m + 2)) := by
  have hv : 0 ≤ (2 * omega m).toReal := ENNReal.toReal_nonneg
  set M := 49 * L ^ 2 * R₀ ^ 2 * ((2 * omega m).toReal * (4 * R₀) ^ (m + 2)) with hM
  have hM0 : 0 ≤ M := by positivity
  calc ∫⁻ y, ∫⁻ s in Ioi R₀, affineErrorSq (parabolicVolume m) (fun p => χ p • (G p - c)) y s
        ∂scaleMeasure ∂parabolicVolume m
      ≤ ∫⁻ y, ∫⁻ s in Ioi R₀, rx4_largeMajorant m z₀ R₀ (ENNReal.ofReal M) y s
        ∂scaleMeasure ∂parabolicVolume m :=
        lintegral_mono fun y => setLIntegral_mono' measurableSet_Ioi fun s hs =>
          rx4_affineErrorSq_cutoff_le_largeMajorant hR h01 hsupp G c hL hc y
            (hR.trans (mem_Ioi.1 hs))
    _ ≤ ENNReal.ofReal (M * ((2 * omega m).toReal * 5 ^ (m + 2)) * ((R₀ ^ 2)⁻¹ / 2)) :=
        rx4_lintegral_largeMajorant_le z₀ hR M hM0
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hR0 : R₀ ≠ 0 := hR.ne'
        have heq : M * ((2 * omega m).toReal * 5 ^ (m + 2)) * ((R₀ ^ 2)⁻¹ / 2) =
            49 / 2 * (2 * omega m).toReal ^ 2 * (4 ^ (m + 2) * 5 ^ (m + 2)) * L ^ 2 *
              R₀ ^ (m + 2) := by
          rw [hM]
          field_simp
          ring
        rw [heq, show (4 : ℝ) ^ (m + 2) * 5 ^ (m + 2) = 20 ^ (m + 2) by
          rw [← mul_pow]; norm_num]
        have : 0 ≤ (2 * omega m).toReal ^ 2 * 20 ^ (m + 2) * L ^ 2 * R₀ ^ (m + 2) := by
          positivity
        nlinarith

end LargeScale

end ParabolicRectifiability
