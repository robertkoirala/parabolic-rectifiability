import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ProjectionEnergy

/-! # The averaging kernel

Proof of `d1e2_KernelIntegrationStatement`, as `d1e2_kernel_integration_proof`.

Proof sketch: write the inner ball integral with the indicator of
the jointly measurable set `{(y,q) | dist q y < r}`; swap by Tonelli
(`lintegral_lintegral_swap`); for fixed `q` the `y`-integral over `P_b(z,R)` is at most
`W q · |P_b(q,r)| = W q · 2ω_m r^{m+2}` (`parabolicVolume_ball`) and vanishes unless
`dist q z < R + r ≤ 11R`. Constant `C = (2ω_m).toReal`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

/-- The kernel `(y,q) ↦ 1_{dist q y < r} W q`. -/
def d1e2kernel_kernel {m : ℕ} (W : Space m → ℝ≥0∞) (r : ℝ) (y q : Space m) : ℝ≥0∞ :=
  {p : Space m × Space m | dist p.2 p.1 < r}.indicator (fun p => W p.2) (y, q)

theorem d1e2kernel_measurable {m : ℕ} {W : Space m → ℝ≥0∞} (hW : Measurable W) (r : ℝ) :
    Measurable (Function.uncurry (d1e2kernel_kernel W r)) := by
  have hS : MeasurableSet {p : Space m × Space m | dist p.2 p.1 < r} :=
    measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const
  exact (hW.comp measurable_snd).indicator hS

theorem d1e2kernel_inner_eq {m : ℕ} (W : Space m → ℝ≥0∞) (r : ℝ) (y : Space m) :
    ∫⁻ q in Metric.ball y r, W q ∂parabolicVolume m =
      ∫⁻ q, d1e2kernel_kernel W r y q ∂parabolicVolume m := by
  rw [← lintegral_indicator measurableSet_ball]
  rfl

/-- For fixed `q`, the `y`-integral of the kernel over `P_b(z,R)` is at most
`1_{P_b(z,11R)}(q) W q · |P_b(q,r)|`. -/
theorem d1e2kernel_fixed_le {m : ℕ} (W : Space m → ℝ≥0∞) (z : Space m) {R r : ℝ}
    (hr : 0 < r) (hrR : r ≤ 10 * R) (q : Space m) :
    ∫⁻ y in Metric.ball z R, d1e2kernel_kernel W r y q ∂parabolicVolume m ≤
      (Metric.ball z (11 * R)).indicator W q * (2 * omega m * ENNReal.ofReal r ^ (m + 2)) := by
  by_cases hq : q ∈ Metric.ball z (11 * R)
  · rw [Set.indicator_of_mem hq]
    have hpt : ∀ y, d1e2kernel_kernel W r y q ≤
        (Metric.ball q r).indicator (fun _ => W q) y := by
      intro y
      by_cases hy : dist q y < r
      · have hy' : y ∈ Metric.ball q r := by
          rw [Metric.mem_ball, dist_comm]
          exact hy
        have hmem : (y, q) ∈ {p : Space m × Space m | dist p.2 p.1 < r} := hy
        rw [d1e2kernel_kernel, Set.indicator_of_mem hmem, Set.indicator_of_mem hy']
      · have hmem : (y, q) ∉ {p : Space m × Space m | dist p.2 p.1 < r} := hy
        rw [d1e2kernel_kernel, Set.indicator_of_notMem hmem]
        exact zero_le
    calc ∫⁻ y in Metric.ball z R, d1e2kernel_kernel W r y q ∂parabolicVolume m
        ≤ ∫⁻ y, d1e2kernel_kernel W r y q ∂parabolicVolume m :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ y, (Metric.ball q r).indicator (fun _ => W q) y ∂parabolicVolume m :=
          lintegral_mono hpt
      _ = W q * parabolicVolume m (Metric.ball q r) :=
          lintegral_indicator_const measurableSet_ball _
      _ = W q * (2 * omega m * ENNReal.ofReal r ^ (m + 2)) := by
          rw [parabolicVolume_ball q r hr]
  · have hzero : ∀ y ∈ Metric.ball z R, d1e2kernel_kernel W r y q ≤ 0 := by
      intro y hy
      have hmem : (y, q) ∉ {p : Space m × Space m | dist p.2 p.1 < r} := by
        intro h
        apply hq
        have h1 : dist q y < r := h
        have h2 : dist y z < R := hy
        rw [Metric.mem_ball]
        calc dist q z ≤ dist q y + dist y z := dist_triangle _ _ _
          _ < r + R := add_lt_add h1 h2
          _ ≤ 11 * R := by linarith
      rw [d1e2kernel_kernel, Set.indicator_of_notMem hmem]
    calc ∫⁻ y in Metric.ball z R, d1e2kernel_kernel W r y q ∂parabolicVolume m
        ≤ ∫⁻ _y in Metric.ball z R, 0 ∂parabolicVolume m :=
          setLIntegral_mono' measurableSet_ball hzero
      _ = 0 := lintegral_zero
      _ ≤ _ := zero_le

/-- **The averaging kernel**: averaging ball integrals of a nonnegative function `W` at radius
`r ≤ 10R` over the centres in `P_b(z,R)` costs at most a constant times `r^{m+2}` times the
integral of `W` over `P_b(z,11R)`. -/
theorem d1e2_kernel_integration_proof : d1e2_KernelIntegrationStatement := by
  intro m
  refine ⟨(2 * omega m).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro W hW z R r hr hrR
  have hω : 2 * omega m ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hc : (ENNReal.ofReal r)⁻¹ ^ (m + 2) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hr0)
  have hcr : (ENNReal.ofReal r)⁻¹ ^ (m + 2) * ENNReal.ofReal r ^ (m + 2) = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel hr0 ENNReal.ofReal_ne_top, one_pow]
  have hind : Measurable ((Metric.ball z (11 * R)).indicator W) :=
    hW.indicator measurableSet_ball
  calc ∫⁻ y in Metric.ball z R,
          (ENNReal.ofReal r)⁻¹ ^ (m + 2) * ∫⁻ q in Metric.ball y r, W q ∂parabolicVolume m
        ∂parabolicVolume m
      = (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          ∫⁻ y in Metric.ball z R, ∫⁻ q, d1e2kernel_kernel W r y q ∂parabolicVolume m
            ∂parabolicVolume m := by
        rw [lintegral_const_mul' _ _ hc]
        simp_rw [d1e2kernel_inner_eq W r]
    _ = (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          ∫⁻ q, ∫⁻ y in Metric.ball z R, d1e2kernel_kernel W r y q ∂parabolicVolume m
            ∂parabolicVolume m := by
        rw [lintegral_lintegral_swap (d1e2kernel_measurable hW r).aemeasurable]
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          ∫⁻ q, (Metric.ball z (11 * R)).indicator W q *
            (2 * omega m * ENNReal.ofReal r ^ (m + 2)) ∂parabolicVolume m := by
        gcongr with q
        exact d1e2kernel_fixed_le W z hr hrR q
    _ = (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
          ((∫⁻ q in Metric.ball z (11 * R), W q ∂parabolicVolume m) *
            (2 * omega m * ENNReal.ofReal r ^ (m + 2))) := by
        rw [lintegral_mul_const _ hind, lintegral_indicator measurableSet_ball]
    _ = 2 * omega m * (∫⁻ q in Metric.ball z (11 * R), W q ∂parabolicVolume m) *
          ((ENNReal.ofReal r)⁻¹ ^ (m + 2) * ENNReal.ofReal r ^ (m + 2)) := by ring
    _ = ENNReal.ofReal (2 * omega m).toReal *
          ∫⁻ q in Metric.ball z (11 * R), W q ∂parabolicVolume m := by
        rw [hcr, mul_one, ENNReal.ofReal_toReal hω]

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
