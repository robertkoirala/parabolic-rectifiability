import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # Scale-band beta estimate for the dispersed digit graph

For every `p > 0` there is `C_p` such that, for `z ∈ E`, `j ≥ 1` and `h_j/4 ≤ r < h_{j-1}/4`,
`β_{p,μ}(z,r)^2 ≤ C_p [δ_j^{2/p} (h_j/r)^2 + (η_j/r)^2]` (`e2_sb_band_proof`). The closure center is
first replaced by a graph point within the strict old-height buffer.  Digit
separation then makes the old height constant on the ball. -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane)

private lemma band_old_height (hG : E2sbGrid) (hD : E2sbDigit)
    {z : Plane} (hz : z ∈ e2_sbSet) {j : ℕ} (hj : 1 ≤ j) {r : ℝ}
    (hr : r < e2_sbH (j - 1) / 4) :
    ∃ Y : ℝ, ∀ x : ℝ, e2_sbGraph x ∈ Metric.ball z r →
      0 ≤ e2_sbHeight x - Y ∧
      e2_sbHeight x - Y ≤ e2_sbH j * e2_sbBit j x + e2_sbTail j := by
  obtain ⟨w, ⟨x₀, hx₀, rfl⟩, hw⟩ :=
    Metric.mem_closure_iff.mp hz (e2_sbH (j - 1) / 4) (div_pos (hG.2.1 _) (by norm_num))
  refine ⟨e2_sbOldHeight (j - 1) x₀, ?_⟩
  intro x hx
  have hdist : dist (e2_sbGraph x) (e2_sbGraph x₀) < e2_sbH (j - 1) / 2 := by
    have ht := dist_triangle (e2_sbGraph x) z (e2_sbGraph x₀)
    have hb := Metric.mem_ball.mp hx
    linarith
  have hd : |e2_sbHeight x - e2_sbHeight x₀| < e2_sbH (j - 1) / 2 := by
    have hc := PiLp.dist_apply_le (e2_sbGraph x) (e2_sbGraph x₀) 1
    simp [e2_sbGraph, Real.dist_eq] at hc
    exact hc.trans_lt hdist
  have hold : e2_sbOldHeight (j - 1) x = e2_sbOldHeight (j - 1) x₀ := by
    unfold e2_sbOldHeight
    apply Finset.sum_congr rfl
    intro i hi
    rw [hD.2.2 (j - 1) x x₀ hd (i + 1) (by omega) (by simpa using Finset.mem_range.mp hi)]
  have hs : e2_sbOldHeight j x = e2_sbOldHeight (j - 1) x +
      e2_sbH j * e2_sbBit j x := by
    simpa only [e2_sbOldHeight, Nat.sub_add_cancel hj] using
      Finset.sum_range_succ (fun i => e2_sbH (i + 1) * e2_sbBit (i + 1) x) (j - 1)
  have hb : 0 ≤ e2_sbBit j x := by
    by_cases hx : x ∈ e2_sbMarked j <;> simp [e2_sbBit, hx]
  have hh := hG.2.1 j
  have ht := hD.2.1 j x
  rw [hs, hold] at ht
  constructor <;> nlinarith [mul_nonneg hh.le hb]

private lemma band_distance_bound (hG : E2sbGrid) (hT : E2sbTails)
    {p : ℝ} (hp : 0 < p) {j : ℕ} {Y : ℝ} {x : ℝ}
    (hx : 0 ≤ e2_sbHeight x - Y ∧
      e2_sbHeight x - Y ≤ e2_sbH j * e2_sbBit j x + e2_sbTail j) :
    ENNReal.ofReal |e2_sbHeight x - Y| ^ p ≤
      (2 : ℝ≥0∞) ^ p * ((e2_sbMarked j).indicator
        (fun _ => ENNReal.ofReal (e2_sbH j) ^ p) x + ENNReal.ofReal (e2_sbTail j) ^ p) := by
  have hh := (hG.2.1 j).le
  have ht := hT.2.2.1 j
  have hb : 0 ≤ e2_sbBit j x := by
    by_cases hx : x ∈ e2_sbMarked j <;> simp [e2_sbBit, hx]
  have hm : ENNReal.ofReal (e2_sbH j * e2_sbBit j x) ^ p =
      (e2_sbMarked j).indicator (fun _ => ENNReal.ofReal (e2_sbH j) ^ p) x := by
    by_cases h : x ∈ e2_sbMarked j
    · simp [e2_sbBit, h]
    · simp [e2_sbBit, h, ENNReal.zero_rpow_of_pos hp]
  calc
    ENNReal.ofReal |e2_sbHeight x - Y| ^ p ≤
        ENNReal.ofReal (e2_sbH j * e2_sbBit j x + e2_sbTail j) ^ p := by
      apply ENNReal.rpow_le_rpow _ hp.le
      apply ENNReal.ofReal_le_ofReal
      simpa [abs_of_nonneg hx.1] using hx.2
    _ = (ENNReal.ofReal (e2_sbH j * e2_sbBit j x) +
        ENNReal.ofReal (e2_sbTail j)) ^ p := by
      rw [ENNReal.ofReal_add (mul_nonneg hh hb) ht]
    _ ≤ _ := by
      simpa [hm] using ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
        (ENNReal.ofReal (e2_sbH j * e2_sbBit j x)) (ENNReal.ofReal (e2_sbTail j)) hp.le

private lemma band_integral_bound (hG : E2sbGrid) (hT : E2sbTails)
    (hD : E2sbDigit) (hP : E2sbPeriodic) (hM : E2sbMeasurable)
    (hDen : E2sbDensity) (hL : E2PlanarLine)
    {p : ℝ} (hp : 0 < p) {z : Plane} (hz : z ∈ e2_sbSet)
    {j : ℕ} (hj : 1 ≤ j) {r : ℝ} (hrlo : e2_sbH j / 4 ≤ r)
    (hrhi : r < e2_sbH (j - 1) / 4) :
    ∃ L : AffineSpatialPlane 2 1,
      (∫⁻ w in Metric.ball z r, Metric.infEDist w L.toSet ^ p ∂e2_sbSource) ≤
      (2 : ℝ≥0∞) ^ p * (ENNReal.ofReal (e2_sbH j) ^ p *
        ENNReal.ofReal (3 * e2_sbDelta j * r) +
        ENNReal.ofReal (e2_sbTail j) ^ p * ENNReal.ofReal (2 * r)) := by
  have hr : 0 < r := lt_of_lt_of_le (div_pos (hG.2.1 j) (by norm_num)) hrlo
  obtain ⟨Y, hY⟩ := band_old_height hG hD hz hj hrhi
  obtain ⟨L, hLine⟩ := hL.2 0 1 Y (by norm_num)
  have hLine' : ∀ w : Plane, Metric.infEDist w L.toSet = ENNReal.ofReal |w 1 - Y| := by
    simpa using hLine
  let A := e2_sbGraph ⁻¹' Metric.ball z r
  let ν : Measure ℝ := volume.restrict (Ico 0 1)
  have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet.preimage hM.2.2
  have hmass : ν A ≤ ENNReal.ofReal (2 * r) := by
    have heq : e2_sbSource (Metric.ball z r) = ν A :=
      Measure.map_apply hM.2.2 Metric.isOpen_ball.measurableSet
    rw [← heq]
    exact hDen.1 z r hr
  have hmark : (ν.restrict A) (e2_sbMarked j) ≤
      ENNReal.ofReal (3 * e2_sbDelta j * r) := by
    calc
      (ν.restrict A) (e2_sbMarked j) =
          volume ((e2_sbMarked j ∩ A) ∩ Ico 0 1) := by
        rw [Measure.restrict_apply (hM.1 j), Measure.restrict_apply ((hM.1 j).inter hA)]
      _ ≤ volume (Ioo (z 0 - r) (z 0 + r) ∩ e2_sbMarked j) := by
        apply measure_mono
        intro x hx
        have hd : |x - z 0| < r := by
          have hc := PiLp.dist_apply_le (e2_sbGraph x) z 0
          have hb := Metric.mem_ball.mp hx.1.2
          have hc' : |x - z 0| ≤ dist (e2_sbGraph x) z := by
            simpa [e2_sbGraph, Real.dist_eq] using hc
          exact hc'.trans_lt hb
        exact ⟨⟨by linarith [(abs_lt.mp hd).1], by linarith [(abs_lt.mp hd).2]⟩, hx.1.1⟩
      _ ≤ _ := hP.2 j hj (z 0) r hrlo
  refine ⟨L, ?_⟩
  rw [e2_sbSource, setLIntegral_map Metric.isOpen_ball.measurableSet
    (measurable_infEDist.pow_const p) hM.2.2]
  change (∫⁻ x, Metric.infEDist (e2_sbGraph x) L.toSet ^ p ∂ν.restrict A) ≤ _
  calc
    (∫⁻ x, Metric.infEDist (e2_sbGraph x) L.toSet ^ p ∂ν.restrict A) ≤
        ∫⁻ x, (2 : ℝ≥0∞) ^ p * ((e2_sbMarked j).indicator
          (fun _ => ENNReal.ofReal (e2_sbH j) ^ p) x +
          ENNReal.ofReal (e2_sbTail j) ^ p) ∂ν.restrict A := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      rw [hLine']
      simpa [e2_sbGraph] using band_distance_bound hG hT hp (hY x hx)
    _ = (2 : ℝ≥0∞) ^ p * (ENNReal.ofReal (e2_sbH j) ^ p *
          (ν.restrict A) (e2_sbMarked j) + ENNReal.ofReal (e2_sbTail j) ^ p * ν A) := by
      have hmI : Measurable ((e2_sbMarked j).indicator
          (fun _ => ENNReal.ofReal (e2_sbH j) ^ p)) := measurable_const.indicator (hM.1 j)
      have hmF : Measurable (fun x => (e2_sbMarked j).indicator
          (fun _ => ENNReal.ofReal (e2_sbH j) ^ p) x + ENNReal.ofReal (e2_sbTail j) ^ p) :=
        hmI.add measurable_const
      rw [lintegral_const_mul _ hmF,
        lintegral_add_left hmI,
        lintegral_indicator_const (hM.1 j), lintegral_const]
      simp
    _ ≤ _ := by gcongr

private lemma band_beta_bound (hG : E2sbGrid) (hT : E2sbTails)
    (hD : E2sbDigit) (hP : E2sbPeriodic) (hM : E2sbMeasurable)
    (hDen : E2sbDensity) (hL : E2PlanarLine)
    {p : ℝ} (hp : 0 < p) {z : Plane} (hz : z ∈ e2_sbSet)
    {j : ℕ} (hj : 1 ≤ j) {r : ℝ} (hrlo : e2_sbH j / 4 ≤ r)
    (hrhi : r < e2_sbH (j - 1) / 4) :
    euclideanBetaPow e2_sbSource 1 p z r ≤
      ENNReal.ofReal ((3 * (2 : ℝ) ^ p) *
        (e2_sbDelta j * (e2_sbH j / r) ^ p + (e2_sbTail j / r) ^ p)) := by
  have hr : 0 < r := lt_of_lt_of_le (div_pos (hG.2.1 j) (by norm_num)) hrlo
  have hh := (hG.2.1 j).le
  have ht := hT.2.2.1 j
  have hd := (hG.2.2.2.2.2.2.2.2 j hj).1.le
  obtain ⟨L, hcost⟩ := band_integral_bound hG hT hD hP hM hDen hL hp hz hj hrlo hrhi
  have hraw :
      (ENNReal.ofReal r)⁻¹ ^ (1 + p) * ((2 : ℝ≥0∞) ^ p *
        (ENNReal.ofReal (e2_sbH j) ^ p * ENNReal.ofReal (3 * e2_sbDelta j * r) +
         ENNReal.ofReal (e2_sbTail j) ^ p * ENNReal.ofReal (2 * r))) =
      ENNReal.ofReal ((r⁻¹) ^ (1 + p) * ((2 : ℝ) ^ p *
        (e2_sbH j ^ p * (3 * e2_sbDelta j * r) + e2_sbTail j ^ p * (2 * r)))) := by
    symm
    simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add,
      ← ENNReal.ofReal_rpow_of_nonneg, ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_ofNat]
  have hnorm : (r⁻¹) ^ (1 + p) * ((2 : ℝ) ^ p *
      (e2_sbH j ^ p * (3 * e2_sbDelta j * r) + e2_sbTail j ^ p * (2 * r))) =
      (2 : ℝ) ^ p * (3 * e2_sbDelta j * (e2_sbH j / r) ^ p +
        2 * (e2_sbTail j / r) ^ p) := by
    rw [Real.inv_rpow hr.le, Real.rpow_add hr, Real.rpow_one,
      Real.div_rpow hh hr.le, Real.div_rpow ht hr.le]
    field_simp
  calc
    euclideanBetaPow e2_sbSource 1 p z r ≤
        (ENNReal.ofReal r)⁻¹ ^ (1 + p) *
          (∫⁻ w in Metric.ball z r, Metric.infEDist w L.toSet ^ p ∂e2_sbSource) := by
      simp only [euclideanBetaPow, ite_eq_left hr, Nat.cast_one]
      exact mul_le_mul' le_rfl (iInf_le _ L)
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (1 + p) * ((2 : ℝ≥0∞) ^ p *
        (ENNReal.ofReal (e2_sbH j) ^ p * ENNReal.ofReal (3 * e2_sbDelta j * r) +
         ENNReal.ofReal (e2_sbTail j) ^ p * ENNReal.ofReal (2 * r))) :=
      mul_le_mul' le_rfl hcost
    _ = ENNReal.ofReal ((2 : ℝ) ^ p * (3 * e2_sbDelta j * (e2_sbH j / r) ^ p +
        2 * (e2_sbTail j / r) ^ p)) := by rw [hraw, hnorm]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.rpow_nonneg (div_nonneg ht hr.le) p,
        Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p]

private lemma band_real_power_sum {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    (a + b) ^ q ≤ (2 : ℝ) ^ q * (a ^ q + b ^ q) := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  simpa (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add,
    ← ENNReal.ofReal_rpow_of_nonneg, ENNReal.ofReal_ofNat] using
    ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow (ENNReal.ofReal a) (ENNReal.ofReal b) hq

private lemma band_power_conversion {p δ h t r : ℝ} (hp : 0 < p)
    (hδ : 0 ≤ δ) (hh : 0 ≤ h) (ht : 0 ≤ t) (hr : 0 < r) :
    ((3 * (2 : ℝ) ^ p) * (δ * (h / r) ^ p + (t / r) ^ p)) ^ (2 / p) ≤
      ((3 * (2 : ℝ) ^ p) ^ (2 / p) * (2 : ℝ) ^ (2 / p)) *
        (δ ^ (2 / p) * (h / r) ^ 2 + (t / r) ^ 2) := by
  have hq : 0 ≤ 2 / p := by positivity
  have hpow (x : ℝ) (hx : 0 ≤ x) : (x ^ p) ^ (2 / p) = x ^ 2 := by
    rw [← Real.rpow_mul hx, show p * (2 / p) = 2 by field_simp, Real.rpow_two]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  calc
    (3 * (2 : ℝ) ^ p) ^ (2 / p) * (δ * (h / r) ^ p + (t / r) ^ p) ^ (2 / p) ≤
        (3 * (2 : ℝ) ^ p) ^ (2 / p) * ((2 : ℝ) ^ (2 / p) *
          ((δ * (h / r) ^ p) ^ (2 / p) + ((t / r) ^ p) ^ (2 / p))) := by
      gcongr
      exact band_real_power_sum (by positivity) (by positivity) hq
    _ = _ := by
      rw [Real.mul_rpow hδ (by positivity), hpow _ (by positivity), hpow _ (by positivity)]
      ring

/-- The scale-band estimate; its constant is uniform in the center,
generation and radius, for every real exponent `p > 0`. -/
theorem e2_sb_band_proof (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit)
    (hP : E2sbPeriodic) (hM : E2sbMeasurable) (hDen : E2sbDensity)
    (hL : E2PlanarLine) : E2sbBand := by
  intro p hp
  refine ⟨(3 * (2 : ℝ) ^ p) ^ (2 / p) * (2 : ℝ) ^ (2 / p), by positivity, ?_⟩
  intro z hz j hj r hrlo hrhi
  have hr : 0 < r := lt_of_lt_of_le (div_pos (hG.2.1 j) (by norm_num)) hrlo
  have hh := (hG.2.1 j).le
  have ht := hT.2.2.1 j
  have hd := (hG.2.2.2.2.2.2.2.2 j hj).1.le
  calc
    euclideanBetaPow e2_sbSource 1 p z r ^ (2 / p) ≤
        ENNReal.ofReal ((3 * (2 : ℝ) ^ p) *
          (e2_sbDelta j * (e2_sbH j / r) ^ p + (e2_sbTail j / r) ^ p)) ^ (2 / p) :=
      ENNReal.rpow_le_rpow (band_beta_bound hG hT hD hP hM hDen hL hp hz hj hrlo hrhi)
        (by positivity)
    _ = ENNReal.ofReal (((3 * (2 : ℝ) ^ p) *
          (e2_sbDelta j * (e2_sbH j / r) ^ p + (e2_sbTail j / r) ^ p)) ^ (2 / p)) :=
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (band_power_conversion hp hd hh ht hr)

end ParabolicRectifiability.Examples
