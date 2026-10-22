import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor

/-! # Periodicity of the marked digits

For `j ≥ 1`, the marked-bit indicator `b_j` is periodic with period `P_j` and mean `δ_j`. Its
discrepancy satisfies `|∫_a^b b_j - δ_j (b - a)| ≤ 2 δ_j P_j` on every bounded interval, and
the marked set has mass at most `3 δ_j r` in every interval of radius `r ≥ h_j/4`
(`e2_sb_periodic_proof`). -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private theorem marked_measurable (j : ℕ) : MeasurableSet (e2_sbMarked j) := by
  change MeasurableSet ((fun x : ℝ => ⌊x / e2_sbEll j⌋) ⁻¹' {z : ℤ | ((j + 1 : ℕ) : ℤ) ∣ z})
  exact ((Set.to_countable {z : ℤ | ((j + 1 : ℕ) : ℤ) ∣ z}).measurableSet).preimage
    (measurable_id.div_const _).floor

private theorem bit_nonneg (j : ℕ) (x : ℝ) : 0 ≤ e2_sbBit j x := by
  classical
  simp only [e2_sbBit, Set.indicator_apply]
  split_ifs <;> norm_num

private theorem bit_integrable (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (e2_sbBit j) volume a b := by
  apply intervalIntegrable_iff.mpr
  exact (intervalIntegrable_const (c := (1 : ℝ))).def'.indicator (marked_measurable j)

private theorem bit_periodic (j : ℕ) (hl : 0 < e2_sbEll j) :
    Function.Periodic (e2_sbBit j) (e2_sbPeriod j) := by
  classical
  intro x
  have hf : ⌊(x + e2_sbPeriod j) / e2_sbEll j⌋ = ⌊x / e2_sbEll j⌋ + (j + 1 : ℕ) := by
    rw [e2_sbPeriod, add_div, mul_div_cancel_right₀ _ hl.ne']
    exact_mod_cast Int.floor_add_intCast (x / e2_sbEll j) ((j + 1 : ℕ) : ℤ)
  simp [e2_sbBit, Set.indicator_apply, e2_sbMarked, hf, dvd_add_self_right]

private theorem marked_first_period (j : ℕ) (hl : 0 < e2_sbEll j)
    {x : ℝ} (hx : x ∈ Ico 0 (e2_sbPeriod j)) :
    x ∈ e2_sbMarked j ↔ x < e2_sbEll j := by
  have h0 : 0 ≤ ⌊x / e2_sbEll j⌋ := Int.floor_nonneg.mpr (div_nonneg hx.1 hl.le)
  have hq : ⌊x / e2_sbEll j⌋ < ((j + 1 : ℕ) : ℤ) := by
    apply Int.floor_lt.mpr
    simpa [e2_sbPeriod, Nat.cast_add, Nat.cast_one] using (div_lt_iff₀ hl).mpr hx.2
  change ((j + 1 : ℕ) : ℤ) ∣ ⌊x / e2_sbEll j⌋ ↔ _
  constructor
  · intro h
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt h0 hq h
    have := (Int.floor_eq_zero_iff.mp hz).2
    exact (div_lt_one hl).mp this
  · intro h
    have hz : ⌊x / e2_sbEll j⌋ = 0 := Int.floor_eq_zero_iff.mpr
      ⟨div_nonneg hx.1 hl.le, (div_lt_one hl).mpr h⟩
    simp [hz]

private theorem bit_first_period (j : ℕ) (hl : 0 < e2_sbEll j)
    {x : ℝ} (hx : x ∈ Ico 0 (e2_sbPeriod j)) :
    e2_sbBit j x = (Iio (e2_sbEll j)).indicator (fun _ => (1 : ℝ)) x := by
  classical
  simp [e2_sbBit, Set.indicator_apply, marked_first_period j hl hx]

private theorem bit_period_integral (j : ℕ) (hl : 0 < e2_sbEll j) :
    (∫ x in 0..e2_sbPeriod j, e2_sbBit j x) = e2_sbEll j := by
  classical
  have hp : 0 < e2_sbPeriod j := by unfold e2_sbPeriod; positivity
  have hlp : e2_sbEll j ≤ e2_sbPeriod j := by
    unfold e2_sbPeriod
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hfirst : (∫ x in 0..e2_sbEll j, e2_sbBit j x) = e2_sbEll j := by
    calc
      _ = ∫ _ in (0 : ℝ)..e2_sbEll j, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hl.le
        intro x hx
        rw [bit_first_period j hl ⟨hx.1.le, hx.2.trans_le hlp⟩]
        simp [hx.2]
      _ = _ := by simp
  have hsecond : (∫ x in e2_sbEll j..e2_sbPeriod j, e2_sbBit j x) = 0 := by
    calc
      _ = ∫ _ in e2_sbEll j..e2_sbPeriod j, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hlp
        intro x hx
        rw [bit_first_period j hl ⟨hl.le.trans hx.1.le, hx.2⟩]
        simp [not_lt.mpr hx.1.le]
      _ = _ := by simp
  linarith [intervalIntegral.integral_add_adjacent_intervals
    (bit_integrable j 0 (e2_sbEll j)) (bit_integrable j (e2_sbEll j) (e2_sbPeriod j))]

private theorem delta_period (j : ℕ) :
    e2_sbDelta j * e2_sbPeriod j = e2_sbEll j := by
  have hq : (j : ℝ) + 1 ≠ 0 := by positivity
  dsimp [e2_sbDelta, e2_sbPeriod]
  field_simp

/-- A nonnegative periodic integrand with mean mass `L` has discrepancy at most `2L`.
The proof reduces each endpoint to its fractional period, so it also covers negative endpoints. -/
private theorem periodic_discrepancy {f : ℝ → ℝ} {P δ L : ℝ}
    (hp : 0 < P) (hδ : 0 ≤ δ) (hmean : δ * P = L)
    (hper : Function.Periodic f P) (hfi : ∀ a b, IntervalIntegrable f volume a b)
    (hf : ∀ x, 0 ≤ f x) (hmass : (∫ x in 0..P, f x) = L) (a b : ℝ) :
    |(∫ x in a..b, f x) - δ * (b - a)| ≤ 2 * L := by
  let g : ℝ → ℝ := fun x => f x - δ
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b =>
    (hfi a b).sub intervalIntegrable_const
  have hg : Function.Periodic g P := by intro x; dsimp [g]; rw [hper x]
  have hgmean : (∫ x in 0..P, g x) = 0 := by
    dsimp [g]
    rw [intervalIntegral.integral_sub (hfi 0 P) intervalIntegrable_const, hmass]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    linarith
  have hprimitive : ∀ t : ℝ, -L ≤ (∫ x in 0..t, g x) ∧ (∫ x in 0..t, g x) ≤ L := by
    intro t
    let ε := Int.fract (t / P) * P
    have hε : ε ∈ Ico 0 P := Int.fract_div_mul_self_mem_Ico P t hp
    have hrepr : ε + ⌊t / P⌋ • P = t := Int.fract_div_mul_self_add_zsmul_eq P t hp.ne'
    have hz := hg.intervalIntegral_add_zsmul_eq ⌊t / P⌋ ε hgi
    have hshift := hg.intervalIntegral_add_eq ε 0
    simp only [zero_add, hgmean] at hshift hz
    rw [hshift] at hz
    simp only [smul_zero] at hz
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgi 0 ε) (hgi ε (ε + ⌊t / P⌋ • P))
    rw [hz, hrepr, add_zero] at hsplit
    rw [← hsplit]
    have hn : 0 ≤ ∫ x in 0..ε, f x := intervalIntegral.integral_nonneg_of_forall hε.1 hf
    have hu : (∫ x in 0..ε, f x) ≤ L := by
      rw [← hmass]
      exact intervalIntegral.integral_mono_interval le_rfl hε.1 hε.2.le
        (Eventually.of_forall hf) (hfi 0 P)
    have hdε : 0 ≤ δ * ε := mul_nonneg hδ hε.1
    have hdε' : δ * ε ≤ L := by nlinarith [mul_le_mul_of_nonneg_left hε.2.le hδ]
    dsimp [g]
    rw [intervalIntegral.integral_sub (hfi 0 ε) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    constructor <;> linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi 0 a) (hgi a b)
  have ha := hprimitive a
  have hb := hprimitive b
  have hbound : |∫ x in a..b, g x| ≤ 2 * L := abs_le.mpr ⟨by linarith, by linarith⟩
  dsimp [g] at hbound
  rw [intervalIntegral.integral_sub (hfi a b) intervalIntegrable_const] at hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm δ] using hbound

/-- Periodic marked mass discrepancy and the mass bound on every real centered interval. -/
theorem e2_sb_periodic_proof (hG : E2sbGrid) : E2sbPeriodic := by
  have hdisc : ∀ j, 1 ≤ j → ∀ a b : ℝ,
      |(∫ x in a..b, e2_sbBit j x) - e2_sbDelta j * (b - a)| ≤
        2 * e2_sbDelta j * e2_sbPeriod j := by
    intro j hj a b
    simpa only [delta_period, mul_assoc] using
      periodic_discrepancy (hG.1 j |> fun h =>
        show 0 < e2_sbPeriod j by unfold e2_sbPeriod; positivity)
        (hG.2.2.2.2.2.2.2.2 j hj).1.le (delta_period j)
        (bit_periodic j (hG.1 j)) (bit_integrable j) (bit_nonneg j)
        (bit_period_integral j (hG.1 j)) a b
  constructor
  · intro j hj a b _hab
    exact hdisc j hj a b
  · intro j hj x₀ r hr
    have hl := hG.1 j
    have hp : 0 < e2_sbPeriod j := by unfold e2_sbPeriod; positivity
    have hh : e2_sbH j = 2 ^ 10 * e2_sbPeriod j := hG.2.2.2.2.2.2.1 j hj
    have hδ : 0 < e2_sbDelta j := (hG.2.2.2.2.2.2.2.2 j hj).1
    have hδp : 0 ≤ e2_sbDelta j * e2_sbPeriod j := mul_nonneg hδ.le hp.le
    have hrpos : 0 < r := lt_of_lt_of_le (div_pos (hG.2.1 j) (by norm_num)) hr
    have hab : x₀ - r ≤ x₀ + r := by linarith
    have hfinite : volume (Ioo (x₀ - r) (x₀ + r) ∩ e2_sbMarked j) ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) measure_Ioo_lt_top)
    have heq : (∫ x in (x₀ - r)..(x₀ + r), e2_sbBit j x) =
        (volume (Ioo (x₀ - r) (x₀ + r) ∩ e2_sbMarked j)).toReal := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
      simp only [e2_sbBit, integral_indicator_const (1 : ℝ) (marked_measurable j),
        measureReal_restrict_apply (marked_measurable j), smul_eq_mul, mul_one]
      rw [inter_comm]
      rfl
    apply (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity), ← heq]
    have hd := (abs_le.mp (hdisc j hj (x₀ - r) (x₀ + r))).2
    have hpr : 2 * e2_sbPeriod j ≤ r := by rw [hh] at hr; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hpr hδ.le]

end ParabolicRectifiability.Examples
