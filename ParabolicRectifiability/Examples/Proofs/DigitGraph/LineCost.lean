import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Line-cost lower bound for the dispersed digit graph

If `J = (x₀ - h_j, x₀ + h_j)` lies in one generation-`(j-1)` interval, then every affine line
`L` satisfies `∫_J dist(T(x), L)^2 dx ≥ δ_j h_j^3/16` (`e2_sb_lineCost_proof`), by the
two-height variance estimate `E2Variance` applied to the marked bit `b_j`. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private lemma bit_zero_or_one (j : ℕ) (x : ℝ) :
    e2_sbBit j x = 0 ∨ e2_sbBit j x = 1 := by
  classical
  by_cases hx : x ∈ e2_sbMarked j
  · exact Or.inr (by simp [e2_sbBit, hx])
  · exact Or.inl (by simp [e2_sbBit, hx])

private lemma affine_sq_integrable (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (a b c A B : ℝ) (hAB : A ≤ B) :
    IntervalIntegrable (fun x => (a * x + b * f x - c) ^ 2) volume A B := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).2
  apply IntegrableOn.of_bound (measure_Icc_lt_top)
    (((measurable_const.mul measurable_id).add (measurable_const.mul hf)).sub
      measurable_const |>.pow_const 2 |>.aestronglyMeasurable)
    ((|a| * (|A| + |B|) + |b| * C + |c|) ^ 2)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hxabs : |x| ≤ |A| + |B| := abs_le.mpr ⟨by
    have := neg_abs_le A; have := abs_nonneg B; linarith [hx.1], by
    have := le_abs_self B; have := abs_nonneg A; linarith [hx.2]⟩
  have habs : |a * x + b * f x - c| ≤ |a| * (|A| + |B|) + |b| * C + |c| := by
    calc
      _ ≤ |a * x + b * f x| + |c| := abs_sub _ _
      _ ≤ |a * x| + |b * f x| + |c| := by
        linarith [abs_add_le (a * x) (b * f x)]
      _ = |a| * |x| + |b| * |f x| + |c| := by rw [abs_mul, abs_mul]
      _ ≤ _ := by gcongr; exact hC x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (a * x + b * f x - c) ^ 2 ≤ _
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans habs)).2 habs

private lemma old_height_on_cell (hD : E2sbDigit) (j : ℕ) (k : ℤ)
    (x x₀ : ℝ)
    (hx : x ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j))
    (hx₀ : x₀ ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j)) :
    e2_sbOldHeight j x = e2_sbOldHeight j x₀ := by
  unfold e2_sbOldHeight
  apply Finset.sum_congr rfl
  intro i hi
  rw [hD.1 j (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega) k x x₀ hx hx₀]

private lemma old_height_step (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    e2_sbOldHeight j x = e2_sbOldHeight (j - 1) x + e2_sbH j * e2_sbBit j x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp [e2_sbOldHeight, Finset.sum_range_succ]

/-- The line-cost lower bound, from the grid, tail, digit, periodicity, measurability,
covariance, variance and planar-line statements. -/
theorem e2_sb_lineCost_proof (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit)
    (hP : E2sbPeriodic) (hM : E2sbMeasurable) (hPr : E2sbPrimitive)
    (hV : E2Variance) (hL : E2PlanarLine) : E2sbLineCost := by
  intro j hj k x₀ hlo hhi L
  obtain ⟨a, b, c, hab, hdist⟩ := hL.1 L
  let h := e2_sbH j
  let δ := e2_sbDelta j
  let P := e2_sbPeriod j
  let Y := e2_sbOldHeight (j - 1) x₀
  let A := x₀ - h
  let B := x₀ + h
  let u := fun x : ℝ => a * x + (b * h) * e2_sbBit j x - (c - b * Y)
  let v := fun x : ℝ => a * x + b * e2_sbHeight x - c
  have hh : 0 < h := hG.2.1 j
  have hAB : A ≤ B := by dsimp [A, B]; linarith
  have hδ : 0 < δ ∧ δ ≤ 1 / 2 := hG.2.2.2.2.2.2.2.2 j hj
  have hscale : 2 ^ 10 * P = h := (hG.2.2.2.2.2.2.1 j hj).symm
  have hPpos : 0 < P := by nlinarith [hh]
  have hbit : Measurable (e2_sbBit j) := measurable_const.indicator (hM.1 j)
  have hbabs (x : ℝ) : |e2_sbBit j x| ≤ 1 := by
    rcases bit_zero_or_one j x with hx | hx <;> simp [hx]
  have hheight (x : ℝ) : |e2_sbHeight x| ≤ e2_sbTail 0 := by
    have hx := hD.2.1 0 x
    simp only [e2_sbOldHeight, Finset.range_zero, Finset.sum_empty, sub_zero] at hx
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have hui : IntervalIntegrable (fun x => u x ^ 2) volume A B :=
    affine_sq_integrable (e2_sbBit j) hbit 1 hbabs a (b * h) (c - b * Y) A B hAB
  have hvi : IntervalIntegrable (fun x => v x ^ 2) volume A B :=
    affine_sq_integrable e2_sbHeight hM.2.1 (e2_sbTail 0) hheight a b c A B hAB
  have hmean : |(∫ X in (-h)..h, e2_sbBit j (x₀ + X)) - 2 * h * δ| ≤ 2 * δ * P := by
    rw [intervalIntegral.integral_comp_add_left]
    have hm := hP.1 j hj A B hAB
    have hlen : B - A = 2 * h := by dsimp [A, B]; ring
    have hprod : e2_sbDelta j * (2 * h) = 2 * h * δ := by dsimp [δ]; ring
    rw [hlen, hprod] at hm
    simpa only [A, B, sub_eq_add_neg] using hm
  have hideal0 := hV h δ P (fun X => e2_sbBit j (x₀ + X)) hh hδ.1 hδ.2 hPpos
    hscale.le (hbit.comp (measurable_const.add measurable_id))
    (fun X => bit_zero_or_one j (x₀ + X)) hmean (hPr j hj x₀ h hh)
    a b (c - a * x₀ - b * Y) hab
  have hideal : δ * h ^ 3 / 4 ≤ ∫ x in A..B, u x ^ 2 := by
    have heq : (∫ X in (-h)..h,
        (a * X + b * h * e2_sbBit j (x₀ + X) - (c - a * x₀ - b * Y)) ^ 2) =
        ∫ X in (-h)..h, u (x₀ + X) ^ 2 := by
      congr 1
      funext X
      dsimp [u]
      ring
    rw [heq, intervalIntegral.integral_comp_add_left (fun x => u x ^ 2) x₀] at hideal0
    simpa only [A, B, sub_eq_add_neg] using hideal0
  have hx₀ : x₀ ∈ Ico ((k : ℝ) * e2_sbEll (j - 1))
      (((k : ℝ) + 1) * e2_sbEll (j - 1)) := by
    constructor <;> dsimp [h] at hh <;> linarith
  have hpoint (x : ℝ) (hx : x ∈ Ioo A B) :
      u x ^ 2 / 2 - e2_sbTail j ^ 2 ≤ v x ^ 2 := by
    have hxcell : x ∈ Ico ((k : ℝ) * e2_sbEll (j - 1))
        (((k : ℝ) + 1) * e2_sbEll (j - 1)) := by
      dsimp [A, B, h] at hx
      constructor <;> linarith [hx.1, hx.2]
    have hold := old_height_on_cell hD (j - 1) k x x₀ hxcell hx₀
    have htail := hD.2.1 j x
    rw [old_height_step j hj x, hold] at htail
    have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
    have heta : 0 ≤ e2_sbTail j := hT.2.2.1 j
    have he2 : (e2_sbHeight x - (Y + h * e2_sbBit j x)) ^ 2 ≤ e2_sbTail j ^ 2 := by
      dsimp [Y, h]
      nlinarith [htail.1, htail.2]
    have hbe2 : (b * (e2_sbHeight x - (Y + h * e2_sbBit j x))) ^ 2 ≤ e2_sbTail j ^ 2 := by
      nlinarith [sq_nonneg (e2_sbHeight x - (Y + h * e2_sbBit j x)),
        mul_le_mul_of_nonneg_right hb2 (sq_nonneg (e2_sbHeight x - (Y + h * e2_sbBit j x)))]
    have hvu : v x = u x + b * (e2_sbHeight x - (Y + h * e2_sbBit j x)) := by
      dsimp [u, v]; ring
    rw [hvu]
    nlinarith [sq_nonneg (u x + 2 * (b * (e2_sbHeight x - (Y + h * e2_sbBit j x))))]
  have hcomp := intervalIntegral.integral_mono_on_of_le_Ioo hAB
    ((hui.div_const 2).sub (intervalIntegrable_const)) hvi hpoint
  rw [intervalIntegral.integral_sub (hui.div_const 2) intervalIntegrable_const,
    intervalIntegral.integral_div, intervalIntegral.integral_const] at hcomp
  simp only [smul_eq_mul] at hcomp
  have htail2 : e2_sbTail j ^ 2 ≤ δ * h ^ 2 / 32 := hT.2.2.2.2.2.2.1 j hj
  have hactual : δ * h ^ 3 / 16 ≤ ∫ x in A..B, v x ^ 2 := by
    have he := mul_le_mul_of_nonneg_left htail2 hh.le
    dsimp [A, B] at hcomp
    nlinarith
  have hactualSet : δ * h ^ 3 / 16 ≤ ∫ x in Ioo A B, v x ^ 2 := by
    simpa only [intervalIntegral.integral_of_le hAB, integral_Ioc_eq_integral_Ioo] using hactual
  have hvset : IntegrableOn (fun x => v x ^ 2) (Ioo A B) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hAB).1 hvi
  calc
    ENNReal.ofReal (δ * h ^ 3 / 16) ≤ ENNReal.ofReal (∫ x in Ioo A B, v x ^ 2) :=
      ENNReal.ofReal_le_ofReal hactualSet
    _ = ∫⁻ x in Ioo A B, ENNReal.ofReal (v x ^ 2) :=
      ofReal_integral_eq_lintegral_ofReal hvset (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    _ = _ := by
      apply lintegral_congr
      intro x
      rw [hdist, ENNReal.rpow_two]
      change ENNReal.ofReal (v x ^ 2) = ENNReal.ofReal |v x| ^ (2 : ℕ)
      rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

end ParabolicRectifiability.Examples
