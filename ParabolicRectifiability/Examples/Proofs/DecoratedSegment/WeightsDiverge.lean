import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements
import Mathlib.Analysis.PSeries

/-! # Divergence of fractional powers of the decorated-segment weights

For `0 < q < 1`, the logarithmic denominator is bounded by a sufficiently small
positive power of `j + 1`. After taking the power `q`, this gives a positive
constant times the harmonic sequence as a lower bound.
-/

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- A power bound for the logarithmic denominator of the segment weights. -/
private lemma e2_sap_delta_lower_bound (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    1 / ((100 * (1 + 1 / ε) ^ 2) * ((j : ℝ) + 1) ^ (1 + 2 * ε)) ≤
      e2_sapDelta j := by
  let x : ℝ := (j : ℝ) + 1
  have hx : 1 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_left (Nat.cast_nonneg j)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hbound : 1 + Real.log x ≤ (1 + 1 / ε) * x ^ ε := by
    calc
      1 + Real.log x ≤ x ^ ε + x ^ ε / ε :=
        add_le_add (Real.one_le_rpow hx hε.le) (Real.log_le_rpow_div hxpos.le hε)
      _ = (1 + 1 / ε) * x ^ ε := by ring
  have hsq : (1 + Real.log x) ^ 2 ≤ (1 + 1 / ε) ^ 2 * x ^ (2 * ε) := by
    calc
      (1 + Real.log x) ^ 2 ≤ ((1 + 1 / ε) * x ^ ε) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hbound 2
      _ = (1 + 1 / ε) ^ 2 * x ^ (2 * ε) := by
        rw [mul_pow]
        congr 1
        simpa only [Nat.cast_ofNat, mul_comm] using
          (Real.rpow_mul_natCast hxpos.le ε 2).symm
  have hden : 100 * x * (1 + Real.log x) ^ 2 ≤
      (100 * (1 + 1 / ε) ^ 2) * x ^ (1 + 2 * ε) := by
    calc
      100 * x * (1 + Real.log x) ^ 2 ≤
          100 * x * ((1 + 1 / ε) ^ 2 * x ^ (2 * ε)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (100 * (1 + 1 / ε) ^ 2) * x ^ (1 + 2 * ε) := by
        rw [Real.rpow_add hxpos, Real.rpow_one]
        ring
  exact one_div_le_one_div_of_le (by positivity) hden

/-- Every power below one of the decorated-segment weights has infinite sum. -/
theorem e2_sap_weightsDiverge_proof : E2sapWeightsDiverge := by
  intro q hq hq1
  let ε : ℝ := (1 - q) / (2 * q)
  have hε : 0 < ε := div_pos (sub_pos.mpr hq1) (by positivity)
  let C : ℝ := 100 * (1 + 1 / ε) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hexp : (1 + 2 * ε) * q = 1 := by
    dsimp [ε]
    field_simp [ne_of_gt hq]
    ring
  have hlower (j : ℕ) :
      (1 / C ^ q) * (1 / ((j : ℝ) + 1)) ≤ e2_sapDelta j ^ q := by
    have hx : 0 < (j : ℝ) + 1 := by positivity
    have hp : (1 / (C * ((j : ℝ) + 1) ^ (1 + 2 * ε))) ^ q ≤
        e2_sapDelta j ^ q :=
      Real.rpow_le_rpow (by positivity) (e2_sap_delta_lower_bound ε hε j) hq.le
    simpa only [Real.div_rpow zero_le_one (by positivity :
        0 ≤ C * ((j : ℝ) + 1) ^ (1 + 2 * ε)), Real.one_rpow,
      Real.mul_rpow hC.le (Real.rpow_nonneg hx.le _),
      ← Real.rpow_mul hx.le, hexp, Real.rpow_one, one_div_mul_one_div] using hp
  by_contra hfinite
  have hs : Summable (fun j : ℕ => e2_sapDelta j ^ q) := by
    refine (ENNReal.summable_toReal hfinite).congr fun j => ?_
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg (by
      unfold e2_sapDelta
      positivity) q)
  have hscaled : Summable (fun j : ℕ => (1 / C ^ q) * (1 / ((j : ℝ) + 1))) :=
    hs.of_nonneg_of_le (fun j => by positivity) hlower
  have hharm : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1)) :=
    (summable_mul_left_iff (by positivity : (1 / C ^ q) ≠ 0)).mp hscaled
  have hfalse := (Real.summable_one_div_nat_add_rpow 1 1).mp (by
    convert hharm using 1
    funext j
    rw [Real.rpow_one, abs_of_pos (by positivity : 0 < (j : ℝ) + 1)])
  exact (lt_irrefl (1 : ℝ)) hfalse

end ParabolicRectifiability.Examples
