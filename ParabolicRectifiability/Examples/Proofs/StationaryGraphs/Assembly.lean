import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements
import ParabolicRectifiability.Characterization.Assembly.CoveringLemmas

/-! # Assembly of the stationary product estimates (`e2_stationary_assembly`)

The three clauses of `StationaryProductStatement` from `E2StationaryLengthStatement`,
`E2StationaryVerticalStatement` and `E2StationaryHorizontalStatement` (taken as hypotheses).

* clause 1 is the vertical identity;
* the mixed square is the minimum of the horizontal and vertical squares (`iInf_sum`);
* `ℓ / r² ∈ [1/2, 2]` from the length statement;
* lower: `(1/16) b ≤ β²_H` (horizontal bound) and `(1/16) b ≤ (1/2) b ≤ (ℓ/r²) b = β²_V`;
* upper: `β²_mixed ≤ β²_V = (ℓ/r²) b ≤ 2 b` (`betaSq_mixed_le_vertical`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-- The mixed squared beta is the minimum of the horizontal and vertical ones. -/
theorem e2sd_betaSq_mixed_eq_inf {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    {r : ℝ} (hr : 0 < r) :
    betaSq μ k .mixed z r = betaSq μ k .horizontal z r ⊓ betaSq μ k .vertical z r := by
  rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hr]
  have h : (⨅ L : Models n k .mixed, fit μ L z r) =
      (⨅ L : Models n k .horizontal, fit μ L z r) ⊓ ⨅ L : Models n k .vertical, fit μ L z r :=
    iInf_sum
  rw [h]
  rcases le_total (⨅ L : Models n k .horizontal, fit μ L z r)
      (⨅ L : Models n k .vertical, fit μ L z r) with hle | hle
  · rw [inf_eq_left.mpr hle, inf_eq_left.mpr (by gcongr)]
  · rw [inf_eq_right.mpr hle, inf_eq_right.mpr (by gcongr)]

theorem e2_stationary_assembly_proof : E2StationaryAssemblyStatement := by
  intro hA hB hC n hn m hmn ν hfin hreg x t r ht hr0 hr2
  have hV := hB n hn m hmn ν hfin hreg x t r ht hr0 hr2
  have hH := hC hA n hn m hmn ν hfin hreg x t r ht hr0 hr2
  obtain ⟨hl, hu⟩ := hA t r ht hr0 hr2
  have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
  have hp : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r ^ 2) := (ENNReal.ofReal_pow hr0.le 2).symm
  have hp0 : ENNReal.ofReal (r ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hr2pos).ne'
  have hpt : ENNReal.ofReal (r ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq2 : volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) / ENNReal.ofReal r ^ 2 ≤ 2 := by
    rw [hp]
    refine ENNReal.div_le_of_le_mul ?_
    calc _ ≤ ENNReal.ofReal (2 * r ^ 2) := hu
      _ = 2 * ENNReal.ofReal (r ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have hq1 : ENNReal.ofReal (1 / 2) ≤
      volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) / ENNReal.ofReal r ^ 2 := by
    rw [hp, ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl hpt), ← ENNReal.ofReal_mul (by norm_num)]
    refine le_trans (le_of_eq ?_) hl
    congr 1; ring
  have hmix := e2sd_betaSq_mixed_eq_inf (e2_stationarySource ν) (m + 2) (point x t) hr0
  refine ⟨hV, ?_, ?_⟩
  · show _ ≤ betaSq (e2_stationarySource ν) (m + 2) .mixed (point x t) r
    rw [hmix]
    refine le_inf hH ?_
    rw [hV]
    calc ENNReal.ofReal (1 / 16) * euclideanBetaPow ν m 2 x r
        ≤ ENNReal.ofReal (1 / 2) * euclideanBetaPow ν m 2 x r := by
          gcongr; norm_num
      _ ≤ _ := by gcongr
  · show betaSq (e2_stationarySource ν) (m + 2) .mixed (point x t) r ≤ _
    calc _ ≤ betaSq (e2_stationarySource ν) (m + 2) .vertical (point x t) r :=
          Characterization.betaSq_mixed_le_vertical _ _ _ _
      _ ≤ _ := by rw [hV]; gcongr

end ParabolicRectifiability.Examples
