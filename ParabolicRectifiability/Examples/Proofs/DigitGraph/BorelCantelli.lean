import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Parameters eventually inside one parent cell

By Borel–Cantelli, for almost every `x ∈ [0,1)` and all large `j`, the interval
`[x - h_j, x + h_j]` lies in one generation-`(j-1)` grid interval
(`e2_sb_borelCantelli_proof`): the parameters whose interval crosses a cell boundary have
summable measures. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

/-- The points whose symmetric interval crosses a cell boundary. -/
private def boundaryBad (ell h : ℝ) : Set ℝ :=
  {x | ¬ ∃ k : ℤ, (k : ℝ) * ell ≤ x - h ∧ x + h ≤ ((k : ℝ) + 1) * ell}

/-- Each cell contributes at most two intervals of length `h`. -/
private lemma boundaryBad_measure (ell h : ℝ) (hell : 0 < ell) (hh : 0 ≤ h)
    (c : ℕ) (hc : (c : ℝ) * ell = 1) :
    (volume.restrict (Ico (0 : ℝ) 1)) (boundaryBad ell h) ≤
      ENNReal.ofReal ((c : ℝ) * (2 * h)) := by
  classical
  let U (k : ℕ) : Set ℝ :=
    Icc ((k : ℝ) * ell) ((k : ℝ) * ell + h) ∪
      Icc (((k : ℝ) + 1) * ell - h) (((k : ℝ) + 1) * ell)
  have cover : boundaryBad ell h ∩ Ico (0 : ℝ) 1 ⊆
      ⋃ k ∈ Finset.range c, U k := by
    rintro x ⟨hbad, hx⟩
    let k : ℕ := ⌊x / ell⌋₊
    have hx0 : 0 ≤ x / ell := div_nonneg hx.1 hell.le
    have hk : k < c := by
      apply (Nat.floor_lt hx0).2
      apply (div_lt_iff₀ hell).2
      simpa [hc] using hx.2
    have hleft : (k : ℝ) * ell ≤ x := (le_div_iff₀ hell).1 (Nat.floor_le hx0)
    have hright : x < ((k : ℝ) + 1) * ell :=
      (div_lt_iff₀ hell).1 (Nat.lt_floor_add_one (x / ell))
    refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨Finset.mem_range.2 hk, ?_⟩⟩
    by_cases hl : (k : ℝ) * ell ≤ x - h
    · have hr : ((k : ℝ) + 1) * ell < x + h := by
        by_contra! hn
        exact hbad ⟨(k : ℤ), by exact_mod_cast hl, by exact_mod_cast hn⟩
      exact Or.inr ⟨by linarith, hright.le⟩
    · exact Or.inl ⟨hleft, by linarith⟩
  rw [Measure.restrict_apply' measurableSet_Ico]
  calc
    volume (boundaryBad ell h ∩ Ico 0 1) ≤ volume (⋃ k ∈ Finset.range c, U k) :=
      measure_mono cover
    _ ≤ ∑ k ∈ Finset.range c, volume (U k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range c, ENNReal.ofReal (2 * h) := by
      apply Finset.sum_le_sum
      intro k _hk
      calc
        volume (U k) ≤ volume (Icc ((k : ℝ) * ell) ((k : ℝ) * ell + h)) +
            volume (Icc (((k : ℝ) + 1) * ell - h) (((k : ℝ) + 1) * ell)) :=
          measure_union_le _ _
        _ = ENNReal.ofReal (2 * h) := by
          simp only [Real.volume_Icc, add_sub_cancel_left, sub_sub_cancel]
          rw [← ENNReal.ofReal_add hh hh]
          congr 1
          ring
    _ = ENNReal.ofReal ((c : ℝ) * (2 * h)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The boundary errors are summable, so almost every parameter is eventually
inside one parent cell with the required margin. -/
theorem e2_sb_borelCantelli_proof (hG : E2sbGrid) (_hT : E2sbTails) :
    E2sbBorelCantelli := by
  let μ := volume.restrict (Ico (0 : ℝ) 1)
  let B (n : ℕ) := boundaryBad (e2_sbEll n) (e2_sbH (n + 1))
  have bound (n : ℕ) : μ (B n) ≤ ENNReal.ofReal (2 / 2 ^ (n + 21) : ℝ) := by
    obtain ⟨c, hc⟩ := hG.2.2.2.2.1 n
    calc
      μ (B n) ≤ ENNReal.ofReal ((c : ℝ) * (2 * e2_sbH (n + 1))) :=
        boundaryBad_measure _ _ (hG.1 n) (hG.2.1 (n + 1)).le c hc
      _ = ENNReal.ofReal (2 / 2 ^ (n + 21) : ℝ) := by
        congr 1
        simp only [e2_sbH]
        calc
          (c : ℝ) * (2 * (e2_sbEll n / 2 ^ (n + 21))) =
              2 * ((c : ℝ) * e2_sbEll n) / 2 ^ (n + 21) := by ring
          _ = _ := by rw [hc]; ring
  have hs : Summable (fun n : ℕ => (2 / 2 ^ (n + 21) : ℝ)) := by
    have hs' := summable_geometric_two.mul_left (2 / 2 ^ (21 : ℕ) : ℝ)
    convert hs' using 1
    ext n
    simp only [div_pow, one_pow, pow_add]
    ring
  have hsum : (∑' n, μ (B n)) ≠ ∞ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum bound)
  have hae := ae_eventually_notMem hsum
  filter_upwards [hae] with x hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx
  apply eventually_atTop.2
  refine ⟨N + 1, fun j hj => ?_⟩
  have hj1 : 1 ≤ j := by omega
  have h := hN (j - 1) (by omega)
  change ¬ ¬ ∃ k : ℤ, (k : ℝ) * e2_sbEll (j - 1) ≤ x - e2_sbH (j - 1 + 1) ∧
    x + e2_sbH (j - 1 + 1) ≤ ((k : ℝ) + 1) * e2_sbEll (j - 1) at h
  simpa only [Nat.sub_add_cancel hj1, not_not] using h

end ParabolicRectifiability.Examples
