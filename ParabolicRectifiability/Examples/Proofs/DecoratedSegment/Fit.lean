import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Fitting a baseline and its satellite against a unit normal

The tilted case uses its explicit hypothesis. When the normal is nearly vertical,
either the offset separates the baseline, or the vertical coefficient separates
the satellite. In both cases the distance is at least `h / 4` throughout one interval.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private lemma e2_sap_interval_cost {a b h p : ℝ} (hh : 0 < h) (hp : 0 ≤ p)
    (f : ℝ → ℝ) (hf : ∀ s ∈ Icc a b, h / 4 ≤ |f s|) :
    ENNReal.ofReal ((h / 4) ^ p * (b - a)) ≤
      ∫⁻ s in Icc a b, ENNReal.ofReal |f s| ^ p := by
  calc
    ENNReal.ofReal ((h / 4) ^ p * (b - a)) =
        (∫⁻ _s in Icc a b, ENNReal.ofReal (h / 4) ^ p) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hp]
    _ ≤ _ := setLIntegral_mono' measurableSet_Icc fun s hs =>
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hf s hs)) hp

private lemma e2_sap_scale_cost {h p : ℝ} (hh : 0 < h) :
    (h / 4) ^ p * h = (4 : ℝ) ^ (-p) * h ^ (p + 1) := by
  rw [Real.div_rpow hh.le (by norm_num), Real.rpow_add_one hh.ne',
    Real.rpow_neg (by norm_num)]
  ring

private lemma e2_sap_satellite_separation {h δ ξ α β c : ℝ}
    (hh : 0 < h) (hδ : δ ≤ 1 / 4) (hξ : |ξ| ≤ h / 2)
    (hα : |α| < 1 / 4) (hc : |c| < h / 2) (hn : α ^ 2 + β ^ 2 = 1) :
    ∀ s ∈ Icc (ξ - δ * h / 2) (ξ + δ * h / 2),
      h / 4 ≤ |α * s + β * h - c| := by
  have hβ : (15 : ℝ) / 16 ≤ |β| := by
    by_contra hb
    have ha2 := mul_self_le_mul_self (abs_nonneg α) hα.le
    have hb2 := mul_self_le_mul_self (abs_nonneg β) (le_of_lt (lt_of_not_ge hb))
    nlinarith [sq_abs α, sq_abs β]
  intro s hs
  have hsabs : |s| ≤ 5 * h / 8 := by
    rcases abs_le.mp hξ with ⟨hξl, hξu⟩
    apply abs_le.mpr
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hδ hh.le, hs.1, hs.2]
  have has : |α * s| ≤ 5 * h / 32 := by
    rw [abs_mul]
    have ht := mul_le_mul hα.le hsabs (abs_nonneg s) (by norm_num : (0:ℝ) ≤ 1/4)
    nlinarith
  have hbh : 15 * h / 16 ≤ |β * h| := by
    rw [abs_mul, abs_of_pos hh]
    nlinarith [mul_le_mul_of_nonneg_right hβ hh.le]
  have htri : |β * h| ≤ |α * s + β * h - c| + |α * s| + |c| := by
    calc
      |β * h| = |(α * s + β * h - c) - α * s + c| := by congr 1; ring
      _ ≤ |(α * s + β * h - c) - α * s| + |c| := abs_add_le _ _
      _ ≤ (|α * s + β * h - c| + |α * s|) + |c| :=
        add_le_add (abs_sub _ _) le_rfl
  linarith

/-- The baseline/satellite fitting estimate, assuming only the tilted-line estimate. -/
theorem e2_sap_fit_proof (hT : E2sapFitTilted) : E2sapFit := by
  intro p hp h δ ξ hh hδ hδq hξ α β c hn
  have hp0 : 0 ≤ p := by linarith
  have hpow : 0 ≤ (4 : ℝ) ^ (-p) := Real.rpow_nonneg (by norm_num) _
  have hhpow : 0 ≤ h ^ (p + 1) := Real.rpow_nonneg hh.le _
  have hden : 0 < p + 1 := by linarith
  have hmin0 : 0 ≤ min (1 : ℝ) (2 / (p + 1)) := by positivity
  have hmin1 : min (1 : ℝ) (2 / (p + 1)) ≤ 1 := min_le_left _ _
  have hmin2 : min (1 : ℝ) (2 / (p + 1)) ≤ 2 / (p + 1) := min_le_right _ _
  have hc1 : e2_sapFitConst p ≤ (4 : ℝ) ^ (-p) := by
    simpa only [e2_sapFitConst, mul_one] using mul_le_mul_of_nonneg_left hmin1 hpow
  have hc0 : 0 ≤ e2_sapFitConst p := mul_nonneg hpow hmin0
  by_cases hα : 1 / 4 ≤ |α|
  · have hcoef : e2_sapFitConst p * δ ≤ 2 * (4 : ℝ) ^ (-p) / (p + 1) := by
      calc
        e2_sapFitConst p * δ ≤ e2_sapFitConst p * 1 :=
          mul_le_mul_of_nonneg_left (by linarith : δ ≤ 1) hc0
        _ ≤ (4 : ℝ) ^ (-p) * (2 / (p + 1)) := by
          simpa only [e2_sapFitConst, mul_one] using mul_le_mul_of_nonneg_left hmin2 hpow
        _ = _ := by ring
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef hhpow)).trans
      ((hT p (by linarith) h hh α c hα).trans le_self_add)
  have hαsmall : |α| < 1 / 4 := lt_of_not_ge hα
  have htarget : e2_sapFitConst p * δ * h ^ (p + 1) ≤
      (h / 4) ^ p * (δ * h) := by
    calc
      _ ≤ (4 : ℝ) ^ (-p) * δ * h ^ (p + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 hδ.le) hhpow
      _ = δ * ((4 : ℝ) ^ (-p) * h ^ (p + 1)) := by ring
      _ = δ * ((h / 4) ^ p * h) := by rw [e2_sap_scale_cost hh]
      _ = _ := by ring
  by_cases hc : h / 2 ≤ |c|
  · have hsep : ∀ s ∈ Icc (-h) h, h / 4 ≤ |α * s - c| := by
      intro s hs
      have hsabs : |s| ≤ h := abs_le.mpr hs
      have has : |α * s| ≤ h / 4 := by
        rw [abs_mul]
        have ht := mul_le_mul hαsmall.le hsabs (abs_nonneg s)
          (by norm_num : (0:ℝ) ≤ 1 / 4)
        linarith
      have ht : |c| ≤ |α * s - c| + |α * s| := by
        simpa only [sub_zero, abs_sub_comm] using (abs_sub_le c (α * s) 0)
      linarith
    have hlen : δ * h ≤ h - -h := by nlinarith
    have hcost := e2_sap_interval_cost hh hp0 (fun s => α * s - c) hsep
    apply le_trans _ (hcost.trans le_self_add)
    apply ENNReal.ofReal_le_ofReal
    exact htarget.trans (mul_le_mul_of_nonneg_left hlen (Real.rpow_nonneg (by positivity) _))
  · have hsep := e2_sap_satellite_separation hh hδq hξ hαsmall (lt_of_not_ge hc) hn
    have hcost := e2_sap_interval_cost hh hp0 (fun s => α * s + β * h - c) hsep
    have hlen : (ξ + δ * h / 2) - (ξ - δ * h / 2) = δ * h := by ring
    rw [hlen] at hcost
    exact (ENNReal.ofReal_le_ofReal htarget).trans (hcost.trans le_add_self)

end ParabolicRectifiability.Examples
