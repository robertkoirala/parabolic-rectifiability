import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # Subquadratic energy of the dispersed digit graph at every endpoint

For `0 < p < 2` and every finite endpoint `a > 0`, the energy `S_{p,μ}^a` of the dispersed
digit source is bounded on `E` by a constant depending only on `p` and `a`
(`e2_sb_spAll_proof`). The small-scale bound up to `1/4` is a hypothesis; the bounded annulus
`[1/4, a)` is controlled with a line through the centre. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane)

private theorem source_mass (hM : E2sbMeasurable) : e2_sbSource univ = 1 := by
  simp [e2_sbSource, Measure.map_apply hM.2.2 MeasurableSet.univ, Real.volume_Ico]

private theorem beta_le_inv (hM : E2sbMeasurable) (hL : E2PlanarLine)
    {p : ℝ} (hp : 0 < p) (z : Plane) {r : ℝ} (hr : 0 < r) :
    euclideanBetaPow e2_sbSource 1 p z r ≤ (ENNReal.ofReal r)⁻¹ := by
  obtain ⟨L, hL⟩ := hL.2 1 0 (z 0) (by norm_num)
  have hdist (w : Plane) (hw : w ∈ Metric.ball z r) :
      Metric.infEDist w L.toSet ≤ ENNReal.ofReal r := by
    rw [hL]
    simp only [one_mul, zero_mul, add_zero]
    apply ENNReal.ofReal_le_ofReal
    calc
      |w 0 - z 0| = ‖(w - z) 0‖ := by simp
      _ ≤ ‖w - z‖ := PiLp.norm_apply_le _ _
      _ ≤ r := le_of_lt (by simpa [dist_eq_norm] using hw)
  have hmass : e2_sbSource (Metric.ball z r) ≤ 1 := by
    rw [← source_mass hM]
    exact measure_mono (subset_univ _)
  have hfit : (∫⁻ w in Metric.ball z r, Metric.infEDist w L.toSet ^ p ∂e2_sbSource)
      ≤ ENNReal.ofReal r ^ p := by
    calc
      _ ≤ ∫⁻ _w in Metric.ball z r, ENNReal.ofReal r ^ p ∂e2_sbSource :=
        setLIntegral_mono' measurableSet_ball (fun w hw => ENNReal.rpow_le_rpow (hdist w hw) hp.le)
      _ = ENNReal.ofReal r ^ p * e2_sbSource (Metric.ball z r) := by simp
      _ ≤ ENNReal.ofReal r ^ p * 1 := mul_le_mul_right hmass _
      _ = _ := mul_one _
  have hR0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hRt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold euclideanBetaPow
  rw [ite_eq_left hr]
  simp only [Nat.cast_one]
  calc
    _ ≤ (ENNReal.ofReal r)⁻¹ ^ (1 + p) * ENNReal.ofReal r ^ p := by
      apply mul_le_mul_right
      exact (iInf_le _ L).trans hfit
    _ = (ENNReal.ofReal r)⁻¹ := by
      rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg,
        ← ENNReal.rpow_add _ _ hR0 hRt]
      convert ENNReal.rpow_neg_one (ENNReal.ofReal r) using 1; congr 1; ring

/-- The small-scale bound extends to every positive finite cutoff. -/
theorem e2_sb_spAll_proof (hM : E2sbMeasurable) (hL : E2PlanarLine)
    (hS : E2sbSpSmall) : E2sbSpAll := by
  intro p hp hp2 a ha
  obtain ⟨B, hB⟩ := hS p hp hp2
  by_cases hsmall : a ≤ 1 / 4
  · refine ⟨B, fun z hz => ?_⟩
    exact (lintegral_mono_set (Ioo_subset_Ioo_right hsmall)).trans (hB z hz)
  · let C : ℝ≥0∞ := (4 : ℝ≥0∞) ^ (2 / p)
    let D : ℝ≥0∞ := ENNReal.ofReal B + C * scaleMeasure (Icc (1 / 4) a)
    have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)
    have hD : D ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top hC (scaleMeasure_Icc_lt_top (by norm_num)).ne⟩
    refine ⟨D.toReal, fun z hz => ?_⟩
    rw [ENNReal.ofReal_toReal hD]
    have htail : (∫⁻ r in Ico (1 / 4) a,
        euclideanBetaPow e2_sbSource 1 p z r ^ (2 / p) ∂scaleMeasure)
        ≤ C * scaleMeasure (Icc (1 / 4) a) := by
      calc
        _ ≤ ∫⁻ _r in Ico (1 / 4) a, C ∂scaleMeasure := by
          apply setLIntegral_mono' measurableSet_Ico
          intro r hr
          apply ENNReal.rpow_le_rpow _ (by positivity)
          have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hr.1
          apply (beta_le_inv hM hL hp z hrpos).trans
          calc
            (ENNReal.ofReal r)⁻¹ ≤ (ENNReal.ofReal (1 / 4))⁻¹ :=
              ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hr.1)
            _ = 4 := by
              rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
              norm_num
        _ = C * scaleMeasure (Ico (1 / 4) a) := by simp
        _ ≤ C * scaleMeasure (Icc (1 / 4) a) :=
          mul_le_mul_right (measure_mono Ico_subset_Icc_self) C
    have hcover : Ioo (0 : ℝ) a ⊆ Ioo 0 (1 / 4) ∪ Ico (1 / 4) a := by
      intro r hr
      by_cases h : r < 1 / 4
      · exact Or.inl ⟨hr.1, h⟩
      · exact Or.inr ⟨le_of_not_gt h, hr.2⟩
    calc
      _ ≤ ∫⁻ r in Ioo 0 (1 / 4) ∪ Ico (1 / 4) a,
          euclideanBetaPow e2_sbSource 1 p z r ^ (2 / p) ∂scaleMeasure :=
        lintegral_mono_set hcover
      _ ≤ euclideanEnergyS e2_sbSource 1 p (1 / 4) z +
          ∫⁻ r in Ico (1 / 4) a, euclideanBetaPow e2_sbSource 1 p z r ^ (2 / p) ∂scaleMeasure :=
        lintegral_union_le _ _ _
      _ ≤ D := add_le_add (hB z hz) htail

end ParabolicRectifiability.Examples
