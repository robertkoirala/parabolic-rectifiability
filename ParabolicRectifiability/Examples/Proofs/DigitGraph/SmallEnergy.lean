import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import ParabolicRectifiability.Measure.ScaleIntegrals
import Mathlib.Analysis.PSeries

/-! # Uniform subquadratic energy of the dispersed digit graph

The half-open height bands cover all positive scales below `1/4`. On each band,
the inverse-square tail integral bounds the energy by eight times the band
coefficient. The marked proportions form a convergent real p-series, while the
future-height ratios have a geometric majorant. No measurability assertion
about the beta integrand is needed for the upper integral estimates.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations

/-- The height bands cover the entire small-scale interval, including their lower endpoints. -/
theorem e2_sb_heightBands (hG : E2sbGrid) (hT : E2sbTails) :
    Ioo (0 : ℝ) (1 / 4) = ⋃ n : ℕ, Ico (e2_sbH (n + 1) / 4) (e2_sbH n / 4) := by
  ext r
  constructor
  · intro hr
    have hex : ∃ j : ℕ, e2_sbH j / 4 ≤ r := by
      obtain ⟨j, hj⟩ := (hT.2.2.2.2.2.2.2.2.eventually (gt_mem_nhds (by linarith [hr.1] : (0 : ℝ) < 4 * r))).exists
      exact ⟨j, by linarith⟩
    let j := Nat.find hex
    have hj : e2_sbH j / 4 ≤ r := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro he
      simp only [he, e2_sbH] at hj
      exact (not_le_of_gt hr.2) hj
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · simpa [hn] using hj
    · have hh := Nat.find_min hex (show n < j by omega)
      exact lt_of_not_ge hh
  · intro hr
    obtain ⟨n, hn⟩ := mem_iUnion.mp hr
    have hpos := hG.2.1 (n + 1)
    have hle : e2_sbH n ≤ 1 := by
      simpa only [e2_sbH] using hT.2.2.2.2.2.2.2.1.antitone (Nat.zero_le n)
    exact ⟨by linarith [hn.1], by linarith [hn.2]⟩

/-- Distinct half-open height bands are disjoint. -/
theorem e2_sb_heightBands_disjoint (hT : E2sbTails) :
    Pairwise (fun i j : ℕ => Disjoint (Ico (e2_sbH (i + 1) / 4) (e2_sbH i / 4))
      (Ico (e2_sbH (j + 1) / 4) (e2_sbH j / 4))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro r hi hj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hh := hT.2.2.2.2.2.2.2.1.antitone (show i + 1 ≤ j by omega)
    linarith [hi.1, hj.2]
  · have hh := hT.2.2.2.2.2.2.2.1.antitone (show j + 1 ≤ i by omega)
    linarith [hj.1, hi.2]

/-- The exact inverse-square tail integral also bounds a half-open interval. -/
private theorem e2_sb_invSquare_band_le {a b : ℝ} (ha : 0 < a) :
    (∫⁻ r in Ico a b, (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure) ≤
      ENNReal.ofReal ((a ^ 2)⁻¹ / 2) := by
  calc
    _ ≤ ∫⁻ r in Ici a, (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure :=
      lintegral_mono_set Ico_subset_Ici_self
    _ = ∫⁻ r in Ioi a, (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure := by
      rw [restrict_Ioi_eq_restrict_Ici]
    _ = _ := lintegral_inv_pow_Ioi_scaleMeasure 2 (by norm_num) ha

/-- The normalized future tails have a summable geometric majorant. -/
theorem e2_sb_tailRatio_sq_le (hG : E2sbGrid) (hT : E2sbTails)
    (j : ℕ) (hj : 1 ≤ j) :
    (e2_sbTail j / e2_sbH j) ^ 2 ≤ (1 / 2 : ℝ) ^ j := by
  have hh := hG.2.1 j
  have hd := hG.2.2.2.2.2.2.2.2 j hj
  have ht := hT.2.2.2.2.2.1 j hj
  have ht0 := hT.2.2.1 j
  have hratio : e2_sbTail j / e2_sbH j ≤ (1 / 2 : ℝ) ^ j := by
    calc
      _ ≤ e2_sbDelta j / 2 ^ (j + 30) := by
        apply (div_le_iff₀ hh).mpr
        convert ht using 1; ring
      _ ≤ 1 / 2 ^ (j + 30) := by gcongr; linarith [hd.2]
      _ ≤ 1 / 2 ^ j := by
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (1 / 2 : ℝ) ^ j := by rw [div_pow, one_pow]
  have hratio0 : 0 ≤ e2_sbTail j / e2_sbH j := div_nonneg ht0 hh.le
  have hgeo : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ ≤ e2_sbTail j / e2_sbH j := by
      nlinarith [hratio.trans hgeo]
    _ ≤ _ := hratio

/-- The sequence of marked proportions is a real p-series after an index shift. -/
theorem e2_sb_delta_rpow_summable {q : ℝ} (hq : 1 < q) :
    Summable (fun n : ℕ => e2_sbDelta (n + 1) ^ q) := by
  have hs := (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_rpow.mpr hq)
  convert hs using 1
  ext n
  simp only [e2_sbDelta, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]
  congr 2
  ring

/-- Integrate one band without assuming that the beta integrand is measurable. -/
theorem e2_sb_energy_band_le (hG : E2sbGrid) (hT : E2sbTails)
    {p C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ z ∈ e2_sbSet, ∀ j : ℕ, 1 ≤ j → ∀ r : ℝ,
      e2_sbH j / 4 ≤ r → r < e2_sbH (j - 1) / 4 →
        euclideanBetaPow e2_sbSource 1 p z r ^ (2 / p) ≤
          ENNReal.ofReal (C * (e2_sbDelta j ^ (2 / p) * (e2_sbH j / r) ^ 2 +
            (e2_sbTail j / r) ^ 2)))
    {z : BetaP.Plane} (hz : z ∈ e2_sbSet) (n : ℕ) :
    (∫⁻ r in Ico (e2_sbH (n + 1) / 4) (e2_sbH n / 4),
      euclideanBetaPow e2_sbSource 1 p z r ^ (2 / p) ∂scaleMeasure) ≤
        ENNReal.ofReal (8 * C * (e2_sbDelta (n + 1) ^ (2 / p) + (1 / 2 : ℝ) ^ (n + 1))) := by
  let h := e2_sbH (n + 1)
  let t := e2_sbTail (n + 1)
  let d := e2_sbDelta (n + 1) ^ (2 / p)
  let K := C * (d * h ^ 2 + t ^ 2)
  have hh : 0 < h := hG.2.1 _
  have hd : 0 ≤ d := Real.rpow_nonneg (le_of_lt (hG.2.2.2.2.2.2.2.2 _ (by omega)).1) _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ ∫⁻ r in Ico (h / 4) (e2_sbH n / 4),
        ENNReal.ofReal K * (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure := by
      apply setLIntegral_mono' measurableSet_Ico
      intro r hr
      have hr0 : 0 < r := (div_pos hh (by norm_num)).trans_le hr.1
      have hb := hB z hz (n + 1) (by omega) r hr.1 (by simpa using hr.2)
      refine hb.trans_eq ?_
      rw [← ENNReal.ofReal_inv_of_pos hr0,
        ← ENNReal.ofReal_pow (inv_nonneg.mpr hr0.le), ← ENNReal.ofReal_mul hK]
      congr 1
      dsimp [K, h, t, d]
      ring
    _ = ENNReal.ofReal K * ∫⁻ r in Ico (h / 4) (e2_sbH n / 4),
        (ENNReal.ofReal r)⁻¹ ^ 2 ∂scaleMeasure :=
      lintegral_const_mul _ (measurable_inv_pow_ofReal 2)
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (((h / 4) ^ 2)⁻¹ / 2) :=
      mul_le_mul_right (e2_sb_invSquare_band_le (div_pos hh (by norm_num))) _
    _ = ENNReal.ofReal (8 * C * (d + (t / h) ^ 2)) := by
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      dsimp [K]
      field_simp
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact e2_sb_tailRatio_sq_le hG hT (n + 1) (by omega)

/-- Summing the height bands gives a finite bound uniform over every center in `E`. -/
theorem e2_sb_spSmall_proof (hG : E2sbGrid) (hT : E2sbTails) (hB : E2sbBand) :
    E2sbSpSmall := by
  intro p hp hp2
  obtain ⟨C, hC, hband⟩ := hB p hp
  have hq : 1 < 2 / p := (lt_div_iff₀ hp).mpr (by linarith)
  let a : ℕ → ℝ := fun n => 8 * C *
    (e2_sbDelta (n + 1) ^ (2 / p) + (1 / 2 : ℝ) ^ (n + 1))
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    dsimp [a]
    have hd := (hG.2.2.2.2.2.2.2.2 (n + 1) (by omega)).1
    positivity
  have hs : Summable a := by
    apply Summable.mul_left
    apply (e2_sb_delta_rpow_summable hq).add
    exact (summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  refine ⟨∑' n, a n, fun z hz => ?_⟩
  unfold euclideanEnergyS
  rw [e2_sb_heightBands hG hT, ENNReal.ofReal_tsum_of_nonneg ha0 hs]
  refine (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum fun n => ?_)
  exact e2_sb_energy_band_le hG hT hC hband hz n

end ParabolicRectifiability.Examples
