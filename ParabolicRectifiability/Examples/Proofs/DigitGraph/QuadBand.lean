import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Quadratic band lower bound for the dispersed digit graph

The quadratic band estimate `β_{2,μ}(T(x₀), r)^2 ≥ δ_j/1024` for `3h_j ≤ r ≤ 4h_j`
(`e2_sb_quadBand_proof`). The open parameter
interval stays in its parent cell and maps strictly inside the radius-three ball.
The source integral then dominates the line-cost integral for every affine line. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane)

private theorem parent_interval_domain (hG : E2sbGrid) {j : ℕ} {k : ℤ} {x₀ : ℝ}
    (hx₀ : x₀ ∈ Ico (0 : ℝ) 1)
    (hl : (k : ℝ) * e2_sbEll (j - 1) ≤ x₀ - e2_sbH j)
    (hu : x₀ + e2_sbH j ≤ ((k : ℝ) + 1) * e2_sbEll (j - 1)) :
    Ioo (x₀ - e2_sbH j) (x₀ + e2_sbH j) ⊆ Ico 0 1 := by
  have he := hG.1 (j - 1)
  have hh := hG.2.1 j
  obtain ⟨c, hc⟩ := hG.2.2.2.2.1 (j - 1)
  have hk : 0 ≤ k := by
    by_contra hn
    have hk' : k ≤ -1 := by omega
    have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
    nlinarith [hx₀.1]
  have hkc : k < (c : ℤ) := by
    have hkR : (k : ℝ) < (c : ℝ) := by nlinarith [hx₀.2]
    exact_mod_cast hkR
  have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hkcR : (k : ℝ) + 1 ≤ c := by exact_mod_cast (show k + 1 ≤ (c : ℤ) by omega)
  intro x hx
  constructor
  · nlinarith [mul_nonneg hkR he.le, hx.1]
  · have htop : ((k : ℝ) + 1) * e2_sbEll (j - 1) ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hkcR he.le]
    linarith [hx.2]

private theorem graph_interval_ball (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit)
    {j : ℕ} (hj : 1 ≤ j) {k : ℤ} {x₀ : ℝ}
    (hl : (k : ℝ) * e2_sbEll (j - 1) ≤ x₀ - e2_sbH j)
    (hu : x₀ + e2_sbH j ≤ ((k : ℝ) + 1) * e2_sbEll (j - 1))
    {x : ℝ} (hx : x ∈ Ioo (x₀ - e2_sbH j) (x₀ + e2_sbH j)) :
    e2_sbGraph x ∈ Metric.ball (e2_sbGraph x₀) (3 * e2_sbH j) := by
  have hh := hG.2.1 j
  have hparentx : x ∈ Ico ((k : ℝ) * e2_sbEll (j - 1))
      (((k : ℝ) + 1) * e2_sbEll (j - 1)) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hparent₀ : x₀ ∈ Ico ((k : ℝ) * e2_sbEll (j - 1))
      (((k : ℝ) + 1) * e2_sbEll (j - 1)) := ⟨by linarith, by linarith⟩
  have hold : e2_sbOldHeight (j - 1) x = e2_sbOldHeight (j - 1) x₀ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hD.1 (j - 1) (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)
      k x x₀ hparentx hparent₀]
  have hstep (z : ℝ) : e2_sbOldHeight j z =
      e2_sbOldHeight (j - 1) z + e2_sbH j * e2_sbBit j z := by
    have heq : j = (j - 1) + 1 := by omega
    conv_lhs => rw [heq]
    simp only [e2_sbOldHeight, Finset.sum_range_succ]
    rw [← heq]
  have hb (z : ℝ) : 0 ≤ e2_sbBit j z ∧ e2_sbBit j z ≤ 1 := by
    unfold e2_sbBit
    by_cases hz : z ∈ e2_sbMarked j <;> simp [hz]
  have hd₀ := hD.2.1 j x₀
  have hdx := hD.2.1 j x
  simp only [hstep, hold] at hdx hd₀
  have hbitx := mul_le_mul_of_nonneg_left (hb x).2 hh.le
  have hbit₀ := mul_le_mul_of_nonneg_left (hb x₀).2 hh.le
  have hbitx0 := mul_nonneg hh.le (hb x).1
  have hbit₀0 := mul_nonneg hh.le (hb x₀).1
  have hdy : |e2_sbHeight x - e2_sbHeight x₀| ≤ e2_sbH j + e2_sbTail j := by
    rw [abs_le]
    constructor <;> linarith
  have hδ := hG.2.2.2.2.2.2.2.2 j hj
  have htail := hT.2.2.2.2.2.2.1 j hj
  have htail0 := hT.2.2.1 j
  have htailh : e2_sbTail j < e2_sbH j := by
    have hm := mul_le_mul_of_nonneg_right hδ.2 (sq_nonneg (e2_sbH j))
    nlinarith [sq_nonneg (e2_sbTail j - e2_sbH j)]
  have hdx : |x - x₀| < e2_sbH j := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have hx2 : (x - x₀) ^ 2 < (e2_sbH j) ^ 2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (x - x₀)) hh.le).2 hdx
  have hy2 : (e2_sbHeight x - e2_sbHeight x₀) ^ 2 < (2 * e2_sbH j) ^ 2 := by
    have habs : |e2_sbHeight x - e2_sbHeight x₀| < 2 * e2_sbH j := by linarith
    nlinarith [sq_abs (e2_sbHeight x - e2_sbHeight x₀), abs_nonneg (e2_sbHeight x - e2_sbHeight x₀)]
  have hnorm : ‖e2_sbGraph x - e2_sbGraph x₀‖ ^ 2 =
      (x - x₀) ^ 2 + (e2_sbHeight x - e2_sbHeight x₀) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two, e2_sbGraph]
  rw [Metric.mem_ball, dist_eq_norm]
  nlinarith [norm_nonneg (e2_sbGraph x - e2_sbGraph x₀)]

private theorem quad_band_normalization {δ h r : ℝ} (hδ : 0 ≤ δ) (hh : 0 < h)
    (hr : 0 < r) (hru : r ≤ 4 * h) :
    ENNReal.ofReal (δ / 1024) ≤ (ENNReal.ofReal r)⁻¹ ^ (3 : ℝ) *
      ENNReal.ofReal (δ * h ^ 3 / 16) := by
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_pow (inv_nonneg.mpr hr.le),
    ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hr.le) 3)]
  apply ENNReal.ofReal_le_ofReal
  have hcube : r ^ 3 ≤ (4 * h) ^ 3 := pow_le_pow_left₀ hr.le hru 3
  have hmul := mul_le_mul_of_nonneg_left hcube hδ
  have hr3 : 0 < r ^ 3 := pow_pos hr 3
  have hreal : δ / 1024 ≤ (δ * h ^ 3 / 16) / r ^ 3 :=
    (le_div_iff₀ hr3).2 (by nlinarith)
  convert hreal using 1
  field_simp

/-- On each band `[3 h_j, 4 h_j]`, every line pays at least the same normalized
line cost, hence the infimum is at least `δ_j / 1024`. -/
theorem e2_sb_quadBand_proof (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit)
    (hM : E2sbMeasurable) (hLC : E2sbLineCost) : E2sbQuadBand := by
  intro j hj k x₀ hx₀ hl hu r hrl hru
  have hh := hG.2.1 j
  have hr : 0 < r := by linarith
  have hdom := parent_interval_domain hG hx₀ hl hu
  have hball : Ioo (x₀ - e2_sbH j) (x₀ + e2_sbH j) ⊆
      e2_sbGraph ⁻¹' Metric.ball (e2_sbGraph x₀) r := by
    intro x hx
    exact (Metric.ball_subset_ball hrl) (graph_interval_ball hG hT hD hj hl hu hx)
  have hcost (L : AffineSpatialPlane 2 1) :
      ENNReal.ofReal (e2_sbDelta j * e2_sbH j ^ 3 / 16) ≤
        ∫⁻ w in Metric.ball (e2_sbGraph x₀) r, Metric.infEDist w L.toSet ^ (2 : ℝ)
          ∂e2_sbSource := by
    rw [e2_sbSource, setLIntegral_map measurableSet_ball
      (measurable_infEDist.pow_const (2 : ℝ)) hM.2.2,
      Measure.restrict_restrict (hM.2.2 measurableSet_ball)]
    exact (hLC j hj k x₀ hl hu L).trans (lintegral_mono_set (fun x hx => ⟨hball hx, hdom hx⟩))
  rw [euclideanBetaPow, ite_eq_left hr]
  norm_num only [Nat.cast_one, show (1 : ℝ) + 2 = 3 by norm_num]
  exact (quad_band_normalization (hG.2.2.2.2.2.2.2.2 j hj).1.le hh hr hru).trans
    (mul_le_mul' le_rfl (le_iInf hcost))
end ParabolicRectifiability.Examples
