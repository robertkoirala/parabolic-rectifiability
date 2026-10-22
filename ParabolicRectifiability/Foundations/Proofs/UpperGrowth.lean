import ParabolicRectifiability.Metric.Hausdorff
import Mathlib.MeasureTheory.Measure.Support

/-! # Upper growth implies absolute continuity: proofs

Proves, with the types of `fgac_absolutelyContinuous_hausdorffP_of_growth` and
`fgac_ball_le_of_support_growth`:
* `fgac_absolutelyContinuous_hausdorffP_of_growth_proof` (the type of
  `absolutelyContinuous_hausdorffP_of_growth`),
* `fgac_ball_le_of_support_growth_proof`.
Every helper is prefixed `bf1gac_`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.Foundations

/-- A set of finite extended diameter lies in the ball about each of its points of every radius
exceeding the diameter. -/
theorem bf1gac_subset_ball_of_ediam {n : ℕ} {s : Set (Space n)} {x : Space n} (hx : x ∈ s)
    (hs : Metric.ediam s ≠ ⊤) {r : ℝ} (hr : (Metric.ediam s).toReal < r) :
    s ⊆ Metric.ball x r := by
  intro y hy
  rw [Metric.mem_ball]
  have h1 : edist y x ≤ Metric.ediam s := Metric.edist_le_ediam_of_mem hy hx
  have h2 : dist y x ≤ (Metric.ediam s).toReal := by
    rw [dist_edist]
    exact ENNReal.toReal_mono hs h1
  linarith

/-- The diameter estimate for an arbitrary set of small extended diameter. -/
theorem bf1gac_measure_le_of_ediam {n : ℕ} (lam : Measure (Space n)) (k : ℕ) (hk : 1 ≤ k)
    (B r₀ : ℝ) (hr₀ : 0 < r₀)
    (hgrowth : ∀ (p : Space n) (r : ℝ), 0 < r → r ≤ r₀ →
      lam (Metric.ball p r) ≤ ENNReal.ofReal (B * r ^ k))
    (s : Set (Space n)) (hs : Metric.ediam s ≤ ENNReal.ofReal (r₀ / 2)) :
    lam s ≤ ENNReal.ofReal (max B 1) * (Metric.ediam s) ^ (k : ℝ) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have hfin : Metric.ediam s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  set d : ℝ := (Metric.ediam s).toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hdle : d ≤ r₀ / 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have hdlt : d < r₀ := by linarith
  have hed : Metric.ediam s = ENNReal.ofReal d := (ENNReal.ofReal_toReal hfin).symm
  -- bound for every radius in `(d, r₀]`
  have hbound : ∀ r : ℝ, d < r → r ≤ r₀ → lam s ≤ ENNReal.ofReal (B * r ^ k) := by
    intro r hdr hrr
    exact (measure_mono (bf1gac_subset_ball_of_ediam hx hfin hdr)).trans
      (hgrowth x r (by linarith) hrr)
  -- let `r ↓ d`
  have hcont : Tendsto (fun r : ℝ => ENNReal.ofReal (B * r ^ k)) (𝓝[>] d)
      (𝓝 (ENNReal.ofReal (B * d ^ k))) := by
    have : Continuous (fun r : ℝ => ENNReal.ofReal (B * r ^ k)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    exact (this.tendsto d).mono_left nhdsWithin_le_nhds
  have hlim : lam s ≤ ENNReal.ofReal (B * d ^ k) := by
    refine ge_of_tendsto hcont ?_
    filter_upwards [Ioc_mem_nhdsGT hdlt] with r hr
    exact hbound r hr.1 hr.2
  refine hlim.trans ?_
  rw [hed, ENNReal.ofReal_rpow_of_nonneg hd0 (by positivity), Real.rpow_natCast]
  rw [← ENNReal.ofReal_mul (le_max_of_le_right zero_le_one)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hd0 k)

/-- **G1.** Upper growth implies absolute continuity with respect to `H_P^k`. -/
theorem fgac_absolutelyContinuous_hausdorffP_of_growth_proof :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ lam : Measure (Space n), IsFiniteMeasureOnCompacts lam → lam.InnerRegular →
    ∀ B r₀ : ℝ, 0 < r₀ →
      (∀ (p : Space n) (r : ℝ), 0 < r → r ≤ r₀ →
        lam (Metric.ball p r) ≤ ENNReal.ofReal (B * r ^ k)) →
      lam ≪ hausdorffP n k := by
  intro n _ k hk _ lam _ _ B r₀ hr₀ hgrowth
  set c : ℝ≥0∞ := ENNReal.ofReal (max B 1) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (ENNReal.ofReal_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : lam ≤ Measure.mkMetric (fun d : ℝ≥0∞ => c * d ^ (k : ℝ)) := by
    refine Measure.le_mkMetric _ lam (ENNReal.ofReal (r₀ / 2)) ?_ ?_
    · exact ENNReal.ofReal_pos.2 (by linarith)
    · intro s hs
      exact bf1gac_measure_le_of_ediam lam k hk B r₀ hr₀ hgrowth s hs
  have h2 : (Measure.mkMetric (fun d : ℝ≥0∞ => c * d ^ (k : ℝ)) : Measure (Space n)) ≤
      c • (Measure.hausdorffMeasure (k : ℝ) : Measure (Space n)) := by
    refine Measure.mkMetric_mono_smul hctop hc0 ?_
    exact Eventually.of_forall fun d => le_rfl
  exact Measure.absolutelyContinuous_of_le_smul (h1.trans h2)

/-- **G2.** Support-centred growth gives all-centre growth. -/
theorem fgac_ball_le_of_support_growth_proof {n : ℕ} (k : ℕ) (μ : Measure (Space n)) (A : ℝ)
    (hA : ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r → μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k))
    (p : Space n) (r : ℝ) (hr : 0 < r) :
    μ (Metric.ball p r) ≤ ENNReal.ofReal (2 ^ k * A * r ^ k) := by
  by_cases h0 : μ (Metric.ball p r) = 0
  · rw [h0]; exact zero_le
  have hpos : 0 < μ (Metric.ball p r) := pos_iff_ne_zero.2 h0
  obtain ⟨z, hzb, hzs⟩ := Measure.nonempty_inter_support_of_pos hpos
  have hsub : Metric.ball p r ⊆ Metric.ball z (2 * r) := by
    intro y hy
    rw [Metric.mem_ball] at hy hzb ⊢
    have := dist_triangle y p z
    rw [dist_comm p z] at this
    linarith
  refine (measure_mono hsub).trans ((hA z hzs (2 * r) (by linarith)).trans ?_)
  refine le_of_eq ?_
  congr 1
  rw [mul_pow]
  ring

end ParabolicRectifiability.Foundations
