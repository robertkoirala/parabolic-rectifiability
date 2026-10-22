import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Convex.Function

/-! # The gauge series is an admissible gauge

Proof of `i2_GaugeSeriesAdmissibleStatement`, the auxiliary statement
`i2_gaugeSeries_admissible`.

For `t_j > 0` with `Σ_j t_j⁻¹ < ∞`, the terms `min{1, u/t_j}` satisfy `0 ≤ · ≤ u t_j⁻¹` for
`u ≥ 0`. Hence the series converges for `u ≥ 0` and uniformly on every `[0, M]`
(`continuousOn_tsum`), which gives continuity on `[0, ∞)`. Monotonicity and concavity hold
termwise (each term is the minimum of two affine maps) and pass to the sum. For
`u ≥ max_{j<N} t_j` the first `N` terms equal `1`, so the series is unbounded.
-/

noncomputable section

open Set Filter Topology

namespace ParabolicRectifiability.IntegralCanonical

variable {t : ℕ → ℝ}

/-- Each term is nonnegative for `u ≥ 0`. -/
theorem i2_gs_term_nonneg (ht : ∀ j, 0 < t j) {u : ℝ} (hu : 0 ≤ u) (j : ℕ) :
    0 ≤ min 1 (u / t j) :=
  le_min zero_le_one (div_nonneg hu (ht j).le)

/-- Each term is at most `u t_j⁻¹`. -/
theorem i2_gs_term_le (u : ℝ) (j : ℕ) : min 1 (u / t j) ≤ u * (t j)⁻¹ :=
  (min_le_right _ _).trans_eq (div_eq_mul_inv _ _)

/-- The gauge series converges at every `u ≥ 0`. -/
theorem i2_gs_summable (ht : ∀ j, 0 < t j) (hs : Summable fun j => (t j)⁻¹) {u : ℝ}
    (hu : 0 ≤ u) : Summable fun j => min 1 (u / t j) :=
  Summable.of_nonneg_of_le (i2_gs_term_nonneg ht hu) (i2_gs_term_le u) (hs.mul_left u)

/-- Continuity on `[0, M]`: uniform convergence with majorant `M t_j⁻¹`. -/
theorem i2_gs_continuousOn_Icc (ht : ∀ j, 0 < t j) (hs : Summable fun j => (t j)⁻¹)
    (M : ℝ) : ContinuousOn (i2_gaugeSeries t) (Icc 0 M) := by
  show ContinuousOn (fun u => ∑' j : ℕ, min 1 (u / t j)) (Icc 0 M)
  refine continuousOn_tsum (u := fun j => M * (t j)⁻¹) (fun j => ?_) (hs.mul_left M) ?_
  · exact (continuous_const.min (continuous_id.div_const (t j))).continuousOn
  · intro j u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (i2_gs_term_nonneg ht hu.1 j)]
    exact (i2_gs_term_le u j).trans (mul_le_mul_of_nonneg_right hu.2 (inv_nonneg.2 (ht j).le))

/-- Continuity on `[0, ∞)`, from continuity on `[0, x + 1]` near each `x ≥ 0`. -/
theorem i2_gs_continuousOn (ht : ∀ j, 0 < t j) (hs : Summable fun j => (t j)⁻¹) :
    ContinuousOn (i2_gaugeSeries t) (Ici 0) := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  have hx' : x ∈ Icc (0 : ℝ) (x + 1) := ⟨hx0, by linarith⟩
  refine ((i2_gs_continuousOn_Icc ht hs (x + 1)) x hx').mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- Monotonicity on `[0, ∞)`, termwise. -/
theorem i2_gs_monotoneOn (ht : ∀ j, 0 < t j) (hs : Summable fun j => (t j)⁻¹) :
    MonotoneOn (i2_gaugeSeries t) (Ici 0) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) ≤ a := ha
  have hb0 : (0 : ℝ) ≤ b := hb
  exact Summable.tsum_le_tsum
    (fun j => le_min (min_le_left _ _)
      ((min_le_right _ _).trans (div_le_div_of_nonneg_right hab (ht j).le)))
    (i2_gs_summable ht hs ha0) (i2_gs_summable ht hs hb0)

/-- The termwise concavity inequality: `min{1, ·/t_j}` is the minimum of two affine maps. -/
theorem i2_gs_term_concave (ht : ∀ j, 0 < t j) (j : ℕ) {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    a * min 1 (x / t j) + b * min 1 (y / t j) ≤ min 1 ((a * x + b * y) / t j) := by
  have htj : t j ≠ 0 := (ht j).ne'
  refine le_min ?_ ?_
  · calc a * min 1 (x / t j) + b * min 1 (y / t j) ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
            (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)
      _ = 1 := by rw [mul_one, mul_one, hab]
  · calc a * min 1 (x / t j) + b * min 1 (y / t j) ≤ a * (x / t j) + b * (y / t j) :=
          add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) ha)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
      _ = (a * x + b * y) / t j := by field_simp

/-- Concavity on `[0, ∞)`: the termwise inequality, summed (`tsum_mul_left`, `tsum_add`). -/
theorem i2_gs_concaveOn (ht : ∀ j, 0 < t j) (hs : Summable fun j => (t j)⁻¹) :
    ConcaveOn ℝ (Ici 0) (i2_gaugeSeries t) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hz : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
  have hsx := (i2_gs_summable ht hs hx0).mul_left a
  have hsy := (i2_gs_summable ht hs hy0).mul_left b
  simp only [smul_eq_mul, i2_gaugeSeries]
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add hsx hsy]
  exact Summable.tsum_le_tsum (fun j => i2_gs_term_concave ht j ha hb hab) (hsx.add hsy)
    (i2_gs_summable ht hs hz)

/-- Unboundedness: at `u = Σ_{j<N} t_j ≥ max_{j<N} t_j` the first `N` terms equal `1`. -/
theorem i2_gs_not_bddAbove (ht : ∀ j, 0 < t j) (hs : Summable fun j => (t j)⁻¹) :
    ¬ BddAbove (i2_gaugeSeries t '' Ici 0) := by
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := exists_nat_gt B
  obtain ⟨u, hu, htu⟩ : ∃ u : ℝ, 0 ≤ u ∧ ∀ j ∈ Finset.range N, t j ≤ u :=
    ⟨∑ j ∈ Finset.range N, t j, Finset.sum_nonneg fun j _ => (ht j).le,
      fun j hj => Finset.single_le_sum (fun i _ => (ht i).le) hj⟩
  have hle : i2_gaugeSeries t u ≤ B := hB (mem_image_of_mem _ (show u ∈ Ici 0 from hu))
  have hsum : ∑ j ∈ Finset.range N, min 1 (u / t j) ≤ i2_gaugeSeries t u :=
    (i2_gs_summable ht hs hu).sum_le_tsum (Finset.range N)
      (fun j _ => i2_gs_term_nonneg ht hu j)
  have hone : ∀ j ∈ Finset.range N, min 1 (u / t j) = 1 := by
    intro j hj
    apply min_eq_left
    rw [le_div_iff₀ (ht j), one_mul]
    exact htu j hj
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hsum
  linarith

/-- `Φ_t(0) = 0`. -/
theorem i2_gs_zero : i2_gaugeSeries t 0 = 0 := by
  have h : ∀ j, min (1 : ℝ) (0 / t j) = 0 := fun j => by
    rw [zero_div]
    exact min_eq_right zero_le_one
  simp only [i2_gaugeSeries, h, tsum_zero]

/-- **I1-G1.** For a positive sequence `t` with `Σ_j t_j⁻¹ < ∞`, the gauge series
`Φ_t(u) = Σ_j min{1, u/t_j}` is an admissible gauge. -/
theorem i2_gaugeSeries_admissible_proof : i2_GaugeSeriesAdmissibleStatement := by
  intro t ht hs
  exact ⟨i2_gs_continuousOn ht hs, i2_gs_monotoneOn ht hs, i2_gs_concaveOn ht hs,
    i2_gs_not_bddAbove ht hs, i2_gs_zero, fun u hu => tsum_nonneg (i2_gs_term_nonneg ht hu)⟩

end ParabolicRectifiability.IntegralCanonical
