import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # Cylinder covers of the dispersed digit graph

The closures of the finitely many generation-`j` cylinder images cover the
closure defining `e2_sbSet`. Their diameters are at most `ℓ_j + η_j` in the
Euclidean metric. The resulting total cost is at most `1 + 2⁻ʲ⁻²⁰`.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.BetaP (Plane)

private def cylinder (j k : ℕ) : Set Plane :=
  closure (e2_sbGraph '' Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j))

private lemma oldHeight_eq (hD : E2sbDigit) (j k : ℕ) {x y : ℝ}
    (hx : x ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j))
    (hy : y ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j)) :
    e2_sbOldHeight j x = e2_sbOldHeight j y := by
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact hD.1 j (i + 1) (by omega) (by simpa using Finset.mem_range.mp hi)
    (k : ℤ) x y (by simpa using hx) (by simpa using hy)

private lemma cylinder_ediam (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit)
    (j k : ℕ) : Metric.ediam (cylinder j k) ≤ ENNReal.ofReal (e2_sbEll j + e2_sbTail j) := by
  rw [cylinder, Metric.ediam_closure]
  apply Metric.ediam_le_of_forall_dist_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hold := oldHeight_eq hD j k hx hy
  have htx := hD.2.1 j x
  have hty := hD.2.1 j y
  have hdx : |x - y| ≤ e2_sbEll j := abs_le.mpr ⟨by linarith [hx.1, hx.2, hy.1, hy.2], by linarith [hx.1, hx.2, hy.1, hy.2]⟩
  have hdy : |e2_sbHeight x - e2_sbHeight y| ≤ e2_sbTail j :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := EuclideanSpace.dist_sq_eq (e2_sbGraph x) (e2_sbGraph y)
  simp only [Fin.sum_univ_two, e2_sbGraph, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.dist_eq, sq_abs] at hs
  change dist (e2_sbGraph x) (e2_sbGraph y) ^ 2 =
    (x - y) ^ 2 + (e2_sbHeight x - e2_sbHeight y) ^ 2 at hs
  have hx2 := sq_le_sq₀ (abs_nonneg (x - y)) (hG.1 j).le |>.mpr hdx
  have hy2 := sq_le_sq₀ (abs_nonneg (e2_sbHeight x - e2_sbHeight y)) (hT.2.2.1 j) |>.mpr hdy
  rw [sq_abs] at hx2 hy2
  have hn := dist_nonneg (x := e2_sbGraph x) (y := e2_sbGraph y)
  apply (sq_le_sq₀ hn (add_nonneg (hG.1 j).le (hT.2.2.1 j))).mp
  nlinarith [mul_nonneg (hG.1 j).le (hT.2.2.1 j)]

private lemma cylinder_cover (hG : E2sbGrid) (j n : ℕ)
    (hn : (n : ℝ) * e2_sbEll j = 1) :
    e2_sbSet ⊆ ⋃ k : Fin n, cylinder j k := by
  unfold e2_sbSet
  rw [show (⋃ k : Fin n, cylinder j k) = closure
    (⋃ k : Fin n, e2_sbGraph '' Ico ((k : ℝ) * e2_sbEll j)
      (((k : ℝ) + 1) * e2_sbEll j)) from (closure_iUnion_of_finite _).symm]
  apply closure_mono
  rintro _ ⟨x, hx, rfl⟩
  have hnonneg : 0 ≤ x / e2_sbEll j := div_nonneg hx.1 (hG.1 j).le
  have hlt : ⌊x / e2_sbEll j⌋₊ < n := (Nat.floor_lt hnonneg).mpr
    ((div_lt_iff₀ (hG.1 j)).mpr (by simpa [hn] using hx.2))
  refine mem_iUnion.mpr ⟨⟨⌊x / e2_sbEll j⌋₊, hlt⟩, ⟨x, ?_, rfl⟩⟩
  exact ⟨(le_div_iff₀ (hG.1 j)).mp (Nat.floor_le hnonneg),
    (div_lt_iff₀ (hG.1 j)).mp (Nat.lt_floor_add_one _)⟩

private lemma compact_set (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) :
    IsCompact e2_sbSet := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_closure, Metric.isBounded_iff_ediam_ne_top.mpr ?_⟩
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  simpa [cylinder, e2_sbEll, e2_sbSet] using cylinder_ediam hG hT hD 0 0

private lemma ell_le_height (hG : E2sbGrid) {j : ℕ} (hj : 1 ≤ j) :
    e2_sbEll j ≤ e2_sbH j := by
  have hperiod : e2_sbEll j ≤ e2_sbPeriod j := by
    unfold e2_sbPeriod
    nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (hG.1 j).le]
  have heq := hG.2.2.2.2.2.2.1 j hj
  nlinarith [hG.1 j]

private lemma diameter_tendsto (hG : E2sbGrid) (hT : E2sbTails) :
    Tendsto (fun j => ENNReal.ofReal (e2_sbEll j + e2_sbTail j)) atTop (𝓝 0) := by
  have hH := hT.2.2.2.2.2.2.2.2
  have hell : Tendsto e2_sbEll atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun j => (hG.1 j).le)
      (eventually_atTop.mpr ⟨1, fun j hj => ell_le_height hG hj⟩) hH
  have htail : Tendsto e2_sbTail atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall hT.2.2.1)
      (eventually_atTop.mpr ⟨1, fun j hj => hT.2.2.2.1 j hj⟩)
    simpa using (hH.comp (tendsto_add_atTop_nat 1)).const_mul 2
  have hsum : Tendsto (fun j => e2_sbEll j + e2_sbTail j) atTop (𝓝 0) := by
    simpa using hell.add htail
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hsum

private lemma cover_cost (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit)
    (j n : ℕ) (hj : 1 ≤ j) (hn : (n : ℝ) * e2_sbEll j = 1) :
    (∑ k : Fin n, Metric.ediam (cylinder j k) ^ (1 : ℝ)) ≤
      ENNReal.ofReal (1 + 1 / (2 : ℝ) ^ (j + 20)) := by
  simp only [ENNReal.rpow_one]
  calc
    (∑ k : Fin n, Metric.ediam (cylinder j k)) ≤
        ∑ _k : Fin n, ENNReal.ofReal (e2_sbEll j + e2_sbTail j) :=
      Finset.sum_le_sum fun k _ => cylinder_ediam hG hT hD j k
    _ = ENNReal.ofReal ((n : ℝ) * (e2_sbEll j + e2_sbTail j)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 + 1 / (2 : ℝ) ^ (j + 20)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (n : ℝ) * (e2_sbEll j + e2_sbTail j) = 1 + n * e2_sbTail j := by
          rw [mul_add, hn]
        _ ≤ 1 + n * (e2_sbEll j / (2 : ℝ) ^ (j + 20)) := by
          gcongr
          exact hT.2.2.2.2.1 j hj
        _ = 1 + 1 / (2 : ℝ) ^ (j + 20) := by rw [← mul_div_assoc, hn]

/-- The finite cylinder covers have vanishing diameter and asymptotic total cost one. -/
theorem e2_sb_cover_proof (hG : E2sbGrid) (hT : E2sbTails) (hD : E2sbDigit) :
    E2sbCover := by
  classical
  refine ⟨compact_set hG hT hD, ?_⟩
  choose count hcount using hG.2.2.2.2.1
  let t : ∀ j : ℕ, Fin (count j) → Set Plane := fun j k => cylinder j k
  have hbound := Measure.hausdorffMeasure_le_liminf_sum 1 e2_sbSet
    (fun j => ENNReal.ofReal (e2_sbEll j + e2_sbTail j)) (diameter_tendsto hG hT) t
    (Eventually.of_forall fun j k => cylinder_ediam hG hT hD j k)
    (Eventually.of_forall fun j => cylinder_cover hG j (count j) (hcount j))
  calc
    μH[1] e2_sbSet ≤ liminf (fun j => ∑ k, Metric.ediam (t j k) ^ (1 : ℝ)) atTop := hbound
    _ ≤ liminf (fun j : ℕ => ENNReal.ofReal (1 + 1 / (2 : ℝ) ^ (j + 20))) atTop := by
      exact liminf_le_liminf
        (eventually_atTop.mpr ⟨1, fun j hj => cover_cost hG hT hD j (count j) hj (hcount j)⟩)
    _ = 1 := by
      apply Tendsto.liminf_eq
      have hgeom : Tendsto (fun j : ℕ => 1 / (2 : ℝ) ^ (j + 20)) atTop (𝓝 0) := by
        simpa only [one_div, inv_pow, Function.comp_def] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 2⁻¹ by norm_num)
            (by norm_num)).comp (tendsto_add_atTop_nat 20)
      have hsum : Tendsto (fun j : ℕ => 1 + 1 / (2 : ℝ) ^ (j + 20)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.add hgeom
      simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 1).comp hsum

end ParabolicRectifiability.Examples
