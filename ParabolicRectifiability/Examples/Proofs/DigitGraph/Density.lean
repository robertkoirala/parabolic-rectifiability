import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # Ball growth and upper density of the dispersed digit graph

The coordinate projection gives the global growth estimate. For the lower density,
we approximate each point of the genuine closure by a graph point, then place its
whole half-open grid cell inside a slightly larger ball. The strict buffer avoids
any choice of endpoint coding for a point in the closure.
-/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace ParabolicRectifiability.Examples
open ParabolicRectifiability.BetaP (Plane)

private lemma e2_sb_graph_coord (x : ℝ) : e2_sbGraph x 0 = x := rfl

private lemma e2_sb_graph_dist_le (x y : ℝ) :
    dist (e2_sbGraph x) (e2_sbGraph y) ≤
      |x - y| + |e2_sbHeight x - e2_sbHeight y| := by
  apply (sq_le_sq₀ dist_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  calc
    dist (e2_sbGraph x) (e2_sbGraph y) ^ 2 =
        (x-y)^2 + (e2_sbHeight x-e2_sbHeight y)^2 := by
      simpa only [Fin.sum_univ_two, e2_sbGraph, PiLp.toLp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs] using
        EuclideanSpace.dist_sq_eq (e2_sbGraph x) (e2_sbGraph y)
    _ ≤ (|x-y| + |e2_sbHeight x-e2_sbHeight y|)^2 := by
      nlinarith [sq_abs (x-y), sq_abs (e2_sbHeight x-e2_sbHeight y),
        mul_nonneg (abs_nonneg (x-y)) (abs_nonneg (e2_sbHeight x-e2_sbHeight y))]

/-- Projection onto the first coordinate controls the mass of every ball. -/
lemma e2_sb_ball_growth (hM : E2sbMeasurable) (z : Plane) (r : ℝ) :
    e2_sbSource (Metric.ball z r) ≤ ENNReal.ofReal (2*r) := by
  rw [e2_sbSource, Measure.map_apply hM.2.2 Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply (hM.2.2 Metric.isOpen_ball.measurableSet)]
  calc
    volume (e2_sbGraph ⁻¹' Metric.ball z r ∩ Ico 0 1) ≤
        volume (Ioo (z 0-r) (z 0+r)) := measure_mono (by
      intro x hx
      have hcoord : |x-z 0| ≤ dist (e2_sbGraph x) z := by
        simpa [Real.norm_eq_abs, dist_eq_norm, e2_sb_graph_coord] using
          (PiLp.norm_apply_le (e2_sbGraph x-z) 0)
      have hb := Metric.mem_ball.mp hx.1
      have ha := abs_lt.mp (hcoord.trans_lt hb)
      constructor <;> linarith)
    _ = ENNReal.ofReal (2*r) := by rw [Real.volume_Ioo]; congr 1; ring

private lemma e2_sb_tail_le_half (hG : E2sbGrid) (hT : E2sbTails)
    (j : ℕ) (hj : 1 ≤ j) : e2_sbTail j ≤ e2_sbEll j / 2 := by
  have hp : (2:ℝ) ≤ 2^(j+20) := by
    calc
      (2:ℝ) = 2^1 := by norm_num
      _ ≤ 2^(j+20) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact (hT.2.2.2.2.1 j hj).trans
    (div_le_div_of_nonneg_left (hG.1 j).le (by norm_num) hp)

/-- The generation cell containing a point of `[0,1)` stays inside `[0,1)`.
The integer subdivision of the unit interval is essential at its right endpoint. -/
private lemma e2_sb_cell_in_unit (hG : E2sbGrid) (j : ℕ) (x : ℝ)
    (hx : x ∈ Ico (0:ℝ) 1) :
    ∃ k : ℤ, x ∈ Ico ((k:ℝ)*e2_sbEll j) (((k:ℝ)+1)*e2_sbEll j) ∧
      Ico ((k:ℝ)*e2_sbEll j) (((k:ℝ)+1)*e2_sbEll j) ⊆ Ico (0:ℝ) 1 := by
  let k : ℤ := ⌊x/e2_sbEll j⌋
  have he := hG.1 j
  have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (div_nonneg hx.1 he.le)
  have hklo : (k:ℝ)*e2_sbEll j ≤ x := (le_div_iff₀ he).mp (Int.floor_le _)
  have hkhi : x < ((k:ℝ)+1)*e2_sbEll j := (div_lt_iff₀ he).mp (Int.lt_floor_add_one _)
  obtain ⟨c,hc⟩ := hG.2.2.2.2.1 j
  have hkcR : (k:ℝ) < (c:ℝ) := (mul_lt_mul_iff_left₀ he).mp
    (hklo.trans_lt (hx.2.trans_eq hc.symm))
  have hkc : k+1 ≤ (c:ℤ) := Int.add_one_le_iff.mpr (by exact_mod_cast hkcR)
  have hkc' : (k:ℝ)+1 ≤ (c:ℝ) := by exact_mod_cast hkc
  refine ⟨k, ⟨hklo,hkhi⟩, ?_⟩
  intro y hy
  refine ⟨(mul_nonneg (by exact_mod_cast hk0) he.le).trans hy.1, ?_⟩
  exact hy.2.trans_le ((mul_le_mul_of_nonneg_right hkc' he.le).trans_eq hc)

private lemma e2_sb_height_sub_le_tail (hD : E2sbDigit) (j : ℕ) (k : ℤ) (x y : ℝ)
    (hx : x ∈ Ico ((k:ℝ)*e2_sbEll j) (((k:ℝ)+1)*e2_sbEll j))
    (hy : y ∈ Ico ((k:ℝ)*e2_sbEll j) (((k:ℝ)+1)*e2_sbEll j)) :
    |e2_sbHeight y-e2_sbHeight x| ≤ e2_sbTail j := by
  have hold : e2_sbOldHeight j x = e2_sbOldHeight j y := by
    unfold e2_sbOldHeight
    apply Finset.sum_congr rfl
    intro i hi
    rw [hD.1 j (i+1) (by omega) (by have := Finset.mem_range.mp hi; omega) k x y hx hy]
  have hx' := hD.2.1 j x
  have hy' := hD.2.1 j y
  apply abs_le.mpr
  constructor <;> linarith

/-- Every point of the closure sees a full generation cell at radius `2ℓ_j`. -/
lemma e2_sb_cell_ball_mass (hG : E2sbGrid) (hT : E2sbTails)
    (hD : E2sbDigit) (hM : E2sbMeasurable) (z : Plane) (hz : z ∈ e2_sbSet)
    (j : ℕ) (hj : 1 ≤ j) :
    ENNReal.ofReal (e2_sbEll j) ≤ e2_sbSource (Metric.ball z (2*e2_sbEll j)) := by
  have he := hG.1 j
  obtain ⟨w, ⟨x,hx,rfl⟩, hxz⟩ := Metric.mem_closure_iff.mp hz
    (e2_sbEll j/2) (by positivity)
  obtain ⟨k,hxk,hunit⟩ := e2_sb_cell_in_unit hG j x hx
  have hin : Ico ((k:ℝ)*e2_sbEll j) (((k:ℝ)+1)*e2_sbEll j) ⊆
      e2_sbGraph ⁻¹' Metric.ball z (2*e2_sbEll j) ∩ Ico 0 1 := by
    intro y hy
    refine ⟨?_, hunit hy⟩
    have hxy : |y-x| < e2_sbEll j := abs_lt.mpr (by constructor <;> nlinarith [hxk.1,hxk.2,hy.1,hy.2])
    have hheight := e2_sb_height_sub_le_tail hD j k x y hxk hy
    have htail := e2_sb_tail_le_half hG hT j hj
    have hd := e2_sb_graph_dist_le y x
    have htri := dist_triangle (e2_sbGraph y) (e2_sbGraph x) z
    rw [dist_comm z] at hxz
    exact Metric.mem_ball.mpr (by linarith)
  rw [e2_sbSource, Measure.map_apply hM.2.2 Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply (hM.2.2 Metric.isOpen_ball.measurableSet)]
  calc
    ENNReal.ofReal (e2_sbEll j) =
        volume (Ico ((k:ℝ)*e2_sbEll j) (((k:ℝ)+1)*e2_sbEll j)) := by
      rw [Real.volume_Ico]; congr 1; ring
    _ ≤ _ := measure_mono hin

private lemma e2_sb_ell_tendsto_zero (hG : E2sbGrid) (hT : E2sbTails) :
    Tendsto e2_sbEll atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun j => (hG.1 j).le) _ hT.2.2.2.2.2.2.2.2
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hh := hG.2.2.2.2.2.2.1 j hj
  unfold e2_sbPeriod at hh
  have hn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
  nlinarith [hG.1 j, mul_nonneg hn (hG.1 j).le]

/-- The density estimate: global linear growth and both upper-density bounds
at every point of the Euclidean closure. -/
theorem e2_sb_density_proof (hG : E2sbGrid) (hT : E2sbTails)
    (hD : E2sbDigit) (hM : E2sbMeasurable) : E2sbDensity := by
  refine ⟨fun z r _ => e2_sb_ball_growth hM z r, ?_⟩
  intro z hz
  constructor
  · refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    have hlim : Tendsto (fun j => 2*e2_sbEll j) atTop (𝓝[>] (0:ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨by simpa using (e2_sb_ell_tendsto_zero hG hT).const_mul 2,
        Eventually.of_forall fun j => mul_pos (by norm_num) (hG.1 j)⟩
    apply hlim.frequently
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hr : 0 < 2*e2_sbEll j := mul_pos (by norm_num) (hG.1 j)
    calc
      (2:ℝ≥0∞)⁻¹ = ENNReal.ofReal (e2_sbEll j) / ENNReal.ofReal (2*e2_sbEll j) := by
        rw [← ENNReal.ofReal_div_of_pos hr]
        have heq : e2_sbEll j / (2*e2_sbEll j) = (1:ℝ)/2 := by field_simp [ne_of_gt (hG.1 j)]
        rw [heq, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
        norm_num
      _ ≤ _ := ENNReal.div_le_div_right (e2_sb_cell_ball_mass hG hT hD hM z hz j hj) _
  · refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    change e2_sbSource (Metric.ball z r) / ENNReal.ofReal r ≤ 2
    calc
      _ ≤ ENNReal.ofReal (2*r) / ENNReal.ofReal r :=
        ENNReal.div_le_div_right (e2_sb_ball_growth hM z r) _
      _ = 2 := by rw [← ENNReal.ofReal_div_of_pos hr']; simp [ne_of_gt hr']

end ParabolicRectifiability.Examples
