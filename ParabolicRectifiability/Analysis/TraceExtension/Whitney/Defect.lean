import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Data
import ParabolicRectifiability.Measure.ScaleIntegrals

/-! # Cell incidence and the summable cube defect

Put `c = a/3`, `M = 1 + D/c = 1 + 3D/a` and `E = 2 + 2D/c = 2 + 6D/a`.

*Incidence geometry.* If the cell `Q_j` meets the open ball `P(y,s)` and
`d_P(y,F₀) ≤ 2s`, then a point `q` of the intersection gives
`a r_j ≤ d_P(q,F₀) ≤ d_P(y,F₀) + d_P(q,y) < 3s`; hence the positive cube radius
`c r_j < s`, and `d_P(p_j,y) < s + D r_j ≤ M s`. If moreover `y ∈ P(z,R)` and
`s < R`, every point of `Q_j` lies within `2 D r_j + s + R < E R` of `z`.

*Measurability.* The joint incidence set
`{(y,s) : j ∈ J(y,s)} = ⋃_{q ∈ Q_j} {(y,s) : d_P(q,y) < s}` is open, so the
cube-defect integrand is jointly measurable.

*The defect bound.* Dominate `cubeDefect y s` by the countable sum of
`r_j^(k+2) 1[c r_j < s, d_P(y,p_j) < M s] s^(-k-2)` over the relevant cells
`Q_j ⊆ P(z, E R)`. Tonelli and the center-volume identity
`|P(p_j, M s)| = v_m M^k s^k` reduce each term to the inverse-square tail
`∫_{c r_j}^∞ s^(-2) ds/s = (c r_j)^(-2)/2`; the disjoint relevant cells pack into
`P(z, E R)`. This gives the coefficient
`v_m^2 M^k E^k / (2 c^2) R^k`, `v_m = 2 ω_m`, `k = m + 2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace WhitneyData

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}

section Incidence

variable (W : WhitneyData m ι F₀ D a)

theorem mem_incidence_iff {y : Space m} {s : ℝ} {j : ι} :
    j ∈ W.incidence y s ↔ ∃ q ∈ W.cell j, dist q y < s :=
  Iff.rfl

/-- Radius threshold: a cell meeting `P(y,s)` with `d_P(y,F₀) ≤ 2s` has `a r_j < 3s`. -/
theorem mul_radius_lt_of_mem_incidence {y : Space m} {s : ℝ}
    (hy : Metric.infDist y F₀ ≤ 2 * s) {j : ι} (hj : j ∈ W.incidence y s) :
    a * W.radius j < 3 * s := by
  obtain ⟨q, hq, hqy⟩ := (W.mem_incidence_iff).mp hj
  calc
    a * W.radius j ≤ Metric.infDist q F₀ := W.le_infDist j q hq
    _ ≤ Metric.infDist y F₀ + dist q y := Metric.infDist_le_infDist_add_dist
    _ < 2 * s + s := by linarith
    _ = 3 * s := by ring

/-- Positive cube radius: `(a/3) r_j < s` for incident cells in the macroscopic range. -/
theorem div_three_mul_radius_lt {y : Space m} {s : ℝ}
    (hy : Metric.infDist y F₀ ≤ 2 * s) {j : ι} (hj : j ∈ W.incidence y s) :
    a / 3 * W.radius j < s := by
  have h := W.mul_radius_lt_of_mem_incidence hy hj
  calc
    a / 3 * W.radius j = a * W.radius j / 3 := by ring
    _ < s := by linarith

/-- An incident center lies within `s + D r_j` of `y`. -/
theorem dist_center_lt_of_mem_incidence {y : Space m} {s : ℝ} {j : ι}
    (hj : j ∈ W.incidence y s) : dist (W.center j) y < s + D * W.radius j := by
  obtain ⟨q, hq, hqy⟩ := (W.mem_incidence_iff).mp hj
  have hqc : dist q (W.center j) ≤ D * W.radius j :=
    Metric.mem_closedBall.mp (W.cell_subset j hq)
  calc
    dist (W.center j) y ≤ dist (W.center j) q + dist q y := dist_triangle _ _ _
    _ < s + D * W.radius j := by
      rw [dist_comm]
      linarith

/-- `D r_j ≤ (3D/a) s` for incident cells in the macroscopic range. -/
theorem mul_radius_le_of_mem_incidence {y : Space m} {s : ℝ}
    (hy : Metric.infDist y F₀ ≤ 2 * s) {j : ι} (hj : j ∈ W.incidence y s) :
    D * W.radius j ≤ 3 * D / a * s := by
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have h := W.mul_radius_lt_of_mem_incidence hy hj
  have hr : W.radius j ≤ 3 * s / a := by
    rw [le_div_iff₀ ha]
    linarith
  calc
    D * W.radius j ≤ D * (3 * s / a) := mul_le_mul_of_nonneg_left hr hD
    _ = 3 * D / a * s := by ring

/-- Center containment: incident centers lie in the open ball `P(y, (1 + 3D/a) s)`. -/
theorem center_mem_ball_of_mem_incidence {y : Space m} {s : ℝ}
    (hy : Metric.infDist y F₀ ≤ 2 * s) {j : ι} (hj : j ∈ W.incidence y s) :
    W.center j ∈ Metric.ball y ((1 + 3 * D / a) * s) := by
  rw [Metric.mem_ball]
  have h1 := W.dist_center_lt_of_mem_incidence hj
  have h2 := W.mul_radius_le_of_mem_incidence hy hj
  calc
    dist (W.center j) y < s + D * W.radius j := h1
    _ ≤ s + 3 * D / a * s := by linarith
    _ = (1 + 3 * D / a) * s := by ring

/-- Relevant-cell containment: an incident cell, for `y ∈ P(z,R)` and `s < R` in the
macroscopic range, lies in `P(z, (2 + 6D/a) R)`. -/
theorem cell_subset_ball_of_mem_incidence {z y : Space m} {R s : ℝ}
    (hyz : y ∈ Metric.ball z R) (hsR : s < R) (hy : Metric.infDist y F₀ ≤ 2 * s) {j : ι}
    (hj : j ∈ W.incidence y s) : W.cell j ⊆ Metric.ball z ((2 + 6 * D / a) * R) := by
  intro q hq
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have h1 : dist q (W.center j) ≤ D * W.radius j :=
    Metric.mem_closedBall.mp (W.cell_subset j hq)
  have h2 := W.dist_center_lt_of_mem_incidence hj
  have h3 := W.mul_radius_le_of_mem_incidence hy hj
  have h4 : 3 * D / a * s ≤ 3 * D / a * R :=
    mul_le_mul_of_nonneg_left hsR.le (div_nonneg (by linarith) ha.le)
  have h5 : dist y z < R := Metric.mem_ball.mp hyz
  have h6 : (2 + 6 * D / a) * R = 2 * R + 2 * (3 * D / a * R) := by ring
  rw [Metric.mem_ball]
  calc
    dist q z ≤ dist q (W.center j) + dist (W.center j) y + dist y z := dist_triangle4 _ _ _ _
    _ < (2 + 6 * D / a) * R := by linarith

end Incidence

section Measurability

variable (W : WhitneyData m ι F₀ D a)

/-- Joint incidence: `{(y,s) : j ∈ J(y,s)} = ⋃_{q ∈ Q_j} {(y,s) : d_P(q,y) < s}`. -/
theorem setOf_mem_incidence_eq (j : ι) :
    {p : Space m × ℝ | j ∈ W.incidence p.1 p.2} =
      ⋃ q ∈ W.cell j, {p : Space m × ℝ | dist q p.1 < p.2} := by
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop, W.mem_incidence_iff]

/-- The joint incidence set is open (although the cell need not be). -/
theorem isOpen_setOf_mem_incidence (j : ι) :
    IsOpen {p : Space m × ℝ | j ∈ W.incidence p.1 p.2} := by
  rw [W.setOf_mem_incidence_eq j]
  exact isOpen_biUnion fun q _ => isOpen_lt (continuous_const.dist continuous_fst) continuous_snd

/-- Joint measurability of the cube-defect integrand `(y,s) ↦ cubeDefect y s`. -/
theorem measurable_cubeDefect [Countable ι] :
    Measurable fun p : Space m × ℝ => W.cubeDefect p.1 p.2 := by
  unfold cubeDefect
  refine Measurable.mul
    (by fun_prop : Measurable fun p : Space m × ℝ => (ENNReal.ofReal p.2)⁻¹ ^ (m + 4))
    (Measurable.tsum fun j => ?_)
  have h : (fun p : Space m × ℝ => (W.incidence p.1 p.2).indicator
        (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j) =
      {p : Space m × ℝ | j ∈ W.incidence p.1 p.2}.indicator
        (fun _ => ENNReal.ofReal (W.radius j ^ (m + 4))) := by
    funext p
    by_cases hj : j ∈ W.incidence p.1 p.2
    · rw [indicator_of_mem hj,
        indicator_of_mem (show p ∈ {p : Space m × ℝ | j ∈ W.incidence p.1 p.2} from hj)]
    · rw [indicator_of_notMem hj,
        indicator_of_notMem (show p ∉ {p : Space m × ℝ | j ∈ W.incidence p.1 p.2} from hj)]
  rw [h]
  exact measurable_const.indicator (W.isOpen_setOf_mem_incidence j).measurableSet

end Measurability

section Defect

variable (W : WhitneyData m ι F₀ D a)

/-- The tent of the cell `Q_j`: scales above the positive cube radius `(a/3) r_j`
whose ball `P(y, (1 + 3D/a) s)` contains the center `p_j`. -/
def defectTent (j : ι) : Set (Space m × ℝ) :=
  {p | a / 3 * W.radius j < p.2 ∧ dist p.1 (W.center j) < (1 + 3 * D / a) * p.2}

/-- The dominating kernel `1_{tent}(y,s) s^(-k-2)`. -/
def defectKernel (j : ι) (p : Space m × ℝ) : ℝ≥0∞ :=
  (W.defectTent j).indicator (fun p => (ENNReal.ofReal p.2)⁻¹ ^ (m + 4)) p

theorem measurableSet_defectTent (j : ι) : MeasurableSet (W.defectTent j) :=
  ((isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt (continuous_fst.dist continuous_const)
      (continuous_const.mul continuous_snd))).measurableSet

theorem measurable_defectKernel (j : ι) : Measurable (W.defectKernel j) :=
  (by fun_prop : Measurable fun p : Space m × ℝ => (ENNReal.ofReal p.2)⁻¹ ^ (m + 4)).indicator
    (W.measurableSet_defectTent j)

/-- Pointwise domination of the cube defect in the macroscopic range by the relevant
tent kernels. -/
theorem cubeDefect_le_tsum_defectKernel {z y : Space m} {R s : ℝ}
    (hyz : y ∈ Metric.ball z R) (hs : s ∈ Ioo 0 R) (hy : Metric.infDist y F₀ ≤ 2 * s) :
    W.cubeDefect y s ≤
      ∑' j, {j | W.cell j ⊆ Metric.ball z ((2 + 6 * D / a) * R)}.indicator
          (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j * W.defectKernel j (y, s) := by
  unfold cubeDefect
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases hj : j ∈ W.incidence y s
  · have hrel : j ∈ {j | W.cell j ⊆ Metric.ball z ((2 + 6 * D / a) * R)} :=
      W.cell_subset_ball_of_mem_incidence hyz hs.2 hy hj
    have hU : (y, s) ∈ W.defectTent j := by
      refine ⟨W.div_three_mul_radius_lt hy hj, ?_⟩
      rw [dist_comm]
      exact Metric.mem_ball.mp (W.center_mem_ball_of_mem_incidence hy hj)
    rw [indicator_of_mem hj, indicator_of_mem hrel, defectKernel, indicator_of_mem hU]
    exact le_of_eq (mul_comm _ _)
  · rw [indicator_of_notMem hj, mul_zero]
    exact zero_le

/-- Center-volume identity: integrating the tent kernel in space at a fixed scale gives
`1[(a/3) r_j < s] v_m M^k s^(-2)`. -/
theorem lintegral_defectKernel_space (j : ι) (s : ℝ) :
    ∫⁻ y, W.defectKernel j (y, s) ∂parabolicVolume m =
      (Ioi (a / 3 * W.radius j)).indicator
        (fun s => 2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2) *
          (ENNReal.ofReal s)⁻¹ ^ 2) s := by
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hM : 0 < 1 + 3 * D / a := by
    have : 0 ≤ 3 * D / a := div_nonneg (by linarith) ha.le
    linarith
  by_cases hs : a / 3 * W.radius j < s
  · have hs0 : 0 < s := lt_trans (mul_pos (by linarith) (W.radius_pos j)) hs
    have hMs : 0 < (1 + 3 * D / a) * s := mul_pos hM hs0
    have hfun : (fun y => W.defectKernel j (y, s)) =
        (Metric.ball (W.center j) ((1 + 3 * D / a) * s)).indicator
          (fun _ => (ENNReal.ofReal s)⁻¹ ^ (m + 4)) := by
      funext y
      by_cases hy : dist y (W.center j) < (1 + 3 * D / a) * s
      · rw [defectKernel, indicator_of_mem (show (y, s) ∈ W.defectTent j from ⟨hs, hy⟩),
          indicator_of_mem (Metric.mem_ball.mpr hy)]
      · rw [defectKernel, indicator_of_notMem (show (y, s) ∉ W.defectTent j from fun h => hy h.2),
          indicator_of_notMem (fun h => hy (Metric.mem_ball.mp h))]
    have hx0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs0).ne'
    have key : (ENNReal.ofReal s)⁻¹ ^ (m + 4) * ENNReal.ofReal s ^ (m + 2) =
        (ENNReal.ofReal s)⁻¹ ^ 2 := by
      rw [show m + 4 = 2 + (m + 2) by omega, pow_add, mul_assoc, ← mul_pow,
        ENNReal.inv_mul_cancel hx0 ENNReal.ofReal_ne_top, one_pow, mul_one]
    rw [hfun, lintegral_indicator_const measurableSet_ball, parabolicVolume_ball _ _ hMs,
      ENNReal.ofReal_mul hM.le, mul_pow, indicator_of_mem (show s ∈ Ioi (a / 3 * W.radius j) from hs),
      ← key]
    ring
  · have hfun : (fun y => W.defectKernel j (y, s)) = fun _ => 0 := by
      funext y
      rw [defectKernel, indicator_of_notMem (show (y, s) ∉ W.defectTent j from fun h => hs h.1)]
    rw [hfun, lintegral_zero, indicator_of_notMem (show s ∉ Ioi (a / 3 * W.radius j) from hs)]

/-- Tonelli and the inverse-square tail: the full tent integral is
`v_m M^k ((a/3) r_j)^(-2) / 2`. -/
theorem lintegral_lintegral_defectKernel (j : ι) :
    ∫⁻ y, ∫⁻ s, W.defectKernel j (y, s) ∂scaleMeasure ∂parabolicVolume m =
      2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2) *
        ENNReal.ofReal (((a / 3 * W.radius j) ^ 2)⁻¹ / 2) := by
  have hc : 0 < a / 3 * W.radius j := mul_pos (by linarith [W.a_pos]) (W.radius_pos j)
  have hK : 2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (omega_lt_top m).ne)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  rw [lintegral_lintegral_swap (f := fun y s => W.defectKernel j (y, s))
    (W.measurable_defectKernel j).aemeasurable]
  simp_rw [W.lintegral_defectKernel_space j]
  rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul' _ _ hK,
    lintegral_inv_pow_Ioi_scaleMeasure 2 two_pos hc, Nat.cast_ofNat]

/-- Packing: the disjoint cells contained in a measurable set `S` have total volume
`Σ r_j^k ≤ |S|`. -/
theorem tsum_indicator_radius_le [Countable ι] (S : Set (Space m)) :
    ∑' j, {j | W.cell j ⊆ S}.indicator (fun j => ENNReal.ofReal (W.radius j ^ (m + 2))) j ≤
      parabolicVolume m S := by
  have h : ∀ j, {j | W.cell j ⊆ S}.indicator (fun j => ENNReal.ofReal (W.radius j ^ (m + 2))) j =
      {j | W.cell j ⊆ S}.indicator (fun j => parabolicVolume m (W.cell j)) j := by
    intro j
    simp only [W.volume_cell]
  rw [tsum_congr h, ← tsum_subtype]
  calc
    ∑' j : {j | W.cell j ⊆ S}, parabolicVolume m (W.cell j) =
        parabolicVolume m (⋃ j : {j | W.cell j ⊆ S}, W.cell j) :=
      (measure_iUnion (f := fun j : {j | W.cell j ⊆ S} => W.cell j)
        (fun i k hik => W.pairwise_disjoint fun h => hik (Subtype.ext h))
        fun i => W.measurableSet_cell i).symm
    _ ≤ parabolicVolume m S := measure_mono (iUnion_subset fun j => j.2)

end Defect

end WhitneyData

/-- **The summable cube defect.** For every `z` and `R > 0`, with `c = a/3`,
`∫_{P(z,R)} ∫_{0<s<R, dist(y,F₀) ≤ 2s} s^(-k-2) Σ_{J(y,s)} r_j^(k+2) ds/s dy
≤ v_m^2 (1+D/c)^k (2+2D/c)^k / (2c^2) · R^k`, `v_m = 2 ω_m`. -/
theorem whitney_cube_defect_le_proof {m : ℕ} {ι : Type*} [Countable ι] {F₀ : Set (Space m)}
    {D a : ℝ} (W : WhitneyData m ι F₀ D a) (_hF₀ : IsClosed F₀) (z : Space m) (R : ℝ)
    (hR : 0 < R) :
    ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
        W.cubeDefect y s ∂scaleMeasure ∂parabolicVolume m ≤
      (2 * omega m) ^ 2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 2) *
        (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2) * R ^ (m + 2)) := by
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hDa : 0 ≤ 3 * D / a := div_nonneg (by linarith) ha.le
  have hM : 0 < 1 + 3 * D / a := by linarith
  have hE : 0 < 2 + 6 * D / a := by
    have : 6 * D / a = 2 * (3 * D / a) := by ring
    linarith
  have hER : 0 < (2 + 6 * D / a) * R := mul_pos hE hR
  -- the relevant cells and their weights
  let w : ι → ℝ≥0∞ := {j | W.cell j ⊆ Metric.ball z ((2 + 6 * D / a) * R)}.indicator
    (fun j => ENNReal.ofReal (W.radius j ^ (m + 4)))
  have hin : ∀ j y, Measurable fun s => W.defectKernel j (y, s) := fun j _ =>
    (W.measurable_defectKernel j).comp measurable_prodMk_left
  have hout : ∀ j, Measurable fun y => ∫⁻ s, W.defectKernel j (y, s) ∂scaleMeasure :=
    fun j => (W.measurable_defectKernel j).lintegral_prod_right'
  have hSmeas : ∀ y : Space m, MeasurableSet (Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s}) :=
    fun _ => measurableSet_Ioo.inter (measurableSet_le measurable_const (measurable_const.mul measurable_id))
  -- termwise algebra
  have hterm : ∀ j, w j * ((2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (((a / 3 * W.radius j) ^ 2)⁻¹ / 2)) =
      (2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (1 / (2 * (a / 3) ^ 2)) *
        {j | W.cell j ⊆ Metric.ball z ((2 + 6 * D / a) * R)}.indicator
          (fun j => ENNReal.ofReal (W.radius j ^ (m + 2))) j := by
    intro j
    by_cases hj : j ∈ {j | W.cell j ⊆ Metric.ball z ((2 + 6 * D / a) * R)}
    · have hr : 0 < W.radius j := W.radius_pos j
      have hr2 : W.radius j ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
      simp only [w, indicator_of_mem hj]
      have hreal : W.radius j ^ (m + 4) * (((a / 3 * W.radius j) ^ 2)⁻¹ / 2) =
          1 / (2 * (a / 3) ^ 2) * W.radius j ^ (m + 2) := by
        calc
          W.radius j ^ (m + 4) * (((a / 3 * W.radius j) ^ 2)⁻¹ / 2) =
              W.radius j ^ (m + 2) * (W.radius j ^ 2 * (W.radius j ^ 2)⁻¹) *
                (1 / (2 * (a / 3) ^ 2)) := by ring
          _ = 1 / (2 * (a / 3) ^ 2) * W.radius j ^ (m + 2) := by
            rw [mul_inv_cancel₀ hr2]
            ring
      calc
        ENNReal.ofReal (W.radius j ^ (m + 4)) *
            ((2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (((a / 3 * W.radius j) ^ 2)⁻¹ / 2)) =
            (2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) *
              (ENNReal.ofReal (W.radius j ^ (m + 4)) *
              ENNReal.ofReal (((a / 3 * W.radius j) ^ 2)⁻¹ / 2)) := by ring
        _ = (2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (1 / (2 * (a / 3) ^ 2) * W.radius j ^ (m + 2)) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg hr.le _), hreal]
        _ = (2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (1 / (2 * (a / 3) ^ 2)) *
            ENNReal.ofReal (W.radius j ^ (m + 2)) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (2 * (a / 3) ^ 2))]
          ring
    · simp only [w, indicator_of_notMem hj, zero_mul, mul_zero]
  calc
    ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
        W.cubeDefect y s ∂scaleMeasure ∂parabolicVolume m
        ≤ ∫⁻ y in Metric.ball z R, ∫⁻ s in Ioo 0 R ∩ {s | Metric.infDist y F₀ ≤ 2 * s},
          ∑' j, w j * W.defectKernel j (y, s) ∂scaleMeasure ∂parabolicVolume m :=
      setLIntegral_mono' measurableSet_ball fun y hy =>
        setLIntegral_mono' (hSmeas y) fun s hs =>
          W.cubeDefect_le_tsum_defectKernel hy hs.1 hs.2
    _ ≤ ∫⁻ y, ∫⁻ s, ∑' j, w j * W.defectKernel j (y, s) ∂scaleMeasure ∂parabolicVolume m :=
      (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun _ => setLIntegral_le_lintegral _ _)
    _ = ∫⁻ y, ∑' j, w j * ∫⁻ s, W.defectKernel j (y, s) ∂scaleMeasure ∂parabolicVolume m := by
      refine lintegral_congr fun y => ?_
      rw [lintegral_tsum fun j => ((hin j y).const_mul (w j)).aemeasurable]
      exact tsum_congr fun j => lintegral_const_mul _ (hin j y)
    _ = ∑' j, w j * ∫⁻ y, ∫⁻ s, W.defectKernel j (y, s) ∂scaleMeasure ∂parabolicVolume m := by
      rw [lintegral_tsum fun j => ((hout j).const_mul (w j)).aemeasurable]
      exact tsum_congr fun j => lintegral_const_mul _ (hout j)
    _ = ∑' j, w j * ((2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (((a / 3 * W.radius j) ^ 2)⁻¹ / 2)) :=
      tsum_congr fun j => by rw [W.lintegral_lintegral_defectKernel j]
    _ = (2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (1 / (2 * (a / 3) ^ 2)) *
        ∑' j, {j | W.cell j ⊆ Metric.ball z ((2 + 6 * D / a) * R)}.indicator
          (fun j => ENNReal.ofReal (W.radius j ^ (m + 2))) j := by
      rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    _ ≤ (2 * omega m * ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2)) * ENNReal.ofReal (1 / (2 * (a / 3) ^ 2)) *
        parabolicVolume m (Metric.ball z ((2 + 6 * D / a) * R)) :=
      mul_le_mul_right (W.tsum_indicator_radius_le _) _
    _ = (2 * omega m) ^ 2 * (ENNReal.ofReal (1 + 3 * D / a) ^ (m + 2) *
        ENNReal.ofReal (1 / (2 * (a / 3) ^ 2)) *
          ENNReal.ofReal ((2 + 6 * D / a) * R) ^ (m + 2)) := by
      rw [parabolicVolume_ball _ _ hER]
      ring
    _ = (2 * omega m) ^ 2 * ENNReal.ofReal ((1 + 3 * D / a) ^ (m + 2) *
        (2 + 6 * D / a) ^ (m + 2) / (2 * (a / 3) ^ 2) * R ^ (m + 2)) := by
      rw [← ENNReal.ofReal_pow hM.le, ← ENNReal.ofReal_pow hER.le,
        ← ENNReal.ofReal_mul (pow_nonneg hM.le _),
        ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hM.le _)
          (by positivity : (0 : ℝ) ≤ 1 / (2 * (a / 3) ^ 2)))]
      congr 2
      rw [mul_pow]
      ring

end ParabolicRectifiability
