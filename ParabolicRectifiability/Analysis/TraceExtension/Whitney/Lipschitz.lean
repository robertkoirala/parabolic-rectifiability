import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Filling

/-! # Global Lipschitz bound for the Whitney filling

Let `F` be the filling of a smooth Whitney partition and
`g` be `L`-Lipschitz on the node set. Put `h = d_P(p,q)` and `δ = d_P(·,F₀)`.

* *Far case* `δ(p) ≤ 4h`: for a nearest point `x ∈ F₀` of `p`, the trace comparison
  of `whitneyFilling_sub_le_proof` gives `‖F(p) - F(q)‖ ≤ C₁ L (d(p,x) + d(q,x)) ≤ 9 C₁ L h`,
  `C₁ = 1 + (H+D)/a`.
* *Near case* `4h < δ(p)`: then `q ∉ F₀`, the cells of `p` and `q` have comparable
  radii, and `F(p) - F(q) = Σ_i (φ_i(p) - φ_i(q)) (g(p_i) - g(p_j))` over the at most
  `2N` active indices. The parabolic derivative bounds of each weight give
  `|φ_i(p) - φ_i(q)| ≤ K h / r_i + K h² / r_i²`, and `h ≲ r_j`, `d(p_i,p_j) ≲ r_j`.

The derivative bounds of the weights are used directly (mean value inequality in the
spatial and time variables), so no derivative bound for `F` itself is needed. If
`H < 0` no point lies off `F₀` and `F = g`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

section ParabolicMeanValue

variable {m : ℕ}

theorem point_fst_snd_val (z : Space m) : point z.1 z.2.val = z :=
  rfl

theorem dist_eq_max_norm_sqrt (p q : Space m) :
    dist p q = max ‖p.1 - q.1‖ (Real.sqrt |p.2.val - q.2.val|) :=
  dist_point p.1 q.1 p.2.val q.2.val

theorem norm_fst_sub_le_dist (p q : Space m) : ‖p.1 - q.1‖ ≤ dist p q := by
  rw [dist_eq_max_norm_sqrt]
  exact le_max_left _ _

theorem abs_snd_sub_le_dist_sq (p q : Space m) : |p.2.val - q.2.val| ≤ dist p q ^ 2 := by
  have h : Real.sqrt |p.2.val - q.2.val| ≤ dist p q := by
    rw [dist_eq_max_norm_sqrt]
    exact le_max_right _ _
  calc
    |p.2.val - q.2.val| = Real.sqrt |p.2.val - q.2.val| ^ 2 :=
      (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ dist p q ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- Differentiability of a spatial slice of a function of ordinary coordinates. -/
theorem differentiableAt_slice_space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : Coordinates m → E} {v : Spatial m} {t : ℝ} (h : DifferentiableAt ℝ Φ (v, t)) :
    DifferentiableAt ℝ (fun w => Φ (w, t)) v :=
  h.comp v (differentiableAt_id.prodMk (differentiableAt_const t))

/-- Differentiability of a time slice of a function of ordinary coordinates. -/
theorem differentiableAt_slice_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : Coordinates m → E} {u : Spatial m} {t : ℝ} (h : DifferentiableAt ℝ Φ (u, t)) :
    DifferentiableAt ℝ (fun s => Φ (u, s)) t :=
  h.comp t ((differentiableAt_const u).prodMk differentiableAt_id)

/-- Parabolic mean value inequality for a function with parabolic derivative bounds:
`|φ(p) - φ(q)| ≤ (K/r) ‖u_p - u_q‖ + (K/r²) |t_p - t_q|`. -/
theorem HasParabolicDerivBounds.abs_sub_le {φ : Space m → ℝ} {K r : ℝ}
    (h : HasParabolicDerivBounds φ K r) (p q : Space m) :
    |φ p - φ q| ≤ K / r * ‖p.1 - q.1‖ + K / r ^ 2 * |p.2.val - q.2.val| := by
  have hdiff : Differentiable ℝ (fun y : Coordinates m => φ (point y.1 y.2)) :=
    h.contDiff.differentiable two_ne_zero
  have h1 : ‖φ (point p.1 p.2.val) - φ (point q.1 p.2.val)‖ ≤ K / r * ‖p.1 - q.1‖ := by
    have hd : ∀ v ∈ (univ : Set (Spatial m)),
        DifferentiableAt ℝ (fun v => φ (point v p.2.val)) v := fun v _ => by
      have h' := differentiableAt_slice_space (hdiff (v, p.2.val))
      exact h'
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le hd
      (fun v _ => h.spatial_le v p.2.val) (mem_univ q.1) (mem_univ p.1)
  have h2 : ‖φ (point q.1 p.2.val) - φ (point q.1 q.2.val)‖ ≤
      K / r ^ 2 * ‖p.2.val - q.2.val‖ := by
    have hd : ∀ t ∈ (univ : Set ℝ), DifferentiableAt ℝ (fun t => φ (point q.1 t)) t :=
      fun t _ => by
        have h' := differentiableAt_slice_time (hdiff (q.1, t))
        exact h'
    exact convex_univ.norm_image_sub_le_of_norm_deriv_le hd
      (fun t _ => by simpa only [Real.norm_eq_abs] using h.time_le q.1 t)
      (mem_univ q.2.val) (mem_univ p.2.val)
  rw [Real.norm_eq_abs] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h2
  calc
    |φ p - φ q| = |(φ (point p.1 p.2.val) - φ (point q.1 p.2.val)) +
        (φ (point q.1 p.2.val) - φ (point q.1 q.2.val))| := by
      rw [sub_add_sub_cancel]
      rfl
    _ ≤ |φ (point p.1 p.2.val) - φ (point q.1 p.2.val)| +
        |φ (point q.1 p.2.val) - φ (point q.1 q.2.val)| := abs_add_le _ _
    _ ≤ K / r * ‖p.1 - q.1‖ + K / r ^ 2 * |p.2.val - q.2.val| := add_le_add h1 h2

end ParabolicMeanValue

section Lipschitz

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H b K : ℝ} {N : ℕ}
  {W : WhitneyData m ι F₀ D a}

/-- If some point lies off `F₀`, the locality constant is nonnegative. -/
theorem WhitneyWeights.nonneg_of_notMem (φ : WhitneyWeights W H) {q : Space m}
    (hq : q ∉ F₀) : 0 ≤ H := by
  obtain ⟨j, hj⟩ := W.exists_mem_cell hq
  obtain ⟨i, hi⟩ : ∃ i, φ.weight i q ≠ 0 := by
    by_contra hex
    have hall : ∀ i, φ.weight i q = 0 := fun i => by
      by_contra h
      exact hex ⟨i, h⟩
    have h0 : HasSum (fun i => φ.weight i q) 0 := by
      rw [show (fun i => φ.weight i q) = fun _ => (0 : ℝ) from funext hall]
      exact hasSum_zero
    exact one_ne_zero ((φ.hasSum_one q hq).unique h0)
  have hd := φ.center_dist_le i j q hj hi
  have hr := W.radius_pos j
  by_contra hH
  have : H * W.radius j < 0 := mul_neg_of_neg_of_pos (not_le.mp hH) hr
  linarith [dist_nonneg (x := W.center i) (y := W.center j)]

/-- On a cell, the distance to `F₀` is at most `(b+D) r_j`. -/
theorem WhitneyPartition.infDist_le_of_mem_cell (P : WhitneyPartition W H b K N) {j : ι}
    {p : Space m} (hp : p ∈ W.cell j) : Metric.infDist p F₀ ≤ (b + D) * W.radius j := by
  have h1 := P.infDist_center_le j
  have h2 : dist p (W.center j) ≤ D * W.radius j := W.dist_center_le hp
  calc
    Metric.infDist p F₀ ≤ Metric.infDist (W.center j) F₀ + dist p (W.center j) :=
      Metric.infDist_le_infDist_add_dist
    _ ≤ b * W.radius j + D * W.radius j := add_le_add h1 h2
    _ = (b + D) * W.radius j := by ring

/-- At most `N` weights are active at a point off `F₀`. -/
theorem WhitneyPartition.card_activeFinset_le (P : WhitneyPartition W H b K N) {q : Space m}
    (hq : q ∉ F₀) : (P.activeFinset hq).card ≤ N := by
  have h := P.overlap_le q
  rw [← (P.finite_active hq).coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-- Real bookkeeping for one index of the near case. -/
theorem near_term_le {Δ e K' μ β Λ L h r ri : ℝ} (hri : 0 < ri) (hr : 0 < r)
    (hK' : 0 ≤ K') (hμ : r ≤ μ * ri) (hh : 0 ≤ h) (hhr : h ≤ β / 4 * r)
    (hw : |Δ| ≤ K' / ri * h + K' / ri ^ 2 * h ^ 2) (he0 : 0 ≤ e) (he : e ≤ L * (Λ * r)) :
    |Δ| * e ≤ (K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * h := by
  have hμ0 : 0 ≤ μ := by
    by_contra hneg
    have : μ * ri < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hri
    linarith
  have hinv : 1 / ri ≤ μ / r := by
    rw [div_le_div_iff₀ hri hr]
    linarith
  have hinv0 : 0 ≤ 1 / ri := (one_div_pos.mpr hri).le
  have hx0 : 0 ≤ h / r := div_nonneg hh hr.le
  have hx : h / r ≤ β / 4 := by
    rw [div_le_iff₀ hr]
    linarith
  have t1 : K' / ri * h ≤ K' * μ * (h / r) := by
    calc
      K' / ri * h = K' * (1 / ri) * h := by ring
      _ ≤ K' * (μ / r) * h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hK') hh
      _ = K' * μ * (h / r) := by ring
  have t2 : K' / ri ^ 2 * h ^ 2 ≤ K' * μ ^ 2 * β / 4 * (h / r) := by
    have hsq : (1 / ri) ^ 2 ≤ (μ / r) ^ 2 := pow_le_pow_left₀ hinv0 hinv 2
    calc
      K' / ri ^ 2 * h ^ 2 = K' * (1 / ri) ^ 2 * h ^ 2 := by ring
      _ ≤ K' * (μ / r) ^ 2 * h ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hK') (sq_nonneg h)
      _ = K' * μ ^ 2 * (h / r) * (h / r) := by ring
      _ ≤ K' * μ ^ 2 * (h / r) * (β / 4) :=
        mul_le_mul_of_nonneg_left hx (mul_nonneg (mul_nonneg hK' (sq_nonneg μ)) hx0)
      _ = K' * μ ^ 2 * β / 4 * (h / r) := by ring
  have hA : |Δ| ≤ (K' * μ + K' * μ ^ 2 * β / 4) * (h / r) := by
    have := add_le_add t1 t2
    calc
      |Δ| ≤ K' / ri * h + K' / ri ^ 2 * h ^ 2 := hw
      _ ≤ K' * μ * (h / r) + K' * μ ^ 2 * β / 4 * (h / r) := this
      _ = (K' * μ + K' * μ ^ 2 * β / 4) * (h / r) := by ring
  have hA0 : 0 ≤ (K' * μ + K' * μ ^ 2 * β / 4) * (h / r) := (abs_nonneg _).trans hA
  calc
    |Δ| * e ≤ ((K' * μ + K' * μ ^ 2 * β / 4) * (h / r)) * (L * (Λ * r)) :=
      mul_le_mul hA he he0 hA0
    _ = (K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * (h / r * r) := by ring
    _ = (K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * h := by rw [div_mul_cancel₀ h hr.ne']

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Near case of the Lipschitz estimate: if `4 d(p,q) < δ(p)` then
`‖F(p) - F(q)‖ ≤ 2N (K'μ + K'μ²β/4) Λ L d(p,q)`, for any constants dominating the
geometric ones. -/
theorem WhitneyPartition.norm_whitneyFilling_sub_le_near (P : WhitneyPartition W H b K N)
    (g : Space m → Y) {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet)
    {K' β μ Λ H' : ℝ} (hK : K ≤ K') (hK' : 0 ≤ K') (hβ : b + D ≤ β) (hβ0 : 0 ≤ β)
    (hμ1 : 4 ≤ μ) (hμ2 : 16 * β / (3 * a) ≤ μ) (hH : H ≤ H') (hH' : 0 ≤ H')
    (hΛ1 : H' ≤ Λ) (hΛ2 : (H' + D) * (5 * β / (4 * a)) + β / 4 + D ≤ Λ)
    {p q : Space m} (hnear : 4 * dist p q < Metric.infDist p F₀) :
    ‖whitneyFilling P.toWhitneyWeights g p - whitneyFilling P.toWhitneyWeights g q‖ ≤
      2 * N * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * dist p q) := by
  classical
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  set h := dist p q with hh_def
  have hh : 0 ≤ h := dist_nonneg
  -- `p` and `q` lie off `F₀`
  have hpF : p ∉ F₀ := by
    intro hp
    rw [Metric.infDist_zero_of_mem hp] at hnear
    linarith
  obtain ⟨j, hj⟩ := W.exists_mem_cell hpF
  have hr := W.radius_pos j
  have hδp_up : Metric.infDist p F₀ ≤ β * W.radius j :=
    (P.infDist_le_of_mem_cell hj).trans (mul_le_mul_of_nonneg_right hβ hr.le)
  have hδp_lo : a * W.radius j ≤ Metric.infDist p F₀ := W.le_infDist j p hj
  have hδpq : Metric.infDist p F₀ ≤ Metric.infDist q F₀ + h := by
    have : Metric.infDist p F₀ ≤ Metric.infDist q F₀ + dist p q :=
      Metric.infDist_le_infDist_add_dist
    linarith
  have hδqp : Metric.infDist q F₀ ≤ Metric.infDist p F₀ + h := by
    have : Metric.infDist q F₀ ≤ Metric.infDist p F₀ + dist q p :=
      Metric.infDist_le_infDist_add_dist
    rw [dist_comm] at this
    linarith
  have hqF : q ∉ F₀ := by
    intro hq
    rw [Metric.infDist_zero_of_mem hq] at hδpq
    linarith
  obtain ⟨l, hl⟩ := W.exists_mem_cell hqF
  have hrl := W.radius_pos l
  have hδq_up : Metric.infDist q F₀ ≤ β * W.radius l :=
    (P.infDist_le_of_mem_cell hl).trans (mul_le_mul_of_nonneg_right hβ hrl.le)
  have hδq_lo : a * W.radius l ≤ Metric.infDist q F₀ := W.le_infDist l q hl
  have hhr : h ≤ β / 4 * W.radius j := by linarith
  -- comparability of the two cells
  have hrl_up : W.radius l ≤ 5 * β / (4 * a) * W.radius j := by
    rw [show 5 * β / (4 * a) * W.radius j = 5 * β * W.radius j / (4 * a) by ring,
      le_div_iff₀ (by linarith : (0 : ℝ) < 4 * a)]
    linarith
  have hrj_up : W.radius j ≤ 4 * β / (3 * a) * W.radius l := by
    rw [show 4 * β / (3 * a) * W.radius l = 4 * β * W.radius l / (3 * a) by ring,
      le_div_iff₀ (by linarith : (0 : ℝ) < 3 * a)]
    linarith
  -- per-index geometry
  have hidx : ∀ i, (P.weight i p ≠ 0 ∨ P.weight i q ≠ 0) →
      W.radius j ≤ μ * W.radius i ∧ dist (W.center i) (W.center j) ≤ Λ * W.radius j := by
    intro i hi
    rcases hi with hip | hiq
    · obtain ⟨-, h2⟩ := P.radius_comparable i j p hj hip
      refine ⟨h2.trans (mul_le_mul_of_nonneg_right hμ1 (W.radius_pos i).le), ?_⟩
      calc
        dist (W.center i) (W.center j) ≤ H * W.radius j := P.center_dist_le i j p hj hip
        _ ≤ H' * W.radius j := mul_le_mul_of_nonneg_right hH hr.le
        _ ≤ Λ * W.radius j := mul_le_mul_of_nonneg_right hΛ1 hr.le
    · obtain ⟨-, h2⟩ := P.radius_comparable i l q hl hiq
      have hri := W.radius_pos i
      refine ⟨?_, ?_⟩
      · calc
          W.radius j ≤ 4 * β / (3 * a) * W.radius l := hrj_up
          _ ≤ 4 * β / (3 * a) * (4 * W.radius i) :=
            mul_le_mul_of_nonneg_left h2 (div_nonneg (by linarith) (by linarith))
          _ = 16 * β / (3 * a) * W.radius i := by ring
          _ ≤ μ * W.radius i := mul_le_mul_of_nonneg_right hμ2 hri.le
      · have d1 : dist (W.center i) (W.center l) ≤ H * W.radius l :=
          P.center_dist_le i l q hl hiq
        have d2 : dist (W.center l) q ≤ D * W.radius l := by
          rw [dist_comm]
          exact W.dist_center_le hl
        have d3 : dist q p = h := dist_comm q p
        have d4 : dist p (W.center j) ≤ D * W.radius j := W.dist_center_le hj
        have d5 : H * W.radius l ≤ H' * W.radius l := mul_le_mul_of_nonneg_right hH hrl.le
        have d6 : (H' + D) * W.radius l ≤ (H' + D) * (5 * β / (4 * a) * W.radius j) :=
          mul_le_mul_of_nonneg_left hrl_up (by linarith)
        have d7 : ((H' + D) * (5 * β / (4 * a)) + β / 4 + D) * W.radius j ≤
            Λ * W.radius j := mul_le_mul_of_nonneg_right hΛ2 hr.le
        calc
          dist (W.center i) (W.center j) ≤
              dist (W.center i) (W.center l) + dist (W.center l) q + dist q p +
                dist p (W.center j) := by
            have e1 := dist_triangle (W.center i) (W.center l) (W.center j)
            have e2 := dist_triangle (W.center l) q (W.center j)
            have e3 := dist_triangle q p (W.center j)
            linarith
          _ ≤ Λ * W.radius j := by linarith
  -- finite sums over the active indices of `p` and `q`
  set S := P.activeFinset hpF ∪ P.activeFinset hqF with hS_def
  have hSp : ∀ i ∉ S, P.weight i p = 0 := fun i hi =>
    P.weight_eq_zero_of_notMem_activeFinset hpF fun h' => hi (Finset.mem_union_left _ h')
  have hSq : ∀ i ∉ S, P.weight i q = 0 := fun i hi =>
    P.weight_eq_zero_of_notMem_activeFinset hqF fun h' => hi (Finset.mem_union_right _ h')
  have h1p : ∑ i ∈ S, P.weight i p = 1 := P.sum_weight_eq_one hpF hSp
  have h1q : ∑ i ∈ S, P.weight i q = 1 := P.sum_weight_eq_one hqF hSq
  have hdiff : whitneyFilling P.toWhitneyWeights g p - whitneyFilling P.toWhitneyWeights g q =
      ∑ i ∈ S, (P.weight i p - P.weight i q) • (g (W.center i) - g (W.center j)) := by
    rw [whitneyFilling_eq_sum P.toWhitneyWeights g hpF hSp,
      whitneyFilling_eq_sum P.toWhitneyWeights g hqF hSq]
    have e : ∑ i ∈ S, (P.weight i p - P.weight i q) • g (W.center j) = 0 := by
      rw [← Finset.sum_smul, Finset.sum_sub_distrib, h1p, h1q, sub_self, zero_smul]
    calc
      ∑ i ∈ S, P.weight i p • g (W.center i) - ∑ i ∈ S, P.weight i q • g (W.center i) =
          ∑ i ∈ S, (P.weight i p - P.weight i q) • g (W.center i) -
            ∑ i ∈ S, (P.weight i p - P.weight i q) • g (W.center j) := by
        rw [e, sub_zero, ← Finset.sum_sub_distrib]
        simp only [sub_smul]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        simp only [smul_sub]
  have hcard : (S.card : ℝ) ≤ 2 * N := by
    have h1 := P.card_activeFinset_le hpF
    have h2 := P.card_activeFinset_le hqF
    have h3 : S.card ≤ (P.activeFinset hpF).card + (P.activeFinset hqF).card :=
      Finset.card_union_le _ _
    have : S.card ≤ 2 * N := by omega
    exact_mod_cast this
  have hterm : ∀ i ∈ S, ‖(P.weight i p - P.weight i q) • (g (W.center i) - g (W.center j))‖ ≤
      (K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * h := by
    intro i hiS
    have hact : P.weight i p ≠ 0 ∨ P.weight i q ≠ 0 := by
      rcases Finset.mem_union.mp hiS with hi | hi
      · exact Or.inl ((P.finite_active hpF).mem_toFinset.mp hi)
      · exact Or.inr ((P.finite_active hqF).mem_toFinset.mp hi)
    obtain ⟨hμi, hdi⟩ := hidx i hact
    have hri := W.radius_pos i
    have hw : |P.weight i p - P.weight i q| ≤
        K' / W.radius i * h + K' / W.radius i ^ 2 * h ^ 2 := by
      have hb := (P.derivBounds i).abs_sub_le p q
      have k1 : K / W.radius i ≤ K' / W.radius i := div_le_div_of_nonneg_right hK hri.le
      have k2 : K / W.radius i ^ 2 ≤ K' / W.radius i ^ 2 :=
        div_le_div_of_nonneg_right hK (by positivity)
      have n1 := norm_fst_sub_le_dist p q
      have n2 := abs_snd_sub_le_dist_sq p q
      have k1' : 0 ≤ K' / W.radius i := div_nonneg hK' hri.le
      have k2' : 0 ≤ K' / W.radius i ^ 2 := div_nonneg hK' (by positivity)
      calc
        |P.weight i p - P.weight i q| ≤
            K / W.radius i * ‖p.1 - q.1‖ + K / W.radius i ^ 2 * |p.2.val - q.2.val| := hb
        _ ≤ K' / W.radius i * ‖p.1 - q.1‖ + K' / W.radius i ^ 2 * |p.2.val - q.2.val| :=
          add_le_add (mul_le_mul_of_nonneg_right k1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right k2 (abs_nonneg _))
        _ ≤ K' / W.radius i * h + K' / W.radius i ^ 2 * h ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left n1 k1') (mul_le_mul_of_nonneg_left n2 k2')
    have he : ‖g (W.center i) - g (W.center j)‖ ≤ L * (Λ * W.radius j) := by
      rw [← dist_eq_norm]
      calc
        dist (g (W.center i)) (g (W.center j)) ≤ L * dist (W.center i) (W.center j) :=
          hg.dist_le_mul _ (W.center_mem_nodeSet i) _ (W.center_mem_nodeSet j)
        _ ≤ L * (Λ * W.radius j) := mul_le_mul_of_nonneg_left hdi hL
    rw [norm_smul, Real.norm_eq_abs]
    exact near_term_le hri hr hK' hμi hh hhr hw (norm_nonneg _) he
  rw [hdiff]
  calc
    ‖∑ i ∈ S, (P.weight i p - P.weight i q) • (g (W.center i) - g (W.center j))‖ ≤
        ∑ i ∈ S, ‖(P.weight i p - P.weight i q) • (g (W.center i) - g (W.center j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, (K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * h := Finset.sum_le_sum hterm
    _ = S.card * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * h) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * N * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * h) := by
      have h0 : 0 ≤ (K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * h := by
        have hμ0 : 0 ≤ μ := by linarith
        have hΛ0 : 0 ≤ Λ := by linarith
        have hA0 : 0 ≤ K' * μ + K' * μ ^ 2 * β / 4 :=
          add_nonneg (mul_nonneg hK' hμ0)
            (div_nonneg (mul_nonneg (mul_nonneg hK' (sq_nonneg μ)) hβ0) (by norm_num))
        exact mul_nonneg (mul_nonneg (mul_nonneg hA0 hΛ0) hL) hh
      exact mul_le_mul_of_nonneg_right hcard h0

/-- Far case of the Lipschitz estimate: if `δ(p) ≤ 4 d(p,q)` then
`‖F(p) - F(q)‖ ≤ 9 (1 + (H+D)/a) L d(p,q)`. -/
theorem norm_whitneyFilling_sub_le_far (hF₀ : IsClosed F₀) (hne : F₀.Nonempty) (hH : 0 ≤ H)
    (φ : WhitneyWeights W H) (g : Space m → Y) {L : ℝ≥0}
    (hg : LipschitzOnWith L g W.nodeSet) {p q : Space m}
    (hfar : Metric.infDist p F₀ ≤ 4 * dist p q) :
    ‖whitneyFilling φ g p - whitneyFilling φ g q‖ ≤ 9 * ((1 + (H + D) / a) * L * dist p q) := by
  obtain ⟨x, hx, hpx⟩ := hF₀.exists_infDist_eq_dist hne p
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hC : 0 ≤ (1 + (H + D) / a) * L := by
    have : 0 ≤ (H + D) / a := div_nonneg (by linarith) ha.le
    exact mul_nonneg (by linarith) (NNReal.coe_nonneg L)
  have h1 := norm_whitneyFilling_sub_le_dist hH φ g hg hx p
  have h2 := norm_whitneyFilling_sub_le_dist hH φ g hg hx q
  have h3 : dist q x ≤ dist p q + dist p x := by
    have := dist_triangle q p x
    rw [dist_comm q p] at this
    exact this
  have h4 : (1 + (H + D) / a) * L * dist q x ≤
      (1 + (H + D) / a) * L * (dist p q + dist p x) := mul_le_mul_of_nonneg_left h3 hC
  have h5 : (1 + (H + D) / a) * L * dist p x ≤ (1 + (H + D) / a) * L * (4 * dist p q) :=
    mul_le_mul_of_nonneg_left (by rw [← hpx]; exact hfar) hC
  calc
    ‖whitneyFilling φ g p - whitneyFilling φ g q‖ ≤
        ‖whitneyFilling φ g p - g x‖ + ‖whitneyFilling φ g q - g x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
      exact dist_triangle_right _ _ _
    _ ≤ (1 + (H + D) / a) * L * dist p x + (1 + (H + D) / a) * L * dist q x := add_le_add h1 h2
    _ ≤ 9 * ((1 + (H + D) / a) * L * dist p q) := by linarith

end Lipschitz

universe u v

/-- **Global Lipschitz bound:** the filling is globally parabolic `C L`-Lipschitz. -/
theorem whitneyFilling_lipschitz_proof (m : ℕ) (D a H b K : ℝ) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        LipschitzWith (C * L) (whitneyFilling P.toWhitneyWeights g) := by
  obtain ⟨H', hH'd⟩ : ∃ x : ℝ, x = max H 0 := ⟨_, rfl⟩
  obtain ⟨K', hK'd⟩ : ∃ x : ℝ, x = max K 0 := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ x : ℝ, x = max b 0 + D := ⟨_, rfl⟩
  obtain ⟨μ, hμd⟩ : ∃ x : ℝ, x = 4 + 16 * β / (3 * a) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = H' + (H' + D) * (5 * β / (4 * a)) + β / 4 + D := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ x : ℝ,
      x = 1 + 9 * (1 + (H' + D) / a) + 2 * N * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ) :=
    ⟨_, rfl⟩
  refine ⟨Real.toNNReal E, ?_⟩
  intro ι _ F₀ W hF₀ hne P Y _ _ g L hg
  have ha : 0 < a := W.a_pos
  have hD : 1 ≤ D := W.one_le_D
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hHH' : H ≤ H' := by rw [hH'd]; exact le_max_left _ _
  have hH' : 0 ≤ H' := by rw [hH'd]; exact le_max_right _ _
  have hKK' : K ≤ K' := by rw [hK'd]; exact le_max_left _ _
  have hK' : 0 ≤ K' := by rw [hK'd]; exact le_max_right _ _
  have hb1 : b ≤ max b 0 := le_max_left _ _
  have hb2 : 0 ≤ max b 0 := le_max_right _ _
  have hβ0 : 0 ≤ β := by rw [hβd]; linarith
  have hβ : b + D ≤ β := by rw [hβd]; linarith
  have h163 : 0 ≤ 16 * β / (3 * a) := div_nonneg (by linarith) (by linarith)
  have hμ1 : 4 ≤ μ := by rw [hμd]; linarith
  have hμ2 : 16 * β / (3 * a) ≤ μ := by rw [hμd]; linarith
  have hμ0 : 0 ≤ μ := by linarith
  have h54 : 0 ≤ 5 * β / (4 * a) := div_nonneg (by linarith) (by linarith)
  have hΛ0 : 0 ≤ (H' + D) * (5 * β / (4 * a)) := mul_nonneg (by linarith) h54
  have hΛ1 : H' ≤ Λ := by rw [hΛd]; linarith
  have hΛ2 : (H' + D) * (5 * β / (4 * a)) + β / 4 + D ≤ Λ := by rw [hΛd]; linarith
  have hΛpos : 0 ≤ Λ := by linarith
  have hC1 : 0 ≤ (H' + D) / a := div_nonneg (by linarith) ha.le
  have hA0 : 0 ≤ K' * μ + K' * μ ^ 2 * β / 4 :=
    add_nonneg (mul_nonneg hK' hμ0)
      (div_nonneg (mul_nonneg (mul_nonneg hK' (sq_nonneg μ)) hβ0) (by norm_num))
  have hnear0 : 0 ≤ 2 * N * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N)) (mul_nonneg hA0 hΛpos)
  have h9 : 0 ≤ 9 * (1 + (H' + D) / a) := by linarith
  have hE1 : 9 * (1 + (H' + D) / a) ≤ E := by rw [hEd]; linarith
  have hE2 : 2 * N * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ) ≤ E := by rw [hEd]; linarith
  have hE3 : 1 ≤ E := by rw [hEd]; linarith
  have hE : (Real.toNNReal E : ℝ) = E := Real.coe_toNNReal _ (by linarith)
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [NNReal.coe_mul, hE, dist_eq_norm]
  have hd : 0 ≤ dist p q := dist_nonneg
  by_cases hH0 : 0 ≤ H
  · by_cases hfar : Metric.infDist p F₀ ≤ 4 * dist p q
    · have h := norm_whitneyFilling_sub_le_far hF₀ hne hH0 P.toWhitneyWeights g hg hfar
      have hmono : (1 + (H + D) / a) ≤ 1 + (H' + D) / a := by
        have : (H + D) / a ≤ (H' + D) / a := div_le_div_of_nonneg_right (by linarith) ha.le
        linarith
      have hLd : 0 ≤ (L : ℝ) * dist p q := mul_nonneg hL hd
      calc
        _ ≤ 9 * ((1 + (H + D) / a) * L * dist p q) := h
        _ = 9 * (1 + (H + D) / a) * (L * dist p q) := by ring
        _ ≤ 9 * (1 + (H' + D) / a) * (L * dist p q) :=
          mul_le_mul_of_nonneg_right (by linarith) hLd
        _ ≤ E * (L * dist p q) := mul_le_mul_of_nonneg_right hE1 hLd
        _ = E * L * dist p q := by ring
    · have hLd : 0 ≤ (L : ℝ) * dist p q := mul_nonneg hL hd
      have h := P.norm_whitneyFilling_sub_le_near g hg hKK' hK' hβ hβ0 hμ1 hμ2
        hHH' hH' hΛ1 hΛ2 (not_le.mp hfar)
      calc
        _ ≤ 2 * N * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ * L * dist p q) := h
        _ = 2 * N * ((K' * μ + K' * μ ^ 2 * β / 4) * Λ) * (L * dist p q) := by ring
        _ ≤ E * (L * dist p q) := mul_le_mul_of_nonneg_right hE2 hLd
        _ = E * L * dist p q := by ring
  · -- no point lies off `F₀`, so the filling is `g`
    have hall : ∀ x, x ∈ F₀ := fun x => by
      by_contra hx
      exact hH0 (P.toWhitneyWeights.nonneg_of_notMem hx)
    rw [whitneyFilling_of_mem _ g (hall p), whitneyFilling_of_mem _ g (hall q), ← dist_eq_norm]
    calc
      dist (g p) (g q) ≤ L * dist p q :=
        hg.dist_le_mul _ (W.mem_nodeSet_of_mem (hall p)) _ (W.mem_nodeSet_of_mem (hall q))
      _ = 1 * (L * dist p q) := by ring
      _ ≤ E * (L * dist p q) := mul_le_mul_of_nonneg_right hE3 (mul_nonneg hL hd)
      _ = E * L * dist p q := by ring

end ParabolicRectifiability
