import ParabolicRectifiability.Analysis.TraceExtension.Whitney.FillingSmooth
import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Lipschitz

/-! # Quantitative derivative bounds for the Whitney filling

Fix `q ∉ F₀` in the cell `Q_j`; put
`δ = d_P(q,F₀) ≤ (b+D) r_j`. Near `q`, every weight active at a point `x` with
`4 d_P(q,x) < δ` has comparable radius `r_j ≤ μ r_i` and a center within `Λ r_j` of
`p_j` (`near_index_bounds`); at most `N` weights are active at any point.

* *First spatial derivative and time derivative at `q`.* By cancellation,
  `D F(q) = Σ_i D φ_i(q) (g(p_i) - g(p_j))`. A weight vanishing at `q` has zero first
  derivatives there (Fermat). The active ones give `|∇_u F| ≲ K L` and
  `|∂_t F| ≲ K L / r_j`.
* *Second spatial derivative.* The shortcut `φ_i(q) = 0 ⇒ D²φ_i(q) = 0` is false in
  general, so it is not used. Instead, for `x` near `q.1` at the same time,
  `DF(x) - DF(q) = Σ_i (Dφ_i(x) - Dφ_i(q)) (g(p_i) - g(p_j))`. Only weights active at
  `x` or at `q` contribute (Fermat at both points), at most `2N` of them, and each
  contributes `≤ (K/r_i²) |x - q.1| · L Λ r_j` by the mean value inequality for `Dφ_i`.
  So `DF` is `C L / r_j`-Lipschitz near `q.1`, and therefore `|D² F(q)| ≤ C L / r_j`.
  This uses only points where at most `2N` weights are active, together with a limiting
  step (here the derivative as a limit of difference quotients of `DF`). It never
  evaluates a second derivative of an inactive weight.

Finally `1/r_j ≤ (b+D)/δ` turns inverse radii into inverse distance.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

section RealBounds

/-- One active index, first order: `|Δ| ≤ (K'/r_i) X`, `e ≤ L Λ r_j`, `r_j ≤ μ r_i`. -/
theorem term_le_first {Δ e K' μ Λ L X r ri : ℝ} (hri : 0 < ri) (hK' : 0 ≤ K')
    (hμ : r ≤ μ * ri) (hX : 0 ≤ X) (hL : 0 ≤ L) (hΛ : 0 ≤ Λ)
    (hw : |Δ| ≤ K' / ri * X) (he0 : 0 ≤ e) (he : e ≤ L * (Λ * r)) :
    |Δ| * e ≤ K' * μ * Λ * L * X := by
  have hratio : r / ri ≤ μ := by
    rw [div_le_iff₀ hri]
    linarith
  have h0 : 0 ≤ K' / ri * X := mul_nonneg (div_nonneg hK' hri.le) hX
  calc
    |Δ| * e ≤ (K' / ri * X) * (L * (Λ * r)) := mul_le_mul hw he he0 h0
    _ = K' * X * L * Λ * (r / ri) := by ring
    _ ≤ K' * X * L * Λ * μ :=
      mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (mul_nonneg (mul_nonneg hK' hX) hL) hΛ)
    _ = K' * μ * Λ * L * X := by ring

/-- One active index, second order: `|Δ| ≤ (K'/r_i²) X`, `e ≤ L Λ r_j`, `r_j ≤ μ r_i`. -/
theorem term_le_second {Δ e K' μ Λ L X r ri : ℝ} (hri : 0 < ri) (hr : 0 < r) (hK' : 0 ≤ K')
    (hμ : r ≤ μ * ri) (hX : 0 ≤ X) (hL : 0 ≤ L) (hΛ : 0 ≤ Λ)
    (hw : |Δ| ≤ K' / ri ^ 2 * X) (he0 : 0 ≤ e) (he : e ≤ L * (Λ * r)) :
    |Δ| * e ≤ K' * μ ^ 2 * Λ * L * X / r := by
  have hratio : r / ri ≤ μ := by
    rw [div_le_iff₀ hri]
    linarith
  have h0 : 0 ≤ K' / ri ^ 2 * X := mul_nonneg (div_nonneg hK' (by positivity)) hX
  rw [le_div_iff₀ hr]
  calc
    |Δ| * e * r ≤ (K' / ri ^ 2 * X) * (L * (Λ * r)) * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul hw he he0 h0) hr.le
    _ = K' * X * L * Λ * (r / ri) ^ 2 := by ring
    _ ≤ K' * X * L * Λ * μ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hr.le hri.le) hratio 2)
        (mul_nonneg (mul_nonneg (mul_nonneg hK' hX) hL) hΛ)
    _ = K' * μ ^ 2 * Λ * L * X := by ring

end RealBounds

section Bounds

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H b K : ℝ} {N : ℕ}
  {W : WhitneyData m ι F₀ D a}

/-- Geometry of the weights active near a point: if `p ∈ Q_j`, `4 d(p,q) < δ(p)` and the
weight `i` is active at `p` or at `q`, then `r_j ≤ μ r_i` and `d(p_i,p_j) ≤ Λ r_j`, for
any constants dominating the geometric ones. -/
theorem WhitneyPartition.near_index_bounds (P : WhitneyPartition W H b K N)
    {β μ Λ H' : ℝ} (hβ : b + D ≤ β) (hμ1 : 4 ≤ μ) (hμ2 : 16 * β / (3 * a) ≤ μ)
    (hH : H ≤ H') (hΛ1 : H' ≤ Λ) (hΛ2 : (H' + D) * (5 * β / (4 * a)) + β / 4 + D ≤ Λ)
    {p q : Space m} {j : ι} (hj : p ∈ W.cell j) (hnear : 4 * dist p q < Metric.infDist p F₀)
    {i : ι} (hi : P.weight i p ≠ 0 ∨ P.weight i q ≠ 0) :
    W.radius j ≤ μ * W.radius i ∧ dist (W.center i) (W.center j) ≤ Λ * W.radius j := by
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hh : 0 ≤ dist p q := dist_nonneg
  have hr := W.radius_pos j
  have hδp_up : Metric.infDist p F₀ ≤ β * W.radius j :=
    (P.infDist_le_of_mem_cell hj).trans (mul_le_mul_of_nonneg_right hβ hr.le)
  have hδp_lo : a * W.radius j ≤ Metric.infDist p F₀ := W.le_infDist j p hj
  have hδpq : Metric.infDist p F₀ ≤ Metric.infDist q F₀ + dist p q :=
    Metric.infDist_le_infDist_add_dist
  have hδqp : Metric.infDist q F₀ ≤ Metric.infDist p F₀ + dist p q := by
    have : Metric.infDist q F₀ ≤ Metric.infDist p F₀ + dist q p :=
      Metric.infDist_le_infDist_add_dist
    rwa [dist_comm] at this
  have hqF : q ∉ F₀ := by
    intro hq
    rw [Metric.infDist_zero_of_mem hq] at hδpq
    linarith
  obtain ⟨l, hl⟩ := W.exists_mem_cell hqF
  have hrl := W.radius_pos l
  have hδq_up : Metric.infDist q F₀ ≤ β * W.radius l :=
    (P.infDist_le_of_mem_cell hl).trans (mul_le_mul_of_nonneg_right hβ hrl.le)
  have hδq_lo : a * W.radius l ≤ Metric.infDist q F₀ := W.le_infDist l q hl
  have hβ0 : 0 ≤ β := by
    have : 0 < β * W.radius j := lt_of_lt_of_le (by linarith) hδp_up
    exact (pos_of_mul_pos_left this hr.le).le
  have hhr : dist p q ≤ β / 4 * W.radius j := by linarith
  have hrl_up : W.radius l ≤ 5 * β / (4 * a) * W.radius j := by
    rw [show 5 * β / (4 * a) * W.radius j = 5 * β * W.radius j / (4 * a) by ring,
      le_div_iff₀ (by linarith : (0 : ℝ) < 4 * a)]
    linarith
  have hrj_up : W.radius j ≤ 4 * β / (3 * a) * W.radius l := by
    rw [show 4 * β / (3 * a) * W.radius l = 4 * β * W.radius l / (3 * a) by ring,
      le_div_iff₀ (by linarith : (0 : ℝ) < 3 * a)]
    linarith
  have hH' : 0 ≤ H' + D := by
    rcases hi with hip | hiq
    · have := P.center_dist_le i j p hj hip
      have : 0 ≤ H * W.radius j := dist_nonneg.trans this
      have : 0 ≤ H := (mul_nonneg_iff_of_pos_right hr).mp this
      linarith
    · have := P.center_dist_le i l q hl hiq
      have : 0 ≤ H * W.radius l := dist_nonneg.trans this
      have : 0 ≤ H := (mul_nonneg_iff_of_pos_right hrl).mp this
      linarith
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
      have d3 : dist q p = dist p q := dist_comm q p
      have d4 : dist p (W.center j) ≤ D * W.radius j := W.dist_center_le hj
      have d5 : H * W.radius l ≤ H' * W.radius l := mul_le_mul_of_nonneg_right hH hrl.le
      have d6 : (H' + D) * W.radius l ≤ (H' + D) * (5 * β / (4 * a) * W.radius j) :=
        mul_le_mul_of_nonneg_left hrl_up hH'
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

/-- Counting: a sum whose terms vanish unless the index is active at `x` or at `y`, and
are at most `c` otherwise, is at most `2 N c`. -/
theorem WhitneyPartition.sum_le_two_mul (P : WhitneyPartition W H b K N) {x y : Space m}
    (hx : x ∉ F₀) (hy : y ∉ F₀) (S : Finset ι) {f : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf0 : ∀ i ∈ S, P.weight i x = 0 → P.weight i y = 0 → f i = 0)
    (hfc : ∀ i ∈ S, (P.weight i x ≠ 0 ∨ P.weight i y ≠ 0) → f i ≤ c) :
    ∑ i ∈ S, f i ≤ 2 * N * c := by
  classical
  have hfilter : ∑ i ∈ S.filter (fun i => P.weight i x ≠ 0 ∨ P.weight i y ≠ 0), f i =
      ∑ i ∈ S, f i := by
    refine Finset.sum_filter_of_ne fun i hi hne => ?_
    by_contra hcon
    exact hne (hf0 i hi (not_not.mp fun h => hcon (Or.inl h))
      (not_not.mp fun h => hcon (Or.inr h)))
  have hsub : S.filter (fun i => P.weight i x ≠ 0 ∨ P.weight i y ≠ 0) ⊆
      P.activeFinset hx ∪ P.activeFinset hy := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with h | h
    · exact Finset.mem_union_left _ ((P.finite_active hx).mem_toFinset.mpr h)
    · exact Finset.mem_union_right _ ((P.finite_active hy).mem_toFinset.mpr h)
  have hcard : ((S.filter (fun i => P.weight i x ≠ 0 ∨ P.weight i y ≠ 0)).card : ℝ) ≤
      2 * N := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (P.activeFinset hx) (P.activeFinset hy)
    have h3 := P.card_activeFinset_le hx
    have h4 := P.card_activeFinset_le hy
    have : (S.filter (fun i => P.weight i x ≠ 0 ∨ P.weight i y ≠ 0)).card ≤ 2 * N := by
      omega
    exact_mod_cast this
  rw [← hfilter]
  calc
    ∑ i ∈ S.filter (fun i => P.weight i x ≠ 0 ∨ P.weight i y ≠ 0), f i ≤
        (S.filter (fun i => P.weight i x ≠ 0 ∨ P.weight i y ≠ 0)).card • c :=
      Finset.sum_le_card_nsmul _ _ _ fun i hi =>
        hfc i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
    _ = ((S.filter (fun i => P.weight i x ≠ 0 ∨ P.weight i y ≠ 0)).card : ℝ) * c :=
      nsmul_eq_mul _ _
    _ ≤ 2 * N * c := mul_le_mul_of_nonneg_right hcard hc

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- First spatial derivative bound at `q ∉ F₀`: `|∇_u F(q)| ≤ 2N K'μΛ L`. -/
theorem WhitneyPartition.norm_fderiv_spaceSlice_filling_le (P : WhitneyPartition W H b K N)
    (g : Space m → Y) {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) (hF₀ : IsClosed F₀)
    (hne : F₀.Nonempty) {K' β μ Λ H' : ℝ} (hK : K ≤ K') (hK' : 0 ≤ K') (hβ : b + D ≤ β)
    (hμ1 : 4 ≤ μ) (hμ2 : 16 * β / (3 * a) ≤ μ) (hH : H ≤ H') (hΛ0 : 0 ≤ Λ)
    (hΛ1 : H' ≤ Λ) (hΛ2 : (H' + D) * (5 * β / (4 * a)) + β / 4 + D ≤ Λ)
    {q : Space m} (hq : q ∉ F₀) :
    ‖fderiv ℝ (fun v => whitneyFilling P.toWhitneyWeights g (point v q.2.val)) q.1‖ ≤
      2 * N * (K' * μ * Λ * L) := by
  classical
  obtain ⟨j, hj⟩ := W.exists_mem_cell hq
  obtain ⟨U, hU, hqU, hUF, S, hS⟩ := P.toWhitneyWeights.exists_open_finset hF₀ hq
  have hδ : 0 < Metric.infDist q F₀ := (hF₀.notMem_iff_infDist_pos hne).mp hq
  have hqU' : point q.1 q.2.val ∈ U := hqU
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hμ0 : 0 ≤ μ := by linarith
  have hc0 : 0 ≤ 2 * N * (K' * μ * Λ * L) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
      (mul_nonneg (mul_nonneg (mul_nonneg hK' hμ0) hΛ0) hL)
  refine ContinuousLinearMap.opNorm_le_bound _ hc0 fun h => ?_
  rw [P.fderiv_spaceSlice_filling_apply g hU hUF hS hqU' (g (W.center j)) h]
  have hnear : 4 * dist q q < Metric.infDist q F₀ := by
    rw [dist_self, mul_zero]
    exact hδ
  calc
    ‖∑ i ∈ S, fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1 h •
        (g (W.center i) - g (W.center j))‖ ≤
        ∑ i ∈ S, |fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1 h| *
          ‖g (W.center i) - g (W.center j)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * N * (K' * μ * Λ * L * ‖h‖) := by
      refine P.sum_le_two_mul hq hq S
        (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK' hμ0) hΛ0) hL) (norm_nonneg h))
        (fun i _ h0 _ => ?_) (fun i _ hact => ?_)
      · have h0' : P.weight i (point q.1 q.2.val) = 0 := h0
        rw [P.toWhitneyWeights.fderiv_spaceSlice_eq_zero h0']
        simp
      · have hact' : P.weight i q ≠ 0 ∨ P.weight i q ≠ 0 := hact
        obtain ⟨hμi, hdi⟩ := P.near_index_bounds hβ hμ1 hμ2 hH hΛ1 hΛ2 hj hnear hact'
        have hri := W.radius_pos i
        have hw : |fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1 h| ≤
            K' / W.radius i * ‖h‖ := by
          rw [← Real.norm_eq_abs]
          calc
            ‖fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1 h‖ ≤
                ‖fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1‖ * ‖h‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ K / W.radius i * ‖h‖ :=
              mul_le_mul_of_nonneg_right ((P.derivBounds i).spatial_le q.1 q.2.val)
                (norm_nonneg h)
            _ ≤ K' / W.radius i * ‖h‖ :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK hri.le) (norm_nonneg h)
        have he : ‖g (W.center i) - g (W.center j)‖ ≤ L * (Λ * W.radius j) := by
          rw [← dist_eq_norm]
          calc
            dist (g (W.center i)) (g (W.center j)) ≤ L * dist (W.center i) (W.center j) :=
              hg.dist_le_mul _ (W.center_mem_nodeSet i) _ (W.center_mem_nodeSet j)
            _ ≤ L * (Λ * W.radius j) := mul_le_mul_of_nonneg_left hdi hL
        exact term_le_first hri hK' hμi (norm_nonneg h) hL hΛ0 hw (norm_nonneg _) he
    _ = 2 * N * (K' * μ * Λ * L) * ‖h‖ := by ring

/-- Time derivative bound at `q ∈ Q_j`, `q ∉ F₀`: `|∂_t F(q)| ≤ 2N K'μ²Λ L / r_j`. -/
theorem WhitneyPartition.norm_deriv_timeSlice_filling_le (P : WhitneyPartition W H b K N)
    (g : Space m → Y) {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) (hF₀ : IsClosed F₀)
    (hne : F₀.Nonempty) {K' β μ Λ H' : ℝ} (hK : K ≤ K') (hK' : 0 ≤ K') (hβ : b + D ≤ β)
    (hμ1 : 4 ≤ μ) (hμ2 : 16 * β / (3 * a) ≤ μ) (hH : H ≤ H') (hΛ0 : 0 ≤ Λ)
    (hΛ1 : H' ≤ Λ) (hΛ2 : (H' + D) * (5 * β / (4 * a)) + β / 4 + D ≤ Λ)
    {q : Space m} (hq : q ∉ F₀) {j : ι} (hj : q ∈ W.cell j) :
    ‖deriv (fun t => whitneyFilling P.toWhitneyWeights g (point q.1 t)) q.2.val‖ ≤
      2 * N * (K' * μ ^ 2 * Λ * L * 1 / W.radius j) := by
  classical
  obtain ⟨U, hU, hqU, hUF, S, hS⟩ := P.toWhitneyWeights.exists_open_finset hF₀ hq
  have hδ : 0 < Metric.infDist q F₀ := (hF₀.notMem_iff_infDist_pos hne).mp hq
  have hqU' : point q.1 q.2.val ∈ U := hqU
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hμ0 : 0 ≤ μ := by linarith
  have hr := W.radius_pos j
  have hnear : 4 * dist q q < Metric.infDist q F₀ := by
    rw [dist_self, mul_zero]
    exact hδ
  rw [P.deriv_timeSlice_filling g hU hUF hS hqU' (g (W.center j))]
  calc
    ‖∑ i ∈ S, deriv (fun s => P.weight i (point q.1 s)) q.2.val •
        (g (W.center i) - g (W.center j))‖ ≤
        ∑ i ∈ S, |deriv (fun s => P.weight i (point q.1 s)) q.2.val| *
          ‖g (W.center i) - g (W.center j)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * N * (K' * μ ^ 2 * Λ * L * 1 / W.radius j) := by
      refine P.sum_le_two_mul hq hq S
        (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK' (sq_nonneg μ)) hΛ0) hL)
          zero_le_one) hr.le)
        (fun i _ h0 _ => ?_) (fun i _ hact => ?_)
      · have h0' : P.weight i (point q.1 q.2.val) = 0 := h0
        rw [P.toWhitneyWeights.deriv_timeSlice_eq_zero h0']
        simp
      · have hact' : P.weight i q ≠ 0 ∨ P.weight i q ≠ 0 := hact
        obtain ⟨hμi, hdi⟩ := P.near_index_bounds hβ hμ1 hμ2 hH hΛ1 hΛ2 hj hnear hact'
        have hri := W.radius_pos i
        have hw : |deriv (fun s => P.weight i (point q.1 s)) q.2.val| ≤
            K' / W.radius i ^ 2 * 1 := by
          rw [mul_one]
          exact ((P.derivBounds i).time_le q.1 q.2.val).trans
            (div_le_div_of_nonneg_right hK (by positivity))
        have he : ‖g (W.center i) - g (W.center j)‖ ≤ L * (Λ * W.radius j) := by
          rw [← dist_eq_norm]
          calc
            dist (g (W.center i)) (g (W.center j)) ≤ L * dist (W.center i) (W.center j) :=
              hg.dist_le_mul _ (W.center_mem_nodeSet i) _ (W.center_mem_nodeSet j)
            _ ≤ L * (Λ * W.radius j) := mul_le_mul_of_nonneg_left hdi hL
        exact term_le_second hri hr hK' hμi zero_le_one hL hΛ0 hw (norm_nonneg _) he

/-- Second spatial derivative bound at `q ∈ Q_j`, `q ∉ F₀`:
`|∇²_u F(q)| ≤ 2N K'μ²Λ L / r_j`, via the local Lipschitz bound of `∇_u F`. -/
theorem WhitneyPartition.norm_fderiv_fderiv_spaceSlice_filling_le
    (P : WhitneyPartition W H b K N) (g : Space m → Y) {L : ℝ≥0}
    (hg : LipschitzOnWith L g W.nodeSet) (hF₀ : IsClosed F₀) (hne : F₀.Nonempty)
    {K' β μ Λ H' : ℝ} (hK : K ≤ K') (hK' : 0 ≤ K') (hβ : b + D ≤ β)
    (hμ1 : 4 ≤ μ) (hμ2 : 16 * β / (3 * a) ≤ μ) (hH : H ≤ H') (hΛ0 : 0 ≤ Λ)
    (hΛ1 : H' ≤ Λ) (hΛ2 : (H' + D) * (5 * β / (4 * a)) + β / 4 + D ≤ Λ)
    {q : Space m} (hq : q ∉ F₀) {j : ι} (hj : q ∈ W.cell j) :
    ‖fderiv ℝ (fun v => fderiv ℝ
        (fun w => whitneyFilling P.toWhitneyWeights g (point w q.2.val)) v) q.1‖ ≤
      2 * N * (K' * μ ^ 2 * Λ * L) / W.radius j := by
  classical
  obtain ⟨U, hU, hqU, hUF, S, hS⟩ := P.toWhitneyWeights.exists_open_finset hF₀ hq
  have hδ : 0 < Metric.infDist q F₀ := (hF₀.notMem_iff_infDist_pos hne).mp hq
  have hqU' : point q.1 q.2.val ∈ U := hqU
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hμ0 : 0 ≤ μ := by linarith
  have hr := W.radius_pos j
  have hM0 : 0 ≤ 2 * N * (K' * μ ^ 2 * Λ * L) / W.radius j :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
      (mul_nonneg (mul_nonneg (mul_nonneg hK' (sq_nonneg μ)) hΛ0) hL)) hr.le
  have hdiff := (P.differentiableAt_fderiv_spaceSlice_filling g hU hUF hS hqU').hasFDerivAt
  refine hdiff.le_of_lip' hM0 ?_
  have hV : IsOpen {v : Spatial m | point v q.2.val ∈ U} :=
    hU.preimage (continuous_point_left q.2.val)
  filter_upwards [hV.mem_nhds hqU', Metric.ball_mem_nhds q.1 (by linarith : (0 : ℝ) <
    Metric.infDist q F₀ / 4)] with x hxU hxb
  have hxU' : point x q.2.val ∈ U := hxU
  have hxF : point x q.2.val ∉ F₀ := hUF hxU'
  have hxq : 4 * dist q (point x q.2.val) < Metric.infDist q F₀ := by
    have h1 : dist q (point x q.2.val) = ‖q.1 - x‖ := dist_point_same_time q.1 x q.2.val
    have h2 : ‖q.1 - x‖ < Metric.infDist q F₀ / 4 := by
      rw [← dist_eq_norm, dist_comm]
      exact Metric.mem_ball.mp hxb
    rw [h1]
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hM0 (norm_nonneg _)) fun h => ?_
  rw [sub_apply,
    P.fderiv_spaceSlice_filling_apply g hU hUF hS hxU' (g (W.center j)) h,
    P.fderiv_spaceSlice_filling_apply g hU hUF hS hqU' (g (W.center j)) h,
    ← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ S, (fderiv ℝ (fun w => P.weight i (point w q.2.val)) x h •
          (g (W.center i) - g (W.center j)) -
        fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1 h •
          (g (W.center i) - g (W.center j)))‖ ≤
        ∑ i ∈ S, |fderiv ℝ (fun w => P.weight i (point w q.2.val)) x h -
            fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1 h| *
          ‖g (W.center i) - g (W.center j)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * N * (K' * μ ^ 2 * Λ * L * (‖x - q.1‖ * ‖h‖) / W.radius j) := by
      refine P.sum_le_two_mul hxF hq S
        (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK' (sq_nonneg μ)) hΛ0)
          hL) (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hr.le)
        (fun i _ h0x h0q => ?_) (fun i _ hact => ?_)
      · have h0q' : P.weight i (point q.1 q.2.val) = 0 := h0q
        rw [P.toWhitneyWeights.fderiv_spaceSlice_eq_zero h0x,
          P.toWhitneyWeights.fderiv_spaceSlice_eq_zero h0q']
        simp
      · obtain ⟨hμi, hdi⟩ := P.near_index_bounds hβ hμ1 hμ2 hH hΛ1 hΛ2 hj hxq hact.symm
        have hri := W.radius_pos i
        have hmvt : ‖fderiv ℝ (fun w => P.weight i (point w q.2.val)) x -
            fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1‖ ≤
            K / W.radius i ^ 2 * ‖x - q.1‖ := by
          have hd2 := (((P.derivBounds i).contDiff_spaceSlice q.2.val).fderiv_right
            one_add_one_eq_two.le).differentiable one_ne_zero
          exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
            (f := fun v => fderiv ℝ (fun w => P.weight i (point w q.2.val)) v)
            (fun v _ => hd2 v) (fun v _ => (P.derivBounds i).spatial₂_le v q.2.val)
            (mem_univ q.1) (mem_univ x)
        have hw : |fderiv ℝ (fun w => P.weight i (point w q.2.val)) x h -
            fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1 h| ≤
            K' / W.radius i ^ 2 * (‖x - q.1‖ * ‖h‖) := by
          rw [← sub_apply, ← Real.norm_eq_abs]
          calc
            ‖(fderiv ℝ (fun w => P.weight i (point w q.2.val)) x -
                fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1) h‖ ≤
                ‖fderiv ℝ (fun w => P.weight i (point w q.2.val)) x -
                  fderiv ℝ (fun w => P.weight i (point w q.2.val)) q.1‖ * ‖h‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ K / W.radius i ^ 2 * ‖x - q.1‖ * ‖h‖ :=
              mul_le_mul_of_nonneg_right hmvt (norm_nonneg h)
            _ ≤ K' / W.radius i ^ 2 * ‖x - q.1‖ * ‖h‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right hK (by positivity)) (norm_nonneg _))
                (norm_nonneg h)
            _ = K' / W.radius i ^ 2 * (‖x - q.1‖ * ‖h‖) := by ring
        have he : ‖g (W.center i) - g (W.center j)‖ ≤ L * (Λ * W.radius j) := by
          rw [← dist_eq_norm]
          calc
            dist (g (W.center i)) (g (W.center j)) ≤ L * dist (W.center i) (W.center j) :=
              hg.dist_le_mul _ (W.center_mem_nodeSet i) _ (W.center_mem_nodeSet j)
            _ ≤ L * (Λ * W.radius j) := mul_le_mul_of_nonneg_left hdi hL
        exact term_le_second hri hr hK' hμi (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hL hΛ0
          hw (norm_nonneg _) he
    _ = 2 * N * (K' * μ ^ 2 * Λ * L) / W.radius j * ‖x - q.1‖ * ‖h‖ := by ring

end Bounds

universe u v

/-- **Derivative bounds for the Whitney filling:** off `F₀` the filling of a
smooth Whitney partition is `C²` in ordinary coordinates, with `|∇_u F| ≤ C L` and
`|∇_u² F| + |∂_t F| ≤ C L / dist(q, F₀)`. -/
theorem whitneyFilling_deriv_bounds_proof (m : ℕ) (D a H b K : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a), IsClosed F₀ → F₀.Nonempty →
      ∀ (P : WhitneyPartition W H b K N) {Y : Type v} [NormedAddCommGroup Y]
        [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0), LipschitzOnWith L g W.nodeSet →
        ContDiffOn ℝ 2 (fun y : Coordinates m => whitneyFilling P.toWhitneyWeights g (point y.1 y.2))
            {y | point y.1 y.2 ∉ F₀} ∧
          ∀ q ∉ F₀,
            ‖fderiv ℝ (fun v => whitneyFilling P.toWhitneyWeights g (point v q.2.val)) q.1‖ ≤
                C * L ∧
              ‖fderiv ℝ (fun v => fderiv ℝ
                  (fun w => whitneyFilling P.toWhitneyWeights g (point w q.2.val)) v) q.1‖ ≤
                C * L / Metric.infDist q F₀ ∧
              ‖deriv (fun t => whitneyFilling P.toWhitneyWeights g (point q.1 t)) q.2.val‖ ≤
                C * L / Metric.infDist q F₀ := by
  obtain ⟨H', hH'd⟩ : ∃ x : ℝ, x = max H 0 := ⟨_, rfl⟩
  obtain ⟨K', hK'd⟩ : ∃ x : ℝ, x = max K 0 := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ x : ℝ, x = max b 0 + D := ⟨_, rfl⟩
  obtain ⟨μ, hμd⟩ : ∃ x : ℝ, x = 4 + 16 * β / (3 * a) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = H' + (H' + D) * (5 * β / (4 * a)) + β / 4 + D := ⟨_, rfl⟩
  have hH' : 0 ≤ H' := by rw [hH'd]; exact le_max_right _ _
  have hK' : 0 ≤ K' := by rw [hK'd]; exact le_max_right _ _
  obtain ⟨C, hCd⟩ : ∃ x : ℝ, x = 2 * N * (K' * μ * Λ) + 2 * N * (K' * μ ^ 2 * Λ) * β :=
    ⟨_, rfl⟩
  by_cases hpar : 1 ≤ D ∧ 0 < a
  swap
  · refine ⟨0, le_rfl, fun W => absurd ⟨W.one_le_D, W.a_pos⟩ hpar⟩
  obtain ⟨hD, ha⟩ := hpar
  have hb1 : b ≤ max b 0 := le_max_left _ _
  have hb2 : 0 ≤ max b 0 := le_max_right _ _
  have hβ0 : 0 ≤ β := by rw [hβd]; linarith
  have hβ : b + D ≤ β := by rw [hβd]; linarith
  have hμ1 : 4 ≤ μ := by
    have : 0 ≤ 16 * β / (3 * a) := div_nonneg (by linarith) (by linarith)
    rw [hμd]
    linarith
  have hμ2 : 16 * β / (3 * a) ≤ μ := by rw [hμd]; linarith
  have hμ0 : 0 ≤ μ := by linarith
  have h54 : 0 ≤ (H' + D) * (5 * β / (4 * a)) :=
    mul_nonneg (by linarith) (div_nonneg (by linarith) (by linarith))
  have hΛ1 : H' ≤ Λ := by rw [hΛd]; linarith
  have hΛ2 : (H' + D) * (5 * β / (4 * a)) + β / 4 + D ≤ Λ := by rw [hΛd]; linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hHH' : H ≤ H' := by rw [hH'd]; exact le_max_left _ _
  have hKK' : K ≤ K' := by rw [hK'd]; exact le_max_left _ _
  have hA : 0 ≤ 2 * N * (K' * μ * Λ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
      (mul_nonneg (mul_nonneg hK' hμ0) hΛ0)
  have hB : 0 ≤ 2 * N * (K' * μ ^ 2 * Λ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
      (mul_nonneg (mul_nonneg hK' (sq_nonneg μ)) hΛ0)
  have hC0 : 0 ≤ C := by rw [hCd]; exact add_nonneg hA (mul_nonneg hB hβ0)
  refine ⟨C, hC0, ?_⟩
  intro ι _ F₀ W hF₀ hne P Y _ _ g L hg
  refine ⟨P.contDiffOn_whitneyFilling g hF₀, fun q hq => ?_⟩
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  obtain ⟨j, hj⟩ := W.exists_mem_cell hq
  have hr := W.radius_pos j
  have hδ : 0 < Metric.infDist q F₀ := (hF₀.notMem_iff_infDist_pos hne).mp hq
  have hδr : Metric.infDist q F₀ ≤ β * W.radius j :=
    (P.infDist_le_of_mem_cell hj).trans (mul_le_mul_of_nonneg_right hβ hr.le)
  -- `X / r_j ≤ X β / δ` for `X ≥ 0`
  have hconv : ∀ X : ℝ, 0 ≤ X → X / W.radius j ≤ X * β / Metric.infDist q F₀ := by
    intro X hX
    rw [div_le_div_iff₀ hr hδ]
    calc
      X * Metric.infDist q F₀ ≤ X * (β * W.radius j) := mul_le_mul_of_nonneg_left hδr hX
      _ = X * β * W.radius j := by ring
  have hCL : 2 * N * (K' * μ ^ 2 * Λ) * L * β ≤ C * L := by
    rw [hCd]
    have : 0 ≤ 2 * N * (K' * μ * Λ) * L := mul_nonneg hA hL
    linarith [this]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 2 * N * (K' * μ * Λ * L) :=
        P.norm_fderiv_spaceSlice_filling_le g hg hF₀ hne hKK' hK' hβ hμ1 hμ2 hHH' hΛ0 hΛ1 hΛ2 hq
      _ = 2 * N * (K' * μ * Λ) * L := by ring
      _ ≤ C * L := by
        rw [hCd]
        have : 0 ≤ 2 * N * (K' * μ ^ 2 * Λ) * β * L := mul_nonneg (mul_nonneg hB hβ0) hL
        linarith
  · calc
      _ ≤ 2 * N * (K' * μ ^ 2 * Λ * L) / W.radius j :=
        P.norm_fderiv_fderiv_spaceSlice_filling_le g hg hF₀ hne hKK' hK' hβ hμ1 hμ2 hHH' hΛ0
          hΛ1 hΛ2 hq hj
      _ ≤ 2 * N * (K' * μ ^ 2 * Λ * L) * β / Metric.infDist q F₀ :=
        hconv _ (mul_nonneg hB hL |>.trans_eq (by ring))
      _ = 2 * N * (K' * μ ^ 2 * Λ) * L * β / Metric.infDist q F₀ := by ring
      _ ≤ C * L / Metric.infDist q F₀ := div_le_div_of_nonneg_right hCL hδ.le
  · calc
      _ ≤ 2 * N * (K' * μ ^ 2 * Λ * L * 1 / W.radius j) :=
        P.norm_deriv_timeSlice_filling_le g hg hF₀ hne hKK' hK' hβ hμ1 hμ2 hHH' hΛ0 hΛ1 hΛ2 hq hj
      _ = 2 * N * (K' * μ ^ 2 * Λ * L) / W.radius j := by ring
      _ ≤ 2 * N * (K' * μ ^ 2 * Λ * L) * β / Metric.infDist q F₀ :=
        hconv _ (mul_nonneg hB hL |>.trans_eq (by ring))
      _ = 2 * N * (K' * μ ^ 2 * Λ) * L * β / Metric.infDist q F₀ := by ring
      _ ≤ C * L / Metric.infDist q F₀ := div_le_div_of_nonneg_right hCL hδ.le

end ParabolicRectifiability
