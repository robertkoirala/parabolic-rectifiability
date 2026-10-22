import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Data

/-! # Deviation of the Whitney filling

For Whitney data `W` with weights `φ`
and a function `g` that is `L`-Lipschitz on the node set `F₀ ∪ {p_j}`, the filling
`F = whitneyFilling φ g` satisfies

* `‖F(q) - g(p_j)‖ ≤ H L r_j` for `q ∈ Q_j` (node deviation), because off `F₀`
  the filling is a finite convex combination of node values `g(p_i)` whose active
  centers satisfy `d_P(p_i,p_j) ≤ H r_j`;
* `‖F(q) - g(x)‖ ≤ (1 + (H+D)/a) L d_P(q,x)` for `x ∈ F₀` (trace comparison),
  using `d_P(q,p_j) ≤ D r_j` and `a r_j ≤ d_P(q,F₀) ≤ d_P(q,x)`.

The supporting finite-sum identities are stated separately: at a point off `F₀`
only finitely many weights are active, they sum to one over every finset
containing the active indices, and the filling is the corresponding finite sum.
No completeness of the value space is used.

*Measurable residuals.* Cell closures are compact and avoid `F₀`, so only finitely
many weights are active on a cell; there the filling is a fixed finite combination
of measurable weights. With `g` continuous on the closed set `F₀`, every residual
`q ↦ ‖F(q) - A(q)‖ₑ` against a continuous `A` is measurable, although the value
space carries no measurable structure.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

namespace WhitneyData

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}

/-- Cells lie off the retained set. -/
theorem notMem_of_mem_cell (W : WhitneyData m ι F₀ D a) {j : ι} {q : Space m}
    (hq : q ∈ W.cell j) : q ∉ F₀ := by
  have h : q ∈ ⋃ i, W.cell i := mem_iUnion.mpr ⟨j, hq⟩
  rw [W.iUnion_cell] at h
  exact h

/-- Every point off the retained set lies in some cell. -/
theorem exists_mem_cell (W : WhitneyData m ι F₀ D a) {q : Space m} (hq : q ∉ F₀) :
    ∃ j, q ∈ W.cell j := by
  have h : q ∈ ⋃ i, W.cell i := by rw [W.iUnion_cell]; exact hq
  exact mem_iUnion.mp h

theorem center_mem_nodeSet (W : WhitneyData m ι F₀ D a) (j : ι) :
    W.center j ∈ W.nodeSet :=
  Or.inr ⟨j, rfl⟩

theorem mem_nodeSet_of_mem (W : WhitneyData m ι F₀ D a) {x : Space m} (hx : x ∈ F₀) :
    x ∈ W.nodeSet :=
  Or.inl hx

/-- Points of a cell are within `D r_j` of its center. -/
theorem dist_center_le (W : WhitneyData m ι F₀ D a) {j : ι} {q : Space m}
    (hq : q ∈ W.cell j) : dist q (W.center j) ≤ D * W.radius j :=
  Metric.mem_closedBall.mp (W.cell_subset j hq)

end WhitneyData

namespace WhitneyWeights

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H : ℝ}
  {W : WhitneyData m ι F₀ D a}

/-- Off `F₀` only finitely many weights are active at a point. -/
theorem finite_active (φ : WhitneyWeights W H) {q : Space m} (hq : q ∉ F₀) :
    {i | φ.weight i q ≠ 0}.Finite := by
  obtain ⟨U, hU, hfin⟩ := φ.locallyFinite q hq
  exact hfin.subset fun i hi => ⟨q, mem_of_mem_nhds hU, hi⟩

/-- Finite local sum: off `F₀`, the weights sum to one over every finset containing
the active indices. -/
theorem sum_weight_eq_one (φ : WhitneyWeights W H) {q : Space m} (hq : q ∉ F₀)
    {s : Finset ι} (hs : ∀ i ∉ s, φ.weight i q = 0) : ∑ i ∈ s, φ.weight i q = 1 :=
  (hasSum_sum_of_ne_finset_zero hs).unique (φ.hasSum_one q hq)

/-- The finset of active indices at a point off `F₀`. -/
def activeFinset (φ : WhitneyWeights W H) {q : Space m} (hq : q ∉ F₀) : Finset ι :=
  (φ.finite_active hq).toFinset

theorem weight_eq_zero_of_notMem_activeFinset (φ : WhitneyWeights W H) {q : Space m}
    (hq : q ∉ F₀) {i : ι} (hi : i ∉ φ.activeFinset hq) : φ.weight i q = 0 := by
  by_contra h
  exact hi ((φ.finite_active hq).mem_toFinset.mpr h)

end WhitneyWeights

section Filling

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H : ℝ}
  {W : WhitneyData m ι F₀ D a} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Trace agreement: the filling equals `g` on `F₀`. -/
theorem whitneyFilling_of_mem (φ : WhitneyWeights W H) (g : Space m → Y) {q : Space m}
    (hq : q ∈ F₀) : whitneyFilling φ g q = g q := by
  unfold whitneyFilling
  rw [ite_eq_left hq]

/-- Off `F₀` the filling is the finite sum over any finset containing the active
indices. -/
theorem whitneyFilling_eq_sum (φ : WhitneyWeights W H) (g : Space m → Y) {q : Space m}
    (hq : q ∉ F₀) {s : Finset ι} (hs : ∀ i ∉ s, φ.weight i q = 0) :
    whitneyFilling φ g q = ∑ i ∈ s, φ.weight i q • g (W.center i) := by
  unfold whitneyFilling
  rw [ite_eq_right hq]
  exact tsum_eq_sum fun i hi => by rw [hs i hi, zero_smul]

/-- Node deviation: on the cell `Q_j`, `‖F(q) - g(p_j)‖ ≤ H L r_j`. -/
theorem norm_whitneyFilling_sub_center_le (φ : WhitneyWeights W H) (g : Space m → Y)
    {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) {j : ι} {q : Space m}
    (hq : q ∈ W.cell j) :
    ‖whitneyFilling φ g q - g (W.center j)‖ ≤ H * L * W.radius j := by
  have hqF : q ∉ F₀ := W.notMem_of_mem_cell hq
  set s := φ.activeFinset hqF
  have hs : ∀ i ∉ s, φ.weight i q = 0 := fun i hi =>
    φ.weight_eq_zero_of_notMem_activeFinset hqF hi
  have h1 : ∑ i ∈ s, φ.weight i q = 1 := φ.sum_weight_eq_one hqF hs
  have hsub : whitneyFilling φ g q - g (W.center j) =
      ∑ i ∈ s, φ.weight i q • (g (W.center i) - g (W.center j)) := by
    rw [whitneyFilling_eq_sum φ g hqF hs]
    calc
      _ = ∑ i ∈ s, φ.weight i q • g (W.center i) -
          (∑ i ∈ s, φ.weight i q) • g (W.center j) := by rw [h1, one_smul]
      _ = _ := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        simp only [smul_sub]
  rw [hsub]
  calc
    ‖∑ i ∈ s, φ.weight i q • (g (W.center i) - g (W.center j))‖
        ≤ ∑ i ∈ s, ‖φ.weight i q • (g (W.center i) - g (W.center j))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, φ.weight i q * (H * L * W.radius j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (φ.nonneg i q)]
        rcases eq_or_ne (φ.weight i q) 0 with h0 | h0
        · rw [h0, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg i q)
          rw [← dist_eq_norm]
          calc
            dist (g (W.center i)) (g (W.center j))
                ≤ L * dist (W.center i) (W.center j) :=
              hg.dist_le_mul _ (W.center_mem_nodeSet i) _ (W.center_mem_nodeSet j)
            _ ≤ L * (H * W.radius j) :=
              mul_le_mul_of_nonneg_left (φ.center_dist_le i j q hq h0) (NNReal.coe_nonneg L)
            _ = H * L * W.radius j := by ring
    _ = H * L * W.radius j := by rw [← Finset.sum_mul, h1, one_mul]

/-- Trace comparison: for `x ∈ F₀`, `‖F(q) - g(x)‖ ≤ (1 + (H+D)/a) L d_P(q,x)`. -/
theorem norm_whitneyFilling_sub_le_dist (hH : 0 ≤ H) (φ : WhitneyWeights W H)
    (g : Space m → Y) {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet) {x : Space m}
    (hx : x ∈ F₀) (q : Space m) :
    ‖whitneyFilling φ g q - g x‖ ≤ (1 + (H + D) / a) * L * dist q x := by
  have ha : 0 < a := W.a_pos
  have hD : 0 ≤ D := zero_le_one.trans W.one_le_D
  have hHD : 0 ≤ (H + D) / a := div_nonneg (add_nonneg hH hD) ha.le
  have hL : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  by_cases hq : q ∈ F₀
  · rw [whitneyFilling_of_mem φ g hq, ← dist_eq_norm]
    calc
      dist (g q) (g x) ≤ L * dist q x :=
        hg.dist_le_mul _ (W.mem_nodeSet_of_mem hq) _ (W.mem_nodeSet_of_mem hx)
      _ = 1 * (L * dist q x) := (one_mul _).symm
      _ ≤ (1 + (H + D) / a) * (L * dist q x) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hL dist_nonneg)
      _ = (1 + (H + D) / a) * L * dist q x := by ring
  · obtain ⟨j, hj⟩ := W.exists_mem_cell hq
    have h1 := norm_whitneyFilling_sub_center_le φ g hg hj
    have hr : a * W.radius j ≤ dist q x :=
      (W.le_infDist j q hj).trans (Metric.infDist_le_dist_of_mem hx)
    have hrj : W.radius j ≤ dist q x / a := by
      rw [le_div_iff₀ ha]
      linarith
    have h2 : ‖g (W.center j) - g x‖ ≤ L * (D * W.radius j + dist q x) := by
      rw [← dist_eq_norm]
      calc
        dist (g (W.center j)) (g x) ≤ L * dist (W.center j) x :=
          hg.dist_le_mul _ (W.center_mem_nodeSet j) _ (W.mem_nodeSet_of_mem hx)
        _ ≤ L * (D * W.radius j + dist q x) := by
          refine mul_le_mul_of_nonneg_left ?_ hL
          calc
            dist (W.center j) x ≤ dist (W.center j) q + dist q x := dist_triangle _ _ _
            _ ≤ D * W.radius j + dist q x := by
              rw [dist_comm]
              linarith [W.dist_center_le hj]
    have h3 : (H + D) * L * W.radius j ≤ (H + D) * L * (dist q x / a) :=
      mul_le_mul_of_nonneg_left hrj (mul_nonneg (add_nonneg hH hD) hL)
    calc
      ‖whitneyFilling φ g q - g x‖
          ≤ ‖whitneyFilling φ g q - g (W.center j)‖ + ‖g (W.center j) - g x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ H * L * W.radius j + L * (D * W.radius j + dist q x) := add_le_add h1 h2
      _ = L * dist q x + (H + D) * L * W.radius j := by ring
      _ ≤ L * dist q x + (H + D) * L * (dist q x / a) := by linarith
      _ = (1 + (H + D) / a) * L * dist q x := by ring

end Filling

section MeasurableResidual

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H : ℝ}
  {W : WhitneyData m ι F₀ D a}

/-- The closure of a cell avoids `F₀`, since `a r_j ≤ d_P(·,F₀)` on the cell. -/
theorem WhitneyData.closure_cell_subset_compl (W : WhitneyData m ι F₀ D a) (j : ι) :
    closure (W.cell j) ⊆ F₀ᶜ := by
  have hsub : closure (W.cell j) ⊆ {x | a * W.radius j ≤ Metric.infDist x F₀} :=
    closure_minimal (fun q hq => W.le_infDist j q hq)
      (isClosed_le continuous_const (Metric.continuous_infDist_pt F₀))
  intro x hx hxF
  have h1 : a * W.radius j ≤ Metric.infDist x F₀ := hsub hx
  rw [Metric.infDist_zero_of_mem hxF] at h1
  exact absurd h1 (not_le.mpr (mul_pos W.a_pos (W.radius_pos j)))

/-- Cell closures are compact. -/
theorem WhitneyData.isCompact_closure_cell (W : WhitneyData m ι F₀ D a) (j : ι) :
    IsCompact (closure (W.cell j)) :=
  (isCompact_closedBall (W.center j) (D * W.radius j)).of_isClosed_subset isClosed_closure
    (closure_minimal (W.cell_subset j) Metric.isClosed_closedBall)

/-- Only finitely many weights are active somewhere on a given cell. -/
theorem WhitneyWeights.finite_active_cell (φ : WhitneyWeights W H) (j : ι) :
    {i | ∃ x ∈ W.cell j, φ.weight i x ≠ 0}.Finite := by
  have hU : ∀ x ∈ closure (W.cell j),
      ∃ U ∈ 𝓝 x, {i | ∃ y ∈ U, φ.weight i y ≠ 0}.Finite :=
    fun x hx => φ.locallyFinite x (W.closure_cell_subset_compl j hx)
  choose! U hUn hUf using hU
  obtain ⟨t, htK, ht⟩ := (W.isCompact_closure_cell j).elim_nhds_subcover U hUn
  refine (t.finite_toSet.biUnion fun x hx => hUf x (htK x hx)).subset ?_
  rintro i ⟨y, hy, hiy⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (ht (subset_closure hy))
  exact mem_iUnion₂.mpr ⟨x, hx, y, hyx, hiy⟩

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Measurable residuals: for `g` continuous on `F₀` and a continuous comparison map
`A`, the residual `q ↦ ‖F(q) - A(q)‖ₑ` of the filling is measurable. On each cell the
filling is a fixed finite combination of measurable weights; on the closed set `F₀`
it is `g`. -/
theorem measurable_enorm_whitneyFilling_sub [Countable ι] (hF₀ : IsClosed F₀)
    (φ : WhitneyWeights W H)
    (g : Space m → Y) (hg : ContinuousOn g F₀) {A : Space m → Y} (hA : Continuous A) :
    Measurable fun q => ‖whitneyFilling φ g q - A q‖ₑ := by
  classical
  have hcell : ∀ j, ∃ ρ : Space m → ℝ≥0∞, Measurable ρ ∧
      ∀ q ∈ W.cell j, ‖whitneyFilling φ g q - A q‖ₑ = ρ q := by
    intro j
    let S : Finset ι := (φ.finite_active_cell j).toFinset
    let Ψ : ((i : S) → ℝ) × Space m → ℝ≥0∞ := fun p =>
      ‖∑ i : S, p.1 i • g (W.center i) - A p.2‖ₑ
    have hΨ : Continuous Ψ :=
      ((continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).smul continuous_const).sub
          (hA.comp continuous_snd)).enorm
    have hw : Measurable fun q : Space m => ((fun i : S => φ.weight i q), q) :=
      (Measurable.of_eval fun (i : S) => φ.measurable i).prodMk measurable_id'
    refine ⟨fun q => Ψ (fun i => φ.weight i q, q), hΨ.measurable.comp hw, fun q hq => ?_⟩
    have hqF : q ∉ F₀ := W.notMem_of_mem_cell hq
    have hS : ∀ i ∉ S, φ.weight i q = 0 := fun i hi => by
      by_contra h
      exact hi ((φ.finite_active_cell j).mem_toFinset.mpr ⟨q, hq, h⟩)
    simp only [Ψ, whitneyFilling_eq_sum φ g hqF hS]
    rw [Finset.sum_coe_sort (s := S) (f := fun i => φ.weight i q • g (W.center i))]
  choose ρ hρm hρ using hcell
  have heq : (fun q => ‖whitneyFilling φ g q - A q‖ₑ) = fun q =>
      F₀.piecewise (fun q => ‖g q - A q‖ₑ) 0 q + ∑' j, (W.cell j).indicator (ρ j) q := by
    funext q
    by_cases hq : q ∈ F₀
    · have h0 : ∀ j, (W.cell j).indicator (ρ j) q = 0 := fun j =>
        indicator_of_notMem (fun h => W.notMem_of_mem_cell h hq) _
      simp only [piecewise_eq_of_mem _ _ _ hq, whitneyFilling_of_mem φ g hq, h0, tsum_zero,
        add_zero]
    · obtain ⟨j, hj⟩ := W.exists_mem_cell hq
      have h0 : ∀ i ≠ j, (W.cell i).indicator (ρ i) q = 0 := fun i hi =>
        indicator_of_notMem (fun h => Set.disjoint_left.mp (W.pairwise_disjoint hi) h hj) _
      rw [piecewise_eq_of_notMem _ _ _ hq, Pi.zero_apply, zero_add, tsum_eq_single j h0,
        indicator_of_mem hj, hρ j q hj]
  rw [heq]
  exact (ContinuousOn.measurable_piecewise (hg.sub hA.continuousOn).enorm continuousOn_const
      hF₀.measurableSet).add
    (Measurable.tsum fun j => (hρm j).indicator (W.measurableSet_cell j))

/-- The squared residual against a spatial affine map, for `g` Lipschitz on the node
set, is measurable. -/
theorem measurable_whitneyFilling_affineResidual [Countable ι] (hF₀ : IsClosed F₀)
    (φ : WhitneyWeights W H) (g : Space m → Y) {L : ℝ≥0} (hg : LipschitzOnWith L g W.nodeSet)
    (c₀ : Y) (B : Spatial m →L[ℝ] Y) :
    Measurable fun q : Space m => ‖whitneyFilling φ g q - (c₀ + B q.1)‖ₑ ^ 2 :=
  (measurable_enorm_whitneyFilling_sub hF₀ φ g
    ((hg.mono subset_union_left).continuousOn)
    (continuous_const.add (B.continuous.comp continuous_fst))).pow_const 2

end MeasurableResidual

/-- **Deviation of the Whitney filling:** the actual filling deviates from the
node values by `‖F(q) - g(p_j)‖ ≤ H L r_j` on `Q_j`, and from trace values by
`‖F(q) - g(x)‖ ≤ (1 + (H+D)/a) L dist(q,x)` for `x ∈ F₀` (continuity at `F₀`). -/
theorem whitneyFilling_sub_le_proof {m : ℕ} {ι : Type*} [Countable ι] {F₀ : Set (Space m)}
    {D a H : ℝ} (W : WhitneyData m ι F₀ D a) (hH : 0 ≤ H) (φ : WhitneyWeights W H)
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (g : Space m → Y) (L : ℝ≥0)
    (hg : LipschitzOnWith L g W.nodeSet) :
    (∀ j, ∀ q ∈ W.cell j, ‖whitneyFilling φ g q - g (W.center j)‖ ≤ H * L * W.radius j) ∧
    ∀ q, ∀ x ∈ F₀, ‖whitneyFilling φ g q - g x‖ ≤ (1 + (H + D) / a) * L * dist q x :=
  ⟨fun _ _ hq => norm_whitneyFilling_sub_center_le φ g hg hq,
    fun q _ hx => norm_whitneyFilling_sub_le_dist hH φ g hg hx q⟩

end ParabolicRectifiability
