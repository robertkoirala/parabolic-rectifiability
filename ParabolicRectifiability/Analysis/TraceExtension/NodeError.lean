import ParabolicRectifiability.Analysis.TraceExtension.SourceAllocation

/-! # Regularity of the node error and comparison with the source error

Two steps of the regular trace extension:

* `whitney_node_error_regular_of_nodeMeasure` (quantized measurability): the node set
  `C = F₀ ∪ {p_j}` is closed; the constrained node
  error is jointly Borel, finite, and its constrained infimum is attained at every
  positive radius, including `L = 0`. The local finiteness of the node measure
  (proved as `nodeMeasure_ball_lt_top_proof`) is taken as a hypothesis.
* `node_error_le_source_error_of_leaves`: the node error of the allocated node
  function is bounded by the source error at the fixed anchor. The signed Jensen bound
  (`allocated_node_estimates_proof`), continuous domination
  (`volume_restrict_le_of_source_density_proof`) and the bounded-slope source fit
  (`exists_source_fit_slope_le_proof`) are taken as hypotheses.

**Borel representative.** The function `g` is arbitrary off the node set. All
measurability statements use the integrand `nodeIntegrand C g (a,B)`, equal to
`‖g - a - B u‖²` on `C` and zero off `C`. It is Borel because `C` is closed and `g`
is continuous on `C`; it agrees `ν`-almost everywhere with the original integrand
because `ν` is carried by `C`.

**Measurability.** For fixed `(a,B)` the fit on `P(p,s)` is jointly Borel in `(p,s)`.
For fixed `(p,s)` it is continuous in `(a,B)` (dominated convergence; the ball has
finite node mass and `g` is bounded on `C ∩ P(p,s)`). A countable dense subset of the
admissible set `Y × {‖B‖ ≤ L}` therefore gives the same infimum.

**Attainment.** If `‖a‖ ≥ 2G + L U` (with `G` bounding `‖g‖` and `U` bounding `‖u‖`
on `C ∩ P(p,s)`), the competitor `(a,B)` is no better than `(0,0)`. The minimum over
the compact set `{‖a‖ ≤ 2G + L U} × {‖B‖ ≤ L}` is therefore global.

**Comparison.** For every affine `A`, the continuous part of the node fit is
dominated by the source on `F₀`, and each atom by signed Jensen; the allocated
reservoirs of the atoms in `P(p,s)` lie in `P(a_p, C₁ s)` and have total density
at most `A`. The least-squares source fit is an admissible competitor.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

universe u v

namespace ParabolicRectifiability

/-! ## Whitney node sets -/

namespace WhitneyData

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}

theorem center_notMem (W : WhitneyData m ι F₀ D a) (j : ι) : W.center j ∉ F₀ := by
  have h : W.center j ∈ ⋃ i, W.cell i := mem_iUnion.mpr ⟨j, W.center_mem j⟩
  rw [W.iUnion_cell] at h
  exact h

theorem center_injective (W : WhitneyData m ι F₀ D a) : Function.Injective W.center := by
  intro i j h
  by_contra hij
  have hi : W.center i ∈ W.cell j := by rw [h]; exact W.center_mem j
  exact Set.disjoint_left.mp (W.pairwise_disjoint hij) (W.center_mem i) hi

theorem subset_nodeSet (W : WhitneyData m ι F₀ D a) : F₀ ⊆ W.nodeSet := subset_union_left

theorem center_mem_nodeSet (W : WhitneyData m ι F₀ D a) (j : ι) : W.center j ∈ W.nodeSet :=
  Or.inr ⟨j, rfl⟩

/-- The node set is closed: centers accumulating off `F₀` would have radii bounded
below (upper center distance) and so be separated. -/
theorem isClosed_nodeSet (W : WhitneyData m ι F₀ D a) (hF₀ : IsClosed F₀)
    (hne : F₀.Nonempty) {b s₀ : ℝ}
    (hb : ∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j) (hs₀ : 0 < s₀)
    (hsep : ∀ i j, i ≠ j → s₀ * max (W.radius i) (W.radius j) ≤ dist (W.center i) (W.center j)) :
    IsClosed W.nodeSet := by
  refine isClosed_of_closure_subset fun q hq => ?_
  unfold nodeSet at hq ⊢
  rw [closure_union, hF₀.closure_eq] at hq
  rcases hq with hq | hq
  · exact Or.inl hq
  by_cases hqF : q ∈ F₀
  · exact Or.inl hqF
  right
  have hδ : 0 < Metric.infDist q F₀ := (hF₀.notMem_iff_infDist_pos hne).mp hqF
  set δ := Metric.infDist q F₀
  have hnear : ∀ j, dist q (W.center j) < δ / 2 → δ / 2 < b * W.radius j := by
    intro j hj
    have h1 : δ ≤ Metric.infDist (W.center j) F₀ + dist q (W.center j) :=
      Metric.infDist_le_infDist_add_dist
    linarith [hb j]
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := Metric.mem_closure_iff.mp hq (δ / 2) (by linarith)
  have hbj := hnear j hj
  have hrj := W.radius_pos j
  have hb0 : 0 < b := by
    by_contra h
    push Not at h
    nlinarith
  set η := min (δ / 2) (s₀ * δ / (4 * b))
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Metric.mem_closure_iff.mp hq η hη0
  by_cases h0 : dist q (W.center i) = 0
  · exact ⟨i, (dist_eq_zero.mp h0).symm⟩
  · exfalso
    have hpos : 0 < dist q (W.center i) := lt_of_le_of_ne dist_nonneg (Ne.symm h0)
    obtain ⟨_, ⟨i', rfl⟩, hi'⟩ := Metric.mem_closure_iff.mp hq _ hpos
    have hne' : i ≠ i' := by
      rintro rfl
      exact lt_irrefl _ hi'
    have hηle : η ≤ δ / 2 := min_le_left _ _
    have hηle' : η ≤ s₀ * δ / (4 * b) := min_le_right _ _
    have hri : δ / 2 < b * W.radius i := hnear i (by linarith)
    have hsep' := hsep i i' hne'
    have hmax : s₀ * W.radius i ≤ s₀ * max (W.radius i) (W.radius i') :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hs₀.le
    have hd : dist (W.center i) (W.center i') ≤
        dist q (W.center i) + dist q (W.center i') := by
      have := dist_triangle (W.center i) q (W.center i')
      rw [dist_comm (W.center i) q] at this
      exact this
    have hX : s₀ * δ / (4 * b) < s₀ * W.radius i / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      have h2 : s₀ * δ < s₀ * (2 * (b * W.radius i)) :=
        mul_lt_mul_of_pos_left (by linarith) hs₀
      nlinarith
    linarith

/-- The node measure is carried by the node set. -/
theorem nodeMeasure_compl_nodeSet (W : WhitneyData m ι F₀ D a)
    (hC : MeasurableSet W.nodeSet) : W.nodeMeasure W.nodeSetᶜ = 0 := by
  rw [nodeMeasure, Measure.add_apply, Measure.restrict_apply hC.compl,
    Measure.sum_apply _ hC.compl]
  have h1 : W.nodeSetᶜ ∩ F₀ = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun q hq => hq.1 (Or.inl hq.2)
  have h2 : ∀ j, (ENNReal.ofReal (W.radius j ^ (m + 2)) • Measure.dirac (W.center j))
      W.nodeSetᶜ = 0 := fun j => by
    have hj : W.center j ∉ W.nodeSetᶜ := fun h => h (W.center_mem_nodeSet j)
    rw [Measure.smul_apply, Measure.dirac_apply' _ hC.compl, Set.indicator_of_notMem hj,
      smul_eq_mul, mul_zero]
  rw [h1, measure_empty, zero_add]
  exact ENNReal.tsum_eq_zero.mpr h2

end WhitneyData

/-! ## The Borel node integrand -/

section NodeFit

variable {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The fitting integrand on `C`, extended by zero: a Borel representative. -/
def nodeIntegrand (C : Set (Space m)) (g : Space m → Y)
    (x : Y × (Spatial m →L[ℝ] Y)) (q : Space m) : ℝ≥0∞ :=
  C.indicator (fun q => ‖g q - (x.1 + x.2 q.1)‖ₑ ^ 2) q

/-- The fit of the Borel representative on `P(p,s)`. -/
def nodeFit (ν : Measure (Space m)) (C : Set (Space m)) (g : Space m → Y)
    (x : Y × (Spatial m →L[ℝ] Y)) (p : Space m) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ q in Metric.ball p s, nodeIntegrand C g x q ∂ν

theorem measurable_nodeIntegrand {C : Set (Space m)} (hC : IsClosed C) {g : Space m → Y}
    (hg : ContinuousOn g C) (x : Y × (Spatial m →L[ℝ] Y)) :
    Measurable (nodeIntegrand C g x) := by
  classical
  have h : ContinuousOn (fun q : Space m => ‖g q - (x.1 + x.2 q.1)‖ₑ ^ 2) C :=
    (ENNReal.continuous_pow 2).comp_continuousOn
      (hg.sub (continuous_const.add (x.2.continuous.comp continuous_fst)).continuousOn).enorm
  have hm := h.measurable_piecewise (continuousOn_const (c := (0 : ℝ≥0∞))) hC.measurableSet
  convert hm using 1
  ext q
  by_cases hq : q ∈ C
  · rw [nodeIntegrand, Set.indicator_of_mem hq, Set.piecewise_eq_of_mem _ _ _ hq]
  · rw [nodeIntegrand, Set.indicator_of_notMem hq, Set.piecewise_eq_of_notMem _ _ _ hq]

theorem affineFitIntegral_eq_nodeFit {ν : Measure (Space m)} {C : Set (Space m)}
    (hν : ∀ᵐ q ∂ν, q ∈ C) (g : Space m → Y) (x : Y × (Spatial m →L[ℝ] Y))
    (p : Space m) (s : ℝ) :
    affineFitIntegral ν g x.1 x.2 p s = nodeFit ν C g x p s := by
  unfold affineFitIntegral nodeFit
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hν] with q hq
  rw [nodeIntegrand, Set.indicator_of_mem hq]

omit [InnerProductSpace ℝ Y] in
/-- On `C ∩ P(p,s)`, `g` is bounded by `G = ‖g(y₀)‖ + L (|s| + d(p,y₀))`. -/
theorem norm_le_of_mem_node {C : Set (Space m)} {g : Space m → Y} {L : ℝ≥0}
    (hg : LipschitzOnWith L g C) {y₀ q p : Space m} {s : ℝ} (hy₀ : y₀ ∈ C) (hq : q ∈ C)
    (hqb : q ∈ Metric.ball p s) :
    ‖g q‖ ≤ ‖g y₀‖ + L * (|s| + dist p y₀) := by
  have hdq : dist q p < s := Metric.mem_ball.mp hqb
  have hs : s ≤ |s| := le_abs_self s
  have hL := hg.dist_le_mul q hq y₀ hy₀
  have htri : dist q y₀ ≤ dist q p + dist p y₀ := dist_triangle q p y₀
  have hmul : (L : ℝ) * dist q y₀ ≤ L * (|s| + dist p y₀) :=
    mul_le_mul_of_nonneg_left (by linarith) L.coe_nonneg
  have h1 : ‖g q‖ ≤ ‖g y₀‖ + ‖g q - g y₀‖ := norm_le_norm_add_norm_sub' (g q) (g y₀)
  rw [← dist_eq_norm] at h1
  linarith

/-- On `P(p,s)`, the spatial coordinate is bounded by `U = ‖p₁‖ + |s|`. -/
theorem norm_fst_le_of_mem_ball {q p : Space m} {s : ℝ} (hqb : q ∈ Metric.ball p s) :
    ‖q.1‖ ≤ ‖p.1‖ + |s| := by
  have hdq : dist q p < s := Metric.mem_ball.mp hqb
  have h1 : dist q.1 p.1 ≤ dist q p := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have h2 : ‖q.1‖ ≤ ‖p.1‖ + ‖q.1 - p.1‖ := norm_le_norm_add_norm_sub' q.1 p.1
  rw [← dist_eq_norm] at h2
  linarith [le_abs_self s]

theorem norm_sub_affine_le {C : Set (Space m)} {g : Space m → Y} {L : ℝ≥0}
    (hg : LipschitzOnWith L g C) {y₀ q p : Space m} {s : ℝ} (hy₀ : y₀ ∈ C) (hq : q ∈ C)
    (hqb : q ∈ Metric.ball p s) (x : Y × (Spatial m →L[ℝ] Y)) :
    ‖g q - (x.1 + x.2 q.1)‖ ≤
      (‖g y₀‖ + L * (|s| + dist p y₀)) + ‖x.1‖ + ‖x.2‖ * (‖p.1‖ + |s|) := by
  have h1 := norm_le_of_mem_node hg hy₀ hq hqb
  have h2 := norm_fst_le_of_mem_ball hqb
  have h3 : ‖x.2 q.1‖ ≤ ‖x.2‖ * (‖p.1‖ + |s|) :=
    (x.2.le_opNorm q.1).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have h4 : ‖g q - (x.1 + x.2 q.1)‖ ≤ ‖g q‖ + (‖x.1‖ + ‖x.2 q.1‖) :=
    (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  linarith

theorem norm_le_norm_sub_affine {g : Space m → Y} (q p : Space m) (s : ℝ)
    (hqb : q ∈ Metric.ball p s) (x : Y × (Spatial m →L[ℝ] Y)) :
    ‖x.1‖ - ‖g q‖ - ‖x.2‖ * (‖p.1‖ + |s|) ≤ ‖g q - (x.1 + x.2 q.1)‖ := by
  have h2 := norm_fst_le_of_mem_ball hqb
  have h3 : ‖x.2 q.1‖ ≤ ‖x.2‖ * (‖p.1‖ + |s|) :=
    (x.2.le_opNorm q.1).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have e : x.1 = g q - (g q - (x.1 + x.2 q.1)) - x.2 q.1 := by abel
  have h4 : ‖x.1‖ ≤ ‖g q‖ + ‖g q - (x.1 + x.2 q.1)‖ + ‖x.2 q.1‖ := by
    calc ‖x.1‖ = ‖g q - (g q - (x.1 + x.2 q.1)) - x.2 q.1‖ := congrArg _ e
      _ ≤ ‖g q - (g q - (x.1 + x.2 q.1))‖ + ‖x.2 q.1‖ := norm_sub_le _ _
      _ ≤ ‖g q‖ + ‖g q - (x.1 + x.2 q.1)‖ + ‖x.2 q.1‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
  linarith

/-- For a fixed ball of finite mass, the fit is continuous in the coefficients. -/
theorem continuous_nodeFit {ν : Measure (Space m)} {C : Set (Space m)} (hC : IsClosed C)
    {g : Space m → Y} {L : ℝ≥0} (hg : LipschitzOnWith L g C) {y₀ : Space m} (hy₀ : y₀ ∈ C)
    {p : Space m} {s : ℝ} (hfin : ν (Metric.ball p s) ≠ ⊤) :
    Continuous fun x => nodeFit ν C g x p s := by
  rw [continuous_iff_continuousAt]
  intro x₀
  show Tendsto (fun x => ∫⁻ q, nodeIntegrand C g x q ∂(ν.restrict (Metric.ball p s))) (𝓝 x₀)
    (𝓝 (∫⁻ q, nodeIntegrand C g x₀ q ∂(ν.restrict (Metric.ball p s))))
  set M : ℝ := (‖g y₀‖ + L * (|s| + dist p y₀)) + (‖x₀.1‖ + 1) +
    (‖x₀.2‖ + 1) * (‖p.1‖ + |s|) with hM
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => ENNReal.ofReal M ^ 2)
    (Eventually.of_forall fun x => measurable_nodeIntegrand hC hg.continuousOn x) ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
    by_cases hqC : q ∈ C
    · rw [nodeIntegrand, Set.indicator_of_mem hqC]
      have hx' : ‖x - x₀‖ < 1 := by rw [← dist_eq_norm]; exact hx
      have h1 : ‖x.1‖ ≤ ‖x₀.1‖ + 1 := by
        have := norm_fst_le (x - x₀)
        have h' : ‖x.1‖ ≤ ‖x₀.1‖ + ‖x.1 - x₀.1‖ := norm_le_norm_add_norm_sub' x.1 x₀.1
        have h'' : (x - x₀).1 = x.1 - x₀.1 := rfl
        rw [h''] at this
        linarith
      have h2 : ‖x.2‖ ≤ ‖x₀.2‖ + 1 := by
        have := norm_snd_le (x - x₀)
        have h' : ‖x.2‖ ≤ ‖x₀.2‖ + ‖x.2 - x₀.2‖ := norm_le_norm_add_norm_sub' x.2 x₀.2
        have h'' : (x - x₀).2 = x.2 - x₀.2 := rfl
        rw [h''] at this
        linarith
      have hb := norm_sub_affine_le hg hy₀ hqC hq x
      have h3 : ‖x.2‖ * (‖p.1‖ + |s|) ≤ (‖x₀.2‖ + 1) * (‖p.1‖ + |s|) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have hle : ‖g q - (x.1 + x.2 q.1)‖ ≤ M := by rw [hM]; linarith
      rw [← ofReal_norm]
      exact pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hle) 2
    · rw [nodeIntegrand, Set.indicator_of_notMem hqC]
      exact zero_le
  · rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hfin
  · refine ae_of_all _ fun q => ?_
    by_cases hqC : q ∈ C
    · simp only [nodeIntegrand, Set.indicator_of_mem hqC]
      exact ((ENNReal.continuous_pow 2).comp (continuous_const.sub (continuous_fst.add
        (continuous_snd.clm_apply continuous_const))).enorm).tendsto x₀
    · simp only [nodeIntegrand, Set.indicator_of_notMem hqC]
      exact tendsto_const_nhds

/-- For fixed coefficients, the fit is jointly Borel in the center and the radius. -/
theorem measurable_nodeFit {ν : Measure (Space m)} [SFinite ν] {C : Set (Space m)}
    (hC : IsClosed C) {g : Space m → Y} (hg : ContinuousOn g C)
    (x : Y × (Spatial m →L[ℝ] Y)) :
    Measurable fun p : Space m × ℝ => nodeFit ν C g x p.1 p.2 := by
  have hF : Measurable (fun z : (Space m × ℝ) × Space m =>
      (Metric.ball z.1.1 z.1.2).indicator (nodeIntegrand C g x) z.2) := by
    classical
    change Measurable (fun z : (Space m × ℝ) × Space m =>
      if dist z.2 z.1.1 < z.1.2 then nodeIntegrand C g x z.2 else 0)
    exact Measurable.ite
      (measurableSet_lt (measurable_snd.dist measurable_fst.fst) measurable_fst.snd)
      ((measurable_nodeIntegrand hC hg x).comp measurable_snd) measurable_const
  have h := hF.lintegral_prod_right' (ν := ν)
  simpa only [nodeFit, lintegral_indicator measurableSet_ball] using h

/-- The constrained infimum of a continuous function over `Y × {‖B‖ ≤ L}` equals its
infimum over a countable dense subset of that set. -/
theorem iInf_constrained_eq_iInf_dense {Φ : Y × (Spatial m →L[ℝ] Y) → ℝ≥0∞}
    (hΦ : Continuous Φ) {L : ℝ≥0} {Dset : Set (Y × (Spatial m →L[ℝ] Y))}
    (hDsub : Dset ⊆ univ ×ˢ Metric.closedBall 0 L)
    (hDdense : univ ×ˢ Metric.closedBall 0 L ⊆ closure Dset) :
    (⨅ (a : Y) (B : Spatial m →L[ℝ] Y) (_ : ‖B‖ ≤ (L : ℝ)), Φ (a, B)) =
      ⨅ d : Dset, Φ d := by
  apply le_antisymm
  · refine le_iInf fun d => ?_
    have hd := hDsub d.2
    exact iInf_le_of_le d.1.1 (iInf_le_of_le d.1.2
      (iInf_le_of_le (mem_closedBall_zero_iff.mp hd.2) le_rfl))
  · refine le_iInf fun a => le_iInf fun B => le_iInf fun hB => ?_
    by_contra hlt
    push Not at hlt
    have hmem : (a, B) ∈ closure Dset :=
      hDdense ⟨mem_univ _, mem_closedBall_zero_iff.mpr hB⟩
    obtain ⟨d, hdU, hdD⟩ := mem_closure_iff.mp hmem {x | Φ x < ⨅ d : Dset, Φ d}
      (isOpen_lt hΦ continuous_const) hlt
    exact absurd (iInf_le (fun d : Dset => Φ d) ⟨d, hdD⟩) (not_le.mpr hdU)

end NodeFit

/-! ## Closedness, measurability, finiteness and attainment -/

section Regular

variable {m : ℕ} {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Joint measurability of the constrained error for a measure carried by a closed set
on which `g` is Lipschitz, with finite mass on balls. -/
theorem measurable_constrainedAffineErrorSq_of_closed [FiniteDimensional ℝ Y]
    {ν : Measure (Space m)} [SFinite ν] {C : Set (Space m)} (hC : IsClosed C)
    (hν : ∀ᵐ q ∂ν, q ∈ C) (hfin : ∀ p s, ν (Metric.ball p s) ≠ ⊤) {g : Space m → Y}
    {L : ℝ≥0} (hg : LipschitzOnWith L g C) {y₀ : Space m} (hy₀ : y₀ ∈ C) :
    Measurable (fun p : Space m × ℝ => constrainedAffineErrorSq ν g L p.1 p.2) := by
  have hsep : TopologicalSpace.IsSeparable
      (univ ×ˢ Metric.closedBall (0 : Spatial m →L[ℝ] Y) L : Set (Y × (Spatial m →L[ℝ] Y))) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨Dset, hDsub, hDcount, hDdense⟩ := hsep.exists_countable_dense_subset
  have hkey : ∀ (p : Space m) (s : ℝ),
      (⨅ (a : Y) (B : Spatial m →L[ℝ] Y) (_ : ‖B‖ ≤ (L : ℝ)), affineFitIntegral ν g a B p s) =
        ⨅ d : Dset, nodeFit ν C g d p s := by
    intro p s
    have h1 : ∀ (a : Y) (B : Spatial m →L[ℝ] Y),
        affineFitIntegral ν g a B p s = nodeFit ν C g (a, B) p s :=
      fun a B => affineFitIntegral_eq_nodeFit hν g (a, B) p s
    simp only [h1]
    exact iInf_constrained_eq_iInf_dense (continuous_nodeFit hC hg hy₀ (hfin p s)) hDsub hDdense
  have hfun : (fun p : Space m × ℝ => constrainedAffineErrorSq ν g L p.1 p.2) =
      fun p => if 0 < p.2 then
        (ENNReal.ofReal p.2)⁻¹ ^ (baseDimension (Spatial m) + 2) *
          ⨅ d : Dset, nodeFit ν C g d p.1 p.2 else 0 := by
    funext p
    simp only [constrainedAffineErrorSq, hkey]
  rw [hfun]
  have : Countable Dset := hDcount.to_subtype
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    ((measurable_snd.ennreal_ofReal.inv.pow_const _).mul
      (Measurable.iInf fun d => measurable_nodeFit hC hg.continuousOn d))
    measurable_const

/-- Attainment of the constrained infimum (including `L = 0`) on a ball of finite mass. -/
theorem exists_constrained_minimizer [FiniteDimensional ℝ Y] {ν : Measure (Space m)}
    {C : Set (Space m)} (hC : IsClosed C) (hν : ∀ᵐ q ∂ν, q ∈ C) {g : Space m → Y}
    {L : ℝ≥0} (hg : LipschitzOnWith L g C) {y₀ : Space m} (hy₀ : y₀ ∈ C) (p : Space m)
    (s : ℝ) (hfin : ν (Metric.ball p s) ≠ ⊤) :
    ∃ (a₀ : Y) (B : Spatial m →L[ℝ] Y), ‖B‖ ≤ L ∧
      ∀ (a : Y) (B' : Spatial m →L[ℝ] Y), ‖B'‖ ≤ L →
        affineFitIntegral ν g a₀ B p s ≤ affineFitIntegral ν g a B' p s := by
  set Φ : Y × (Spatial m →L[ℝ] Y) → ℝ≥0∞ := fun x => nodeFit ν C g x p s
  have hΦ : Continuous Φ := continuous_nodeFit hC hg hy₀ hfin
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ‖g y₀‖ + L * (|s| + dist p y₀) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ‖p.1‖ + |s| := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 2 * G + L * U := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set K : Set (Y × (Spatial m →L[ℝ] Y)) :=
    Metric.closedBall (0 : Y) R ×ˢ Metric.closedBall (0 : Spatial m →L[ℝ] Y) L
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hK0 : ((0 : Y), (0 : Spatial m →L[ℝ] Y)) ∈ K :=
    ⟨Metric.mem_closedBall_self hR0, Metric.mem_closedBall_self L.coe_nonneg⟩
  obtain ⟨x, hxK, hxmin⟩ := hKc.exists_isMinOn ⟨_, hK0⟩ hΦ.continuousOn
  -- Competitors with a large intercept are no better than `(0,0)`.
  have hcoer : ∀ (a : Y) (B' : Spatial m →L[ℝ] Y), ‖B'‖ ≤ L → R < ‖a‖ →
      Φ (0, 0) ≤ Φ (a, B') := by
    intro a B' hB' ha
    show nodeFit ν C g (0, 0) p s ≤ nodeFit ν C g (a, B') p s
    unfold nodeFit
    refine setLIntegral_mono' measurableSet_ball fun q hq => ?_
    by_cases hqC : q ∈ C
    · rw [nodeIntegrand, nodeIntegrand, Set.indicator_of_mem hqC, Set.indicator_of_mem hqC]
      have hgq := norm_le_of_mem_node hg hy₀ hqC hq
      have hlow := norm_le_norm_sub_affine (g := g) q p s hq (a, B')
      have hBU : ‖B'‖ * (‖p.1‖ + |s|) ≤ L * (‖p.1‖ + |s|) :=
        mul_le_mul_of_nonneg_right hB' (by positivity)
      have hle : ‖g q - ((0 : Y) + (0 : Spatial m →L[ℝ] Y) q.1)‖ ≤ ‖g q - (a + B' q.1)‖ := by
        have e : g q - ((0 : Y) + (0 : Spatial m →L[ℝ] Y) q.1) = g q := by simp
        rw [e]
        dsimp only at hlow
        rw [hR, hG, hU] at ha
        linarith
      rw [← ofReal_norm, ← ofReal_norm]
      exact pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hle) 2
    · rw [nodeIntegrand, Set.indicator_of_notMem hqC]
      exact zero_le
  refine ⟨x.1, x.2, mem_closedBall_zero_iff.mp hxK.2, fun a B' hB' => ?_⟩
  rw [affineFitIntegral_eq_nodeFit hν g (x.1, x.2), affineFitIntegral_eq_nodeFit hν g (a, B')]
  change Φ x ≤ Φ (a, B')
  by_cases ha : ‖a‖ ≤ R
  · exact isMinOn_iff.mp hxmin _ ⟨mem_closedBall_zero_iff.mpr ha, mem_closedBall_zero_iff.mpr hB'⟩
  · push Not at ha
    exact (isMinOn_iff.mp hxmin _ hK0).trans (hcoer a B' hB' ha)

/-- Finiteness of the constrained error on a ball of finite mass. -/
theorem constrainedAffineErrorSq_lt_top_of_closed {ν : Measure (Space m)}
    {C : Set (Space m)} (hν : ∀ᵐ q ∂ν, q ∈ C) {g : Space m → Y} {L : ℝ≥0}
    (hg : LipschitzOnWith L g C) {y₀ : Space m} (hy₀ : y₀ ∈ C) (p : Space m) (s : ℝ)
    (hfin : ν (Metric.ball p s) ≠ ⊤) :
    constrainedAffineErrorSq ν g L p s < ⊤ := by
  rcases le_or_gt s 0 with hs | hs
  · rw [constrainedAffineErrorSq_of_nonpos ν g L p hs]
    exact ENNReal.zero_lt_top
  set G : ℝ := ‖g y₀‖ + L * (|s| + dist p y₀)
  have hfit : nodeFit ν C g ((0 : Y), (0 : Spatial m →L[ℝ] Y)) p s ≤
      ENNReal.ofReal G ^ 2 * ν (Metric.ball p s) := by
    unfold nodeFit
    rw [← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_ball fun q hq => ?_
    by_cases hqC : q ∈ C
    · rw [nodeIntegrand, Set.indicator_of_mem hqC]
      have hgq := norm_le_of_mem_node hg hy₀ hqC hq
      have hle : ‖g q - ((0 : Y) + (0 : Spatial m →L[ℝ] Y) q.1)‖ ≤ G := by
        have e : g q - ((0 : Y) + (0 : Spatial m →L[ℝ] Y) q.1) = g q := by simp
        rw [e]
        exact hgq
      rw [← ofReal_norm]
      exact pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal hle) 2
    · rw [nodeIntegrand, Set.indicator_of_notMem hqC]
      exact zero_le
  calc constrainedAffineErrorSq ν g L p s
      ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
          affineFitIntegral ν g 0 0 p s :=
        constrainedAffineErrorSq_le_fitIntegral ν g L p hs 0 0 (by simp)
    _ < ⊤ := by
      rw [affineFitIntegral_eq_nodeFit hν g ((0 : Y), (0 : Spatial m →L[ℝ] Y)) p s]
      refine ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr
        (ENNReal.ofReal_pos.mpr hs))) (hfit.trans_lt ?_)
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hfin.lt_top

end Regular

/-- **Quantized measurability.** For Whitney data of a compact nonempty `F₀` with upper
center distance and center separation, and `g` Lipschitz on the node set, the node set is
closed, the constrained node error is jointly measurable and finite, and its infimum is
attained at every positive radius. The first hypothesis is local finiteness of the node
measure (the statement proved by `nodeMeasure_ball_lt_top_proof`). -/
theorem whitney_node_error_regular_of_nodeMeasure
    (hnode : ∀ {m : ℕ} {ι : Type u} [Countable ι] {F₀ : Set (Space m)} {D a : ℝ}
      (W : WhitneyData m ι F₀ D a) (z : Space m) (R : ℝ),
      W.nodeMeasure (Metric.ball z R) < ⊤)
    {m : ℕ} {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
    {D a b s₀ : ℝ} (W : WhitneyData m ι F₀ D a) (hF₀ : IsCompact F₀) (hne : F₀.Nonempty)
    (hb : ∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j) (hs₀ : 0 < s₀)
    (hsep : ∀ i j, i ≠ j → s₀ * max (W.radius i) (W.radius j) ≤ dist (W.center i) (W.center j))
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (g : Space m → Y) (L : ℝ≥0) (hg : LipschitzOnWith L g W.nodeSet) :
    IsClosed W.nodeSet ∧
    Measurable (fun p : Space m × ℝ => constrainedAffineErrorSq W.nodeMeasure g L p.1 p.2) ∧
    (∀ p s, constrainedAffineErrorSq W.nodeMeasure g L p s < ⊤) ∧
    ∀ p s, 0 < s → ∃ (a₀ : Y) (B : Spatial m →L[ℝ] Y), ‖B‖ ≤ L ∧
      constrainedAffineErrorSq W.nodeMeasure g L p s =
        (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
          affineFitIntegral W.nodeMeasure g a₀ B p s := by
  have hC : IsClosed W.nodeSet := W.isClosed_nodeSet hF₀.isClosed hne hb hs₀ hsep
  have hν : ∀ᵐ q ∂W.nodeMeasure, q ∈ W.nodeSet :=
    mem_ae_iff.mpr (W.nodeMeasure_compl_nodeSet hC.measurableSet)
  obtain ⟨y₀, hy₀F⟩ := hne
  have hy₀ : y₀ ∈ W.nodeSet := W.subset_nodeSet hy₀F
  have hfin : ∀ p s, W.nodeMeasure (Metric.ball p s) ≠ ⊤ := fun p s => (hnode W p s).ne
  have : IsFiniteMeasureOnCompacts W.nodeMeasure := ⟨fun K hK => by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (point 0 0)).mp hK.isBounded
    exact (measure_mono hR).trans_lt (hnode W _ _)⟩
  refine ⟨hC, measurable_constrainedAffineErrorSq_of_closed hC hν hfin hg hy₀,
    fun p s => constrainedAffineErrorSq_lt_top_of_closed hν hg hy₀ p s (hfin p s), ?_⟩
  intro p s hs
  obtain ⟨a₀, B, hB, hmin⟩ := exists_constrained_minimizer hC hν hg hy₀ p s (hfin p s)
  refine ⟨a₀, B, hB, ?_⟩
  simp only [constrainedAffineErrorSq, hs, ↓reduceIte]
  congr 1
  exact le_antisymm (iInf_le_of_le a₀ (iInf_le_of_le B (iInf_le _ hB)))
    (le_iInf fun a => le_iInf fun B' => le_iInf fun hB' => hmin a B' hB')

/-! ## Comparison of the node error with the source error -/

namespace WhitneySourceAllocation

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ} {W : WhitneyData m ι F₀ D a}
  {σ : Measure (Space m)} {A C_B c₂ : ℝ}

theorem nodeFunction_center (S : WhitneySourceAllocation W σ A C_B c₂)
    (coef : ι → Fin (m + 1) → ℝ) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Space m → Y) (j : ι) : S.nodeFunction coef f (W.center j) = S.nodeValue coef f j := by
  unfold nodeFunction
  split_ifs with h
  · congr 1
    exact W.center_injective h.choose_spec
  · exact absurd ⟨j, rfl⟩ h

theorem nodeFunction_of_mem (S : WhitneySourceAllocation W σ A C_B c₂)
    (coef : ι → Fin (m + 1) → ℝ) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Space m → Y) {q : Space m} (hq : q ∈ F₀) : S.nodeFunction coef f q = f q := by
  unfold nodeFunction
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact absurd (by rw [hi]; exact hq) (W.center_notMem i)
  · rfl

end WhitneySourceAllocation

section Comparison

variable {m : ℕ} {ι : Type*} [Countable ι] {F₀ : Set (Space m)} {D a : ℝ}
  {W : WhitneyData m ι F₀ D a} {σ : Measure (Space m)} {A C_B c₂ : ℝ}
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

omit [Countable ι] in
open Classical in
/-- The atoms in `P(p,s)` have total allocated density at most `A`, carried by
`P(a_p, R')`. -/
theorem tsum_ite_density_le (S : WhitneySourceAllocation W σ A C_B c₂) {p ap : Space m}
    {s R' : ℝ}
    (hres : ∀ j, W.center j ∈ Metric.ball p s → ∀ l, S.reservoir j l ⊆ Metric.ball ap R') :
    ∀ᵐ x ∂σ, (∑' j, if W.center j ∈ Metric.ball p s then ∑ l, S.density j l x else 0) ≤
      (Metric.ball ap R').indicator (fun _ => ENNReal.ofReal A) x := by
  classical
  filter_upwards [S.sum_density_le] with x hx
  by_cases hxb : x ∈ Metric.ball ap R'
  · rw [Set.indicator_of_mem hxb]
    refine le_trans ?_ hx
    rw [ENNReal.tsum_prod']
    refine ENNReal.tsum_le_tsum fun j => ?_
    rw [tsum_fintype]
    split_ifs
    · exact le_rfl
    · exact zero_le
  · rw [Set.indicator_of_notMem hxb]
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun j => ?_)
    split_ifs with hj
    · exact Finset.sum_eq_zero fun l _ =>
        S.density_eq_zero j l x fun hxr => hxb (hres j hj l hxr)
    · rfl

/-- The node fit is dominated by the source fit on the enlarged ball about the anchor,
for every affine competitor. -/
theorem nodeFit_le_sourceFit (S : WhitneySourceAllocation W σ A C_B c₂)
    (coef : ι → Fin (m + 1) → ℝ) (f : Space m → Y) {CJ : ℝ} {K₁ : ℝ≥0∞}
    (hF₀m : MeasurableSet F₀) (hdom : (parabolicVolume m).restrict F₀ ≤ K₁ • σ.restrict F₀)
    (a₀ : Y) (B : Spatial m →L[ℝ] Y)
    (hφ : AEMeasurable (fun x => ‖f x - (a₀ + B x.1)‖ₑ ^ 2) σ)
    (hjensen : ∀ i, ENNReal.ofReal (W.radius i ^ (m + 2)) *
        ‖S.nodeValue coef f i - (a₀ + B (W.center i).1)‖ₑ ^ 2 ≤
      ENNReal.ofReal CJ * ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ)
    {p ap : Space m} {s R' : ℝ}
    (hF₀ball : F₀ ∩ Metric.ball p s ⊆ Metric.ball ap R')
    (hres : ∀ j, W.center j ∈ Metric.ball p s → ∀ l, S.reservoir j l ⊆ Metric.ball ap R') :
    affineFitIntegral W.nodeMeasure (S.nodeFunction coef f) a₀ B p s ≤
      (K₁ + ENNReal.ofReal CJ * ENNReal.ofReal A) * affineFitIntegral σ f a₀ B ap R' := by
  classical
  set φf : Space m → ℝ≥0∞ := fun x => ‖f x - (a₀ + B x.1)‖ₑ ^ 2
  unfold affineFitIntegral
  rw [WhitneyData.nodeMeasure, Measure.restrict_add, lintegral_add_measure, add_mul]
  refine add_le_add ?_ ?_
  · -- The continuous part.
    calc ∫⁻ q, ‖S.nodeFunction coef f q - (a₀ + B q.1)‖ₑ ^ 2
          ∂((parabolicVolume m).restrict F₀).restrict (Metric.ball p s)
        = ∫⁻ q, φf q ∂((parabolicVolume m).restrict F₀).restrict (Metric.ball p s) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_of_ae (ae_restrict_mem hF₀m)] with q hq
          rw [S.nodeFunction_of_mem coef f hq]
      _ ≤ ∫⁻ q, φf q ∂(K₁ • σ.restrict F₀).restrict (Metric.ball p s) :=
          lintegral_mono' (Measure.restrict_mono subset_rfl hdom) le_rfl
      _ = K₁ * ∫⁻ q, φf q ∂(σ.restrict F₀).restrict (Metric.ball p s) := by
          rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
      _ ≤ K₁ * ∫⁻ q in Metric.ball ap R', φf q ∂σ := by
          refine mul_le_mul_of_nonneg_left (lintegral_mono' ?_ le_rfl) zero_le
          rw [Measure.restrict_restrict measurableSet_ball]
          exact Measure.restrict_mono (by rw [inter_comm]; exact hF₀ball) le_rfl
  · -- The atoms.
    rw [Measure.restrict_sum _ measurableSet_ball, lintegral_sum_measure]
    have hterm : ∀ j, ∫⁻ q, ‖S.nodeFunction coef f q - (a₀ + B q.1)‖ₑ ^ 2
        ∂(ENNReal.ofReal (W.radius j ^ (m + 2)) • Measure.dirac (W.center j)).restrict
          (Metric.ball p s) ≤
        ENNReal.ofReal CJ *
          (if W.center j ∈ Metric.ball p s then
            ∫⁻ x, ∑ l, φf x * S.density j l x ∂σ else 0) := by
      intro j
      rw [Measure.restrict_smul, lintegral_smul_measure, MeasureTheory.restrict_dirac,
        smul_eq_mul]
      split_ifs with hj
      · rw [lintegral_dirac, S.nodeFunction_center coef f j,
          lintegral_finsetSum' (f := fun l x => φf x * S.density j l x) _
            fun l _ => hφ.mul (S.measurable_density j l).aemeasurable]
        exact hjensen j
      · simp
    have hmeas : ∀ j, AEMeasurable (fun x => if W.center j ∈ Metric.ball p s then
        ∑ l, φf x * S.density j l x else 0) σ := by
      intro j
      split_ifs
      · exact Finset.aemeasurable_fun_sum _ fun l _ =>
          hφ.mul (S.measurable_density j l).aemeasurable
      · exact aemeasurable_const
    have hswap : (∑' j, (if W.center j ∈ Metric.ball p s then
        ∫⁻ x, ∑ l, φf x * S.density j l x ∂σ else 0)) =
        ∫⁻ x, ∑' j, (if W.center j ∈ Metric.ball p s then
          ∑ l, φf x * S.density j l x else 0) ∂σ := by
      rw [lintegral_tsum hmeas]
      refine tsum_congr fun j => ?_
      split_ifs
      · rfl
      · exact lintegral_zero.symm
    have hpoint : ∀ᵐ x ∂σ, (∑' j, (if W.center j ∈ Metric.ball p s then
        ∑ l, φf x * S.density j l x else 0)) ≤
        (Metric.ball ap R').indicator (fun x => ENNReal.ofReal A * φf x) x := by
      filter_upwards [tsum_ite_density_le S hres] with x hx
      have he : (∑' j, (if W.center j ∈ Metric.ball p s then
          ∑ l, φf x * S.density j l x else 0)) =
          φf x * ∑' j, (if W.center j ∈ Metric.ball p s then ∑ l, S.density j l x else 0) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun j => ?_
        split_ifs
        · rw [Finset.mul_sum]
        · rw [mul_zero]
      rw [he]
      by_cases hxb : x ∈ Metric.ball ap R'
      · rw [Set.indicator_of_mem hxb] at hx ⊢
        calc φf x * (∑' j, if W.center j ∈ Metric.ball p s then ∑ l, S.density j l x else 0)
            ≤ φf x * ENNReal.ofReal A := mul_le_mul_of_nonneg_left hx zero_le
          _ = ENNReal.ofReal A * φf x := mul_comm _ _
      · rw [Set.indicator_of_notMem hxb]
        rw [Set.indicator_of_notMem hxb] at hx
        rw [nonpos_iff_eq_zero.mp hx, mul_zero]
    calc ∑' j, ∫⁻ q, ‖S.nodeFunction coef f q - (a₀ + B q.1)‖ₑ ^ 2
          ∂(ENNReal.ofReal (W.radius j ^ (m + 2)) • Measure.dirac (W.center j)).restrict
            (Metric.ball p s)
        ≤ ∑' j, ENNReal.ofReal CJ *
            (if W.center j ∈ Metric.ball p s then
              ∫⁻ x, ∑ l, φf x * S.density j l x ∂σ else 0) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal CJ * ∫⁻ x, ∑' j, (if W.center j ∈ Metric.ball p s then
            ∑ l, φf x * S.density j l x else 0) ∂σ := by
          rw [ENNReal.tsum_mul_left, hswap]
      _ ≤ ENNReal.ofReal CJ *
            ∫⁻ x, (Metric.ball ap R').indicator (fun x => ENNReal.ofReal A * φf x) x ∂σ :=
          mul_le_mul_of_nonneg_left (lintegral_mono_ae hpoint) zero_le
      _ = ENNReal.ofReal CJ * ENNReal.ofReal A * ∫⁻ q in Metric.ball ap R', φf q ∂σ := by
          rw [lintegral_indicator measurableSet_ball,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]

omit [Countable ι] in
/-- The geometry of the node–source comparison: for `p` with `d(p,F₀) ≤ β s` and anchor `a_p`
with `d(p,a_p) ≤ β s`, the continuous part and every allocated reservoir of an atom
in `P(p,s)` lie in `P(a_p, C₁ s)`, `C₁ = 2 + 2β + |C_B| (1+β)/a`. -/
theorem node_geometry (S : WhitneySourceAllocation W σ A C_B c₂) {β : ℝ} (hβ : 0 ≤ β)
    {p ap : Space m} {s : ℝ} (hs : 0 < s) (hpF : Metric.infDist p F₀ ≤ β * s)
    (hpa : dist p ap ≤ β * s) :
    F₀ ∩ Metric.ball p s ⊆ Metric.ball ap ((2 + 2 * β + |C_B| * (1 + β) / |a|) * s) ∧
      ∀ j, W.center j ∈ Metric.ball p s → ∀ l,
        S.reservoir j l ⊆ Metric.ball ap ((2 + 2 * β + |C_B| * (1 + β) / |a|) * s) := by
  have ha : 0 < a := W.a_pos
  rw [abs_of_pos ha]
  have hQ : 0 ≤ |C_B| * (1 + β) / a := by positivity
  constructor
  · rintro x ⟨-, hx⟩
    have hx' := Metric.mem_ball.mp hx
    rw [Metric.mem_ball]
    have := dist_triangle x p ap
    have hQs : 0 ≤ |C_B| * (1 + β) / a * s := mul_nonneg hQ hs.le
    nlinarith [mul_nonneg hβ hs.le]
  · intro j hj l x hx
    have hj' := Metric.mem_ball.mp hj
    have hx' := Metric.mem_ball.mp (S.reservoir_subset j l hx)
    have hrj := W.radius_pos j
    have h1 : a * W.radius j ≤ Metric.infDist (W.center j) F₀ :=
      W.le_infDist j _ (W.center_mem j)
    have h2 : Metric.infDist (W.center j) F₀ ≤ Metric.infDist p F₀ + dist (W.center j) p :=
      Metric.infDist_le_infDist_add_dist
    have h3 : dist (W.center j) (S.anchor j) = Metric.infDist (W.center j) F₀ :=
      S.dist_anchor j
    have harj : a * W.radius j ≤ (1 + β) * s := by nlinarith
    have hCB : C_B * W.radius j ≤ |C_B| * (1 + β) / a * s := by
      have h4 : C_B * W.radius j ≤ |C_B| * W.radius j :=
        mul_le_mul_of_nonneg_right (le_abs_self C_B) hrj.le
      have h5 : |C_B| * W.radius j ≤ |C_B| * (1 + β) / a * s := by
        rw [div_mul_eq_mul_div, le_div_iff₀ ha]
        nlinarith [mul_le_mul_of_nonneg_left harj (abs_nonneg C_B)]
      linarith
    have t1 := dist_triangle x (S.anchor j) ap
    have t2 := dist_triangle (S.anchor j) (W.center j) ap
    have t3 := dist_triangle (W.center j) p ap
    rw [dist_comm (S.anchor j) (W.center j)] at t2
    rw [Metric.mem_ball]
    nlinarith

end Comparison

/-- **Node error against source error** (pointwise form). The constrained node error of
the allocated node function, for every slope bound `L' ≥ C_fit L`, is at most `C` times
the source error `κ_σ` at radius `C₁ s`: at `p ∈ F₀` for every `s > 0`, and at a center
`p_i` for `s ≥ r_i`, about its anchor `a_i`. The three hypotheses are the inputs, instantiated at the
parameters of the statement: the allocated node estimates (`allocated_node_estimates_proof`),
continuous domination (`volume_restrict_le_of_source_density_proof`) and the bounded-slope
source fit (`exists_source_fit_slope_le_proof`). -/
theorem node_error_le_source_error_of_leaves (m : ℕ) (c D a b A C_B c₂ Cm : ℝ) (hc : 0 < c)
    (h3c : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} [Countable ι] {F₀ : Set (Space m)}
      (W : WhitneyData m ι F₀ D a) (σ : Measure (Space m)), σ ≤ parabolicVolume m →
      ∀ (S : WhitneySourceAllocation W σ A C_B c₂) (coef : ι → Fin (m + 1) → ℝ),
        S.IsMomentCoefficients coef Cm →
      ∀ {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
        (f : Space m → Y) (L : ℝ≥0) (T : Set (Space m)),
        σ Tᶜ = 0 → F₀ ⊆ T → LipschitzOnWith L f T →
        (∀ i, ‖S.nodeValue coef f i - f (S.anchor i)‖ ≤ C * L * W.radius i) ∧
        (∀ i (a₀ : Y) (B : Spatial m →L[ℝ] Y),
          ∑ l, coef i l • S.average (fun x => a₀ + B x.1) i l = a₀ + B (W.center i).1) ∧
        ∀ i (a₀ : Y) (B : Spatial m →L[ℝ] Y),
          ENNReal.ofReal (W.radius i ^ (m + 2)) *
              ‖S.nodeValue coef f i - (a₀ + B (W.center i).1)‖ₑ ^ 2 ≤
            ENNReal.ofReal C *
              ∑ l, ∫⁻ x, ‖f x - (a₀ + B x.1)‖ₑ ^ 2 * S.density i l x ∂σ)
    (h3e : ∀ (σ : Measure (Space m)) (_hσ : σ ≤ parabolicVolume m) (F₀ : Set (Space m))
      (_hF₀ : MeasurableSet F₀)
      (_hden : ∀ x ∈ F₀, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)),
      (parabolicVolume m).restrict F₀ ≤ (2 * omega m / ENNReal.ofReal c) • σ.restrict F₀)
    (h1c : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Space m) (R : ℝ) (σ : Measure (Space m)),
      0 < R → σ ≤ parabolicVolume m →
      ENNReal.ofReal (c * R ^ (m + 2)) ≤ σ (Metric.ball x R) →
      ∀ {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
        (f : Space m → Y) (L : ℝ≥0) (T : Set (Space m)),
        σ (Metric.ball x R \ T) = 0 → LipschitzOnWith L f T →
        ∃ (a₀ : Y) (B₀ : Spatial m →L[ℝ] Y), ‖B₀‖ ≤ C * L ∧
          (∀ (a' : Y) (B' : Spatial m →L[ℝ] Y),
            affineFitIntegral σ f a₀ B₀ x R ≤ affineFitIntegral σ f a' B' x R) ∧
          (0 < m → ∀ (a' : Y) (B' : Spatial m →L[ℝ] Y),
            affineFitIntegral σ f a' B' x R = affineFitIntegral σ f a₀ B₀ x R →
              a' = a₀ ∧ B' = B₀)) :
    ∃ C C₁ Cfit : ℝ, 0 ≤ C ∧ 0 < C₁ ∧ 0 ≤ Cfit ∧ ∀ {ι : Type u} [Countable ι]
      {F₀ : Set (Space m)} (W : WhitneyData m ι F₀ D a), IsCompact F₀ → F₀.Nonempty →
      (∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j) →
      ∀ σ : Measure (Space m), σ ≤ parabolicVolume m →
      (∀ x ∈ F₀, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ (m + 2)) ≤ σ (Metric.ball x r)) →
      ∀ (S : WhitneySourceAllocation W σ A C_B c₂) (coef : ι → Fin (m + 1) → ℝ),
        S.IsMomentCoefficients coef Cm →
      ∀ {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
        (f : Space m → Y) (L : ℝ≥0) (T : Set (Space m)), MeasurableSet T →
        σ Tᶜ = 0 → F₀ ⊆ T → LipschitzOnWith L f T →
        ∀ L' : ℝ≥0, Cfit * L ≤ L' →
        (∀ p ∈ F₀, ∀ s : ℝ, 0 < s →
          constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) L' p s ≤
            ENNReal.ofReal C * affineErrorSq σ f p (C₁ * s)) ∧
        ∀ i, ∀ s : ℝ, W.radius i ≤ s →
          constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) L' (W.center i) s ≤
            ENNReal.ofReal C * affineErrorSq σ f (S.anchor i) (C₁ * s) := by
  obtain ⟨CJ, hCJ, hJ⟩ := h3c
  obtain ⟨Cf, hCf, hF⟩ := h1c
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 2 + 2 * |b| + |C_B| * (1 + |b|) / |a| := ⟨_, rfl⟩
  have hC₁pos : 0 < C₁ := by rw [hC₁]; positivity
  have hω : 0 ≤ (omega m).toReal := ENNReal.toReal_nonneg
  have hX : 0 ≤ 2 * (omega m).toReal / c := by positivity
  have hY : 0 ≤ CJ * max A 0 := mul_nonneg hCJ (le_max_right _ _)
  refine ⟨(2 * (omega m).toReal / c + CJ * max A 0) * C₁ ^ (baseDimension (Spatial m) + 2), C₁, Cf,
    mul_nonneg (add_nonneg hX hY) (pow_nonneg hC₁pos.le _), hC₁pos, hCf, ?_⟩
  intro ι _ F₀ W hF₀ hne hb σ hσ hden S coef hcoef Y _ _ _ f L T hTm hTc hF₀T hfL L' hL'
  have hdom := h3e σ hσ F₀ hF₀.isClosed.measurableSet hden
  have hjensen := (hJ W σ hσ S coef hcoef f L T hTc hF₀T hfL).2.2
  have hσT : σ.restrict T = σ := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hTc)
  have hKC : (2 * omega m / ENNReal.ofReal c + ENNReal.ofReal CJ * ENNReal.ofReal A) * ENNReal.ofReal C₁ ^ (baseDimension (Spatial m) + 2) ≤
      ENNReal.ofReal ((2 * (omega m).toReal / c + CJ * max A 0) * C₁ ^ (baseDimension (Spatial m) + 2)) := by
    have e1 : ENNReal.ofReal (2 * (omega m).toReal / c) = 2 * omega m / ENNReal.ofReal c := by
      rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal (omega_lt_top m).ne]
    have e2 : ENNReal.ofReal CJ * ENNReal.ofReal A ≤ ENNReal.ofReal (CJ * max A 0) := by
      rw [ENNReal.ofReal_mul hCJ]
      exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le
    rw [ENNReal.ofReal_mul (add_nonneg hX hY), ENNReal.ofReal_add hX hY, e1,
      ENNReal.ofReal_pow hC₁pos.le]
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl e2) zero_le
  -- The comparison at one center `p` with anchor `ap`.
  have core : ∀ (p ap : Space m) (s : ℝ), 0 < s → Metric.infDist p F₀ ≤ |b| * s →
      dist p ap ≤ |b| * s → ap ∈ F₀ →
      constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) L' p s ≤
        ENNReal.ofReal ((2 * (omega m).toReal / c + CJ * max A 0) * C₁ ^ (baseDimension (Spatial m) + 2)) *
          affineErrorSq σ f ap (C₁ * s) := by
    intro p ap s hs hpF hpa hap
    have hR : 0 < C₁ * s := mul_pos hC₁pos hs
    obtain ⟨hF₀ball, hres⟩ := node_geometry S (abs_nonneg b) hs hpF hpa
    rw [← hC₁] at hF₀ball hres
    obtain ⟨a₀, B₀, hB₀, hmin, -⟩ := hF ap (C₁ * s) σ hR hσ (hden ap hap _ hR) f L T
      (measure_mono_null (fun x hx => hx.2) hTc) hfL
    have hB' : ‖B₀‖ ≤ (L' : ℝ) := hB₀.trans hL'
    have hφ : AEMeasurable (fun x => ‖f x - (a₀ + B₀ x.1)‖ₑ ^ 2) σ := by
      have hcont : ContinuousOn (fun x : Space m => ‖f x - (a₀ + B₀ x.1)‖ₑ ^ 2) T :=
        (ENNReal.continuous_pow 2).comp_continuousOn (hfL.continuousOn.sub
          (continuous_const.add (B₀.continuous.comp continuous_fst)).continuousOn).enorm
      have h := hcont.aemeasurable hTm (μ := σ)
      rwa [hσT] at h
    have hfit := nodeFit_le_sourceFit S coef f hF₀.isClosed.measurableSet hdom a₀ B₀ hφ
      (fun i => hjensen i a₀ B₀) hF₀ball hres
    have hinv : (ENNReal.ofReal s)⁻¹ =
        ENNReal.ofReal C₁ * (ENNReal.ofReal (C₁ * s))⁻¹ := by
      have h0 : ENNReal.ofReal C₁ ≠ 0 := (ENNReal.ofReal_pos.mpr hC₁pos).ne'
      rw [ENNReal.ofReal_mul hC₁pos.le, ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top),
        ← mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_mul]
    have hinf : (⨅ (a' : Y) (B' : Spatial m →L[ℝ] Y), affineFitIntegral σ f a' B' ap (C₁ * s)) =
        affineFitIntegral σ f a₀ B₀ ap (C₁ * s) :=
      le_antisymm (iInf_le_of_le a₀ (iInf_le _ B₀)) (le_iInf₂ fun a' B' => hmin a' B')
    calc constrainedAffineErrorSq W.nodeMeasure (S.nodeFunction coef f) L' p s
        ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
            affineFitIntegral W.nodeMeasure (S.nodeFunction coef f) a₀ B₀ p s :=
          constrainedAffineErrorSq_le_fitIntegral _ _ _ _ hs a₀ B₀ hB'
      _ ≤ (ENNReal.ofReal s)⁻¹ ^ (baseDimension (Spatial m) + 2) *
            ((2 * omega m / ENNReal.ofReal c + ENNReal.ofReal CJ * ENNReal.ofReal A) *
              affineFitIntegral σ f a₀ B₀ ap (C₁ * s)) :=
          mul_le_mul_of_nonneg_left hfit zero_le
      _ = (2 * omega m / ENNReal.ofReal c + ENNReal.ofReal CJ * ENNReal.ofReal A) * ENNReal.ofReal C₁ ^ (baseDimension (Spatial m) + 2) *
            ((ENNReal.ofReal (C₁ * s))⁻¹ ^ (baseDimension (Spatial m) + 2) * affineFitIntegral σ f a₀ B₀ ap (C₁ * s)) := by
          rw [hinv]
          ring
      _ = (2 * omega m / ENNReal.ofReal c + ENNReal.ofReal CJ * ENNReal.ofReal A) * ENNReal.ofReal C₁ ^ (baseDimension (Spatial m) + 2) *
            affineErrorSq σ f ap (C₁ * s) := by
          rw [affineErrorSq_of_pos σ f ap hR, hinf]
      _ ≤ _ := mul_le_mul_of_nonneg_right hKC zero_le
  constructor
  · intro p hp s hs
    have h0 : Metric.infDist p F₀ = 0 := Metric.infDist_zero_of_mem hp
    have hbs : 0 ≤ |b| * s := mul_nonneg (abs_nonneg b) hs.le
    exact core p p s hs (by rw [h0]; exact hbs) (by rw [dist_self]; exact hbs) hp
  · intro i s hs
    have hri := W.radius_pos i
    have hs0 : 0 < s := hri.trans_le hs
    have hbi : Metric.infDist (W.center i) F₀ ≤ |b| * s := by
      have h1 := hb i
      have h2 : b * W.radius i ≤ |b| * W.radius i :=
        mul_le_mul_of_nonneg_right (le_abs_self b) hri.le
      have h3 : |b| * W.radius i ≤ |b| * s := mul_le_mul_of_nonneg_left hs (abs_nonneg b)
      linarith
    exact core (W.center i) (S.anchor i) s hs0 hbi (by rw [S.dist_anchor i]; exact hbi)
      (S.anchor_mem i)

end ParabolicRectifiability
