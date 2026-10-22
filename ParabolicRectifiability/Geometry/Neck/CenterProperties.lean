import ParabolicRectifiability.Geometry.Neck.Region

/-!
# Elementary properties of the center set of a neck region

For every neck region
`N` with separation constant `c₀`:

* the radius `d` is Lipschitz on the center set with constant `max(1, c₀⁻¹)`;
* the core `𝒞₀ = {d = 0}` is compact;
* for every `a > 0` only finitely many centers have `d_c ≥ a`, so the stopping
  centers `𝒞₊` are countable;
* every convergent sequence of pairwise distinct stopping centers has radii tending
  to zero and its limit in the core;
* the removed set `𝒞₀ ∪ ⋃_{c ∈ 𝒞₊} closure P(c, d_c)` is closed, although it is a
  countable union of closed balls, and the punctured region `𝒩` is open.

Only the center, radius and separation fields of the neck region are used.

For the closedness of the removed set we use that it equals
`{y | ∃ c ∈ 𝒞, d_P(y, c) ≤ d_c}` (a core point is its own center of radius zero).
A limit of such points has centers with a convergent subsequence in the compact
set `𝒞`, and continuity of `d` on `𝒞` passes the inequality to the limit. This is
the case analysis in one step: when the subsequence of centers is
eventually constant one obtains the closed ball of that center, and when it
consists of distinct centers the radii tend to zero and the limit is a core point.
-/

noncomputable section

namespace ParabolicRectifiability

open Filter Topology Set

namespace NeckRegion

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ}
variable (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ)

/-- The elementary Lipschitz inequality `|d_c - d_{c'}| ≤ max(1, c₀⁻¹) d_P(c, c')`
on the center set. -/
theorem abs_radius_sub_le (c : Space n) (hc : c ∈ N.centers) (c' : Space n)
    (hc' : c' ∈ N.centers) :
    |N.radius c - N.radius c'| ≤ max 1 c₀⁻¹ * dist c c' := by
  have hc₀ := N.parameters.c₀_pos
  have hd := dist_nonneg (x := c) (y := c')
  have h₀ := N.radius_nonneg c hc
  have h₀' := N.radius_nonneg c' hc'
  rcases h₀.lt_or_eq with hpos | hzero
  · rcases h₀'.lt_or_eq with hpos' | hzero'
    · -- two stopping centers
      rcases eq_or_ne c c' with rfl | hne
      · simp
      have hsep := N.stop_separation c hc c' hc' hpos hpos' hne
      have hmax : max (N.radius c) (N.radius c') ≤ c₀⁻¹ * dist c c' := by
        rw [inv_mul_eq_div, le_div_iff₀ hc₀, mul_comm]
        exact hsep
      calc |N.radius c - N.radius c'| ≤ max (N.radius c) (N.radius c') :=
            abs_sub_le_iff.2 ⟨by linarith [le_max_left (N.radius c) (N.radius c')],
              by linarith [le_max_right (N.radius c) (N.radius c')]⟩
        _ ≤ c₀⁻¹ * dist c c' := hmax
        _ ≤ max 1 c₀⁻¹ * dist c c' :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hd
    · -- `c` stopping, `c'` in the core
      have hsep := N.core_separation c hc hpos c' hc' hzero'.symm
      rw [← hzero', sub_zero, abs_of_nonneg h₀]
      calc N.radius c ≤ dist c c' := hsep
        _ = 1 * dist c c' := (one_mul _).symm
        _ ≤ max 1 c₀⁻¹ * dist c c' := mul_le_mul_of_nonneg_right (le_max_left _ _) hd
  · rcases h₀'.lt_or_eq with hpos' | hzero'
    · -- `c` in the core, `c'` stopping
      have hsep := N.core_separation c' hc' hpos' c hc hzero.symm
      rw [← hzero, zero_sub, abs_neg, abs_of_nonneg h₀', dist_comm]
      calc N.radius c' ≤ dist c' c := hsep
        _ = 1 * dist c' c := (one_mul _).symm
        _ ≤ max 1 c₀⁻¹ * dist c' c := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    · -- two core points
      rw [← hzero, ← hzero', sub_self, abs_zero]
      exact mul_nonneg (le_max_of_le_left zero_le_one) hd

/-- The radius is Lipschitz on `𝒞` with constant `max(1, c₀⁻¹)`. -/
theorem lipschitzOnWith_radius :
    LipschitzOnWith (Real.toNNReal (max 1 c₀⁻¹)) N.radius N.centers := by
  refine LipschitzOnWith.of_dist_le_mul fun c hc c' hc' => ?_
  rw [Real.coe_toNNReal _ (le_max_of_le_left zero_le_one), Real.dist_eq]
  exact N.abs_radius_sub_le c hc c' hc'

theorem continuousOn_radius : ContinuousOn N.radius N.centers :=
  N.lipschitzOnWith_radius.continuousOn

theorem isClosed_centers : IsClosed N.centers :=
  N.isCompact_centers.isClosed

theorem core_subset_centers : N.core ⊆ N.centers := fun _ hc => hc.1

theorem stopping_subset_centers : N.stopping ⊆ N.centers := fun _ hc => hc.1

/-- The core `{c ∈ 𝒞 : d_c = 0}` is compact. -/
theorem isCompact_core : IsCompact N.core :=
  N.isCompact_centers.of_isClosed_subset
    (N.continuousOn_radius.preimage_isClosed_of_isClosed N.isClosed_centers isClosed_singleton)
    N.core_subset_centers

/-- For `a > 0`, the centers with `d_c ≥ a` are `c₀ a`-separated in the compact set `𝒞`,
hence finitely many. -/
theorem finite_setOf_le_radius {a : ℝ} (ha : 0 < a) :
    {c | c ∈ N.centers ∧ a ≤ N.radius c}.Finite := by
  have hc₀ := N.parameters.c₀_pos
  have hε : 0 < c₀ * a / 2 := by positivity
  obtain ⟨t, ht, hcover⟩ :=
    Metric.totallyBounded_iff.1 N.isCompact_centers.totallyBounded _ hε
  -- choose, for each center, a point of the finite net within `c₀ a / 2`
  have hchoose : ∀ c ∈ N.centers, ∃ y ∈ t, dist c y < c₀ * a / 2 := by
    intro c hc
    obtain ⟨y, hy, hcy⟩ := mem_iUnion₂.1 (hcover hc)
    exact ⟨y, hy, hcy⟩
  classical
  let f : Space n → Space n := fun c =>
    if hc : c ∈ N.centers then Classical.choose (hchoose c hc) else c
  have hf : ∀ c (hc : c ∈ N.centers), f c ∈ t ∧ dist c (f c) < c₀ * a / 2 := by
    intro c hc
    simp only [f, hc, ↓reduceDIte]
    exact Classical.choose_spec (hchoose c hc)
  refine Set.Finite.of_finite_image (f := f) (ht.subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact (hf c hc.1).1
  · intro c hc c' hc' hcc'
    by_contra hne
    have hpos : 0 < N.radius c := ha.trans_le hc.2
    have hpos' : 0 < N.radius c' := ha.trans_le hc'.2
    have hsep := N.stop_separation c hc.1 c' hc'.1 hpos hpos' hne
    have h1 := (hf c hc.1).2
    have h2 := (hf c' hc'.1).2
    rw [hcc'] at h1
    have hlt : dist c c' < c₀ * a := by
      calc dist c c' ≤ dist c (f c') + dist c' (f c') := dist_triangle_right _ _ _
        _ < c₀ * a / 2 + c₀ * a / 2 := add_lt_add h1 h2
        _ = c₀ * a := add_halves _
    have hge : c₀ * a ≤ c₀ * max (N.radius c) (N.radius c') :=
      mul_le_mul_of_nonneg_left (le_max_of_le_left hc.2) hc₀.le
    exact absurd (hge.trans hsep) (not_le.2 hlt)

/-- The stopping centers `𝒞₊` are countable. -/
theorem countable_stopping : N.stopping.Countable := by
  have hsub : N.stopping ⊆ ⋃ l : ℕ, {c | c ∈ N.centers ∧ 1 / ((l : ℝ) + 1) ≤ N.radius c} := by
    rintro c ⟨hc, hpos⟩
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt hpos
    exact mem_iUnion.2 ⟨l, hc, hl.le⟩
  refine (countable_iUnion fun l => ?_).mono hsub
  exact (N.finite_setOf_le_radius (by positivity)).countable

/-- A convergent sequence of pairwise distinct (`c` injective)
stopping centers has radii tending to zero and its limit in the core. -/
theorem tendsto_radius_zero_and_mem_core {c : ℕ → Space n} {z : Space n}
    (hc : ∀ i, c i ∈ N.stopping) (hinj : Function.Injective c)
    (hlim : Tendsto c atTop (𝓝 z)) :
    Tendsto (fun i => N.radius (c i)) atTop (𝓝 0) ∧ z ∈ N.core := by
  have hrad : Tendsto (fun i => N.radius (c i)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro a ha
    -- only finitely many indices have radius at least `a`
    have hfin : {i | a ≤ N.radius (c i)}.Finite := by
      have := (N.finite_setOf_le_radius ha).preimage (f := c) hinj.injOn
      exact this.subset fun i hi => ⟨(hc i).1, hi⟩
    obtain ⟨M, hM⟩ := hfin.bddAbove
    refine ⟨M + 1, fun i hi => ?_⟩
    have hlt : N.radius (c i) < a := by
      by_contra hle
      have := hM (not_lt.1 hle)
      omega
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (N.radius_nonneg _ (hc i).1)]
    exact hlt
  refine ⟨hrad, ?_⟩
  have hz : z ∈ N.centers :=
    N.isClosed_centers.mem_of_tendsto hlim (Eventually.of_forall fun i => (hc i).1)
  have hcont : Tendsto (fun i => N.radius (c i)) atTop (𝓝 (N.radius z)) :=
    ((N.continuousOn_radius z hz).tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => (hc i).1⟩)
  exact ⟨hz, tendsto_nhds_unique hcont hrad⟩

/-- The removed set `𝒞₀ ∪ ⋃_{c ∈ 𝒞₊} closure P(c, d_c)`. -/
def removedSet : Set (Space n) :=
  N.core ∪ ⋃ c ∈ N.stopping, Metric.closedBall c (N.radius c)

theorem regionSet_eq : N.regionSet = Metric.ball q R \ N.removedSet := rfl

/-- The removed set consists of the points within `d_c` of some center `c`. -/
theorem removedSet_eq : N.removedSet = {y | ∃ c ∈ N.centers, dist y c ≤ N.radius c} := by
  ext y
  simp only [removedSet, mem_union, mem_iUnion, Metric.mem_closedBall, mem_ofPred_eq,
    exists_prop]
  constructor
  · rintro (hy | ⟨c, hc, hyc⟩)
    · exact ⟨y, hy.1, by simp [hy.2]⟩
    · exact ⟨c, hc.1, hyc⟩
  · rintro ⟨c, hc, hyc⟩
    rcases (N.radius_nonneg c hc).lt_or_eq with hpos | hzero
    · exact Or.inr ⟨c, ⟨hc, hpos⟩, hyc⟩
    · rw [← hzero] at hyc
      have : y = c := dist_le_zero.1 hyc
      subst this
      exact Or.inl ⟨hc, hzero.symm⟩

/-- The removed set is closed, although it is a countable union of closed balls together
with the core. -/
theorem isClosed_removedSet : IsClosed N.removedSet := by
  rw [removedSet_eq]
  refine IsSeqClosed.isClosed ?_
  intro y p hy hyp
  simp only [mem_ofPred_eq] at hy ⊢
  choose c hc hyc using hy
  obtain ⟨c', hc', φ, hφ, hlim⟩ := N.isCompact_centers.tendsto_subseq hc
  refine ⟨c', hc', ?_⟩
  have hrad : Tendsto (fun i => N.radius (c (φ i))) atTop (𝓝 (N.radius c')) :=
    ((N.continuousOn_radius c' hc').tendsto).comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => hc (φ i)⟩)
  have hdist : Tendsto (fun i => dist (y (φ i)) (c (φ i))) atTop (𝓝 (dist p c')) :=
    (hyp.comp hφ.tendsto_atTop).dist hlim
  exact le_of_tendsto_of_tendsto' hdist hrad fun i => hyc (φ i)

/-- The punctured region `𝒩` is open. -/
theorem isOpen_regionSet : IsOpen N.regionSet :=
  Metric.isOpen_ball.sdiff N.isClosed_removedSet

end NeckRegion

end ParabolicRectifiability
