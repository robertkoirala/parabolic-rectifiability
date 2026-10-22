import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalADR

/-! # The support of a horizontal reference

The support description used in the proof of `ba1_horizontal_adr`: for every horizontal
`L`-reference,

  `Γ = supp σ = {(F a, τ a) : a ∈ D} ∪ ⋃_i {(F u, τ(a_i)) : u ∈ Q_i}`,

each **closed** cube `Q_i` taken at its own plateau height `τ(a_i)` (not the image
`(F,T)(Q_i)`: a boundary point of `Q_i` whose face is assigned to a neighbour still appears at
height `τ(a_i)`). This is `b1adrh_carrier_eq`.

* `⊇`: trace points by `b1adrh_map_mem_carrier`; closed plateau points by the plateau lower
  bound `b1adrh_lower_plateau` (inward boxes in `int Q_i ⊆ Φ_i`).
* `⊆`: the right side `S` contains the range of `(F,T)` (every base point lies in `D` or in a
  face `Φ_i ⊆ Q_i`), so `σ(Sᶜ) = 0`, and `S` is closed (`b1adrh_isClosed_supportSet`): a limit
  `(x, t)` of points of `S` has `x = F u` (the range of the bi-Lipschitz `F` is closed). If
  `u ∈ D`, the anchors of the approximating cubes approach `u` and their heights converge to
  `τ u` by the anchor bound; if `u ∉ D`, only finitely many cubes meet `B(u, d(u)/2)`
  (`b1adrh_locallyFinite`: their disjoint interiors of volume `≥ (d(u)/(22(k+1)))^k` lie in
  `B(u, d(u))`), so the limit lies on one closed cube at its own plateau height.

The ADR proof does not use this description.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

variable {n k : ℕ} {L : ℝ}

/-- The trace together with the closed plateau faces, each closed cube at its own plateau
height: `{(F a, τ a) : a ∈ D} ∪ ⋃_i {(F u, τ(a_i)) : u ∈ Q_i}`. -/
def b1adrh_supportSet (H : HorizontalReference n k L) : Set (Space n) :=
  H.map '' H.domain ∪
    ⋃ i, (fun u => point (H.spatialMap u) (H.height (H.anchor i))) '' H.cube i

/-! ### Geometry of the cubes -/

theorem b1adrh_isClosed_cube (H : HorizontalReference n k L) (i : H.cubeIndex) :
    IsClosed (H.cube i) := by
  have hset : H.cube i = ⋂ α, ({x : Spatial k | b1adrh_lo H i α ≤ x α} ∩
      {x : Spatial k | x α ≤ b1adrh_lo H i α + b1adrh_side H i}) := by
    ext x
    rw [b1adrh_mem_cube]
    simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun α =>
    (isClosed_le continuous_const (b1adrh_continuous_coord α)).inter
      (isClosed_le (b1adrh_continuous_coord α) continuous_const)

/-- The interior of `Q_i` has volume at least `ℓ_i^k`. -/
theorem b1adrh_volume_interior_ge (H : HorizontalReference n k L) (i : H.cubeIndex) :
    ENNReal.ofReal (b1adrh_side H i ^ k) ≤ volume (interior (H.cube i)) := by
  have hs := b1adrh_side_pos H i
  calc ENNReal.ofReal (b1adrh_side H i ^ k) = ∏ _α : Fin k, ENNReal.ofReal (b1adrh_side H i) := by
        rw [Fin.prod_const, ENNReal.ofReal_pow hs.le]
    _ = ∏ α, volume (Ioo (b1adrh_lo H i α) (b1adrh_lo H i α + b1adrh_side H i)) := by
        refine Finset.prod_congr rfl fun α _ => ?_
        rw [Real.volume_Ioo, add_sub_cancel_left]
    _ = volume {x : Spatial k | ∀ α,
          x α ∈ Ioo (b1adrh_lo H i α) (b1adrh_lo H i α + b1adrh_side H i)} :=
        (b1adrh_volume_box _ fun _ => measurableSet_Ioo).symm
    _ ≤ volume (interior (H.cube i)) := measure_mono (b1adrh_openBox_subset_interior H i)

/-- **Whitney local finiteness away from `D`**: for `u ∉ D`, `d = dist(u,D)`, only finitely
many cubes meet `B(u, d/2)`. Such a cube has side `ℓ_i ≥ d/(22(k+1))` (since
`d/2 < dist(y,D) ≤ 11 diam Q_i ≤ 11 √k ℓ_i` at a common point `y`) and lies in `B(u,d)` (since
`diam Q_i ≤ dist(y,D)/4 < 3d/8`); the interiors are disjoint. -/
theorem b1adrh_locallyFinite (H : HorizontalReference n k L) {u : Spatial k}
    (hu : u ∉ H.domain) :
    {i : H.cubeIndex |
      (H.cube i ∩ Metric.ball u (Metric.infDist u H.domain / 2)).Nonempty}.Finite := by
  have hd : 0 < Metric.infDist u H.domain :=
    (H.domain_compact.isClosed.notMem_iff_infDist_pos H.domain_nonempty).1 hu
  set d := Metric.infDist u H.domain with hd_def
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsq : √(k : ℝ) ≤ (k : ℝ) + 1 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  let As : H.cubeIndex → Set (Spatial k) := fun i => interior (H.cube i) ∩ Metric.ball u d
  have hAm : ∀ i, MeasurableSet (As i) := fun i =>
    isOpen_interior.measurableSet.inter measurableSet_ball
  have hAd : Pairwise (Function.onFun Disjoint As) := fun i j hij =>
    (H.cube_interior_disjoint i j hij).mono inter_subset_left inter_subset_left
  have hAf : volume (⋃ i, As i) ≠ ∞ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume) (x := u) (r := d)).ne
      (measure_mono (iUnion_subset fun i => inter_subset_right))
  have hε : 0 < ENNReal.ofReal ((d / (22 * ((k : ℝ) + 1))) ^ k) :=
    ENNReal.ofReal_pos.2 (by positivity)
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion volume hε hAm hAd hAf).subset ?_
  rintro i ⟨y, hyQ, hyB⟩
  rw [Metric.mem_ball] at hyB
  obtain ⟨x, hx, hxa⟩ := H.anchor_nearest i
  have h1 : d ≤ Metric.infDist y H.domain + dist u y := Metric.infDist_le_infDist_add_dist
  have h2 : Metric.infDist y H.domain ≤ d + dist y u := Metric.infDist_le_infDist_add_dist
  have h3 := b1adrh_setDist_le H i hyQ
  have h4 := H.whitney_lower i
  have h5 := H.whitney_upper i
  have h6 : Metric.infDist y H.domain ≤ dist y (H.anchor i) :=
    Metric.infDist_le_dist_of_mem (H.anchor_mem i)
  have h7 := dist_triangle y x (H.anchor i)
  have h8 : dist y x ≤ Metric.diam (H.cube i) :=
    Metric.dist_le_diam_of_mem (b1adrh_isBounded H i) hyQ hx
  have h9 := b1adrh_diam_le H i
  rw [dist_comm u y] at h1
  have hside : d / (22 * ((k : ℝ) + 1)) ≤ b1adrh_side H i := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 22 * ((k : ℝ) + 1))]
    have h10 : √(k : ℝ) * b1adrh_side H i ≤ ((k : ℝ) + 1) * b1adrh_side H i :=
      mul_le_mul_of_nonneg_right hsq (b1adrh_side_pos H i).le
    linarith
  have hsub : interior (H.cube i) ⊆ Metric.ball u d := by
    intro w hw
    have h11 := Metric.dist_le_diam_of_mem (b1adrh_isBounded H i) (interior_subset hw) hyQ
    have h12 := dist_triangle w y u
    rw [Metric.mem_ball]
    linarith
  show ENNReal.ofReal ((d / (22 * ((k : ℝ) + 1))) ^ k) ≤ volume (As i)
  have hAi : As i = interior (H.cube i) := inter_eq_left.2 hsub
  rw [hAi]
  calc ENNReal.ofReal ((d / (22 * ((k : ℝ) + 1))) ^ k) ≤ ENNReal.ofReal (b1adrh_side H i ^ k) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hside k)
    _ ≤ volume (interior (H.cube i)) := b1adrh_volume_interior_ge H i

/-- The range of the bi-Lipschitz `F` is closed. -/
theorem b1adrh_isClosed_range (H : HorizontalReference n k L) :
    IsClosed (Set.range H.spatialMap) := by
  have hanti : AntilipschitzWith (Real.toNNReal L) H.spatialMap :=
    AntilipschitzWith.of_le_mul_dist fun u v => (H.spatialMap_bilipschitz u v).1.trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg)
  exact hanti.isClosed_range (b1adrh_lipschitz H).uniformContinuous

/-! ### The support set -/

/-- A point of the support set is `(F v, t')` with `v ∈ D`, `t' = τ v`, or `v ∈ Q_i`,
`t' = τ(a_i)`. -/
theorem b1adrh_supportSet_cases (H : HorizontalReference n k L) {b : Space n}
    (hb : b ∈ b1adrh_supportSet H) :
    ∃ v t', b = point (H.spatialMap v) t' ∧
      ((v ∈ H.domain ∧ t' = H.height v) ∨ ∃ i, v ∈ H.cube i ∧ t' = H.height (H.anchor i)) := by
  unfold b1adrh_supportSet at hb
  rcases hb with ⟨v, hv, rfl⟩ | hb
  · exact ⟨v, H.height v, rfl, Or.inl ⟨hv, rfl⟩⟩
  · obtain ⟨i, v, hv, rfl⟩ := mem_iUnion.1 hb
    exact ⟨v, H.height (H.anchor i), rfl, Or.inr ⟨i, hv, rfl⟩⟩

/-- The range of `(F,T)` lies in the support set. -/
theorem b1adrh_map_mem_supportSet (H : HorizontalReference n k L) (v : Spatial k) :
    H.map v ∈ b1adrh_supportSet H := by
  unfold b1adrh_supportSet
  rcases b1adrh_domain_or_face H v with hv | ⟨i, hv⟩
  · exact Or.inl ⟨v, hv, rfl⟩
  · refine Or.inr (mem_iUnion.2 ⟨i, v, H.face_subset_cube i hv, ?_⟩)
    rw [HorizontalReference.map, H.height_plateau i v hv]

/-- Approximation of a point of the closure by points of the support set. -/
theorem b1adrh_approx (H : HorizontalReference n k L) {x : Spatial n} {t : ℝ}
    (hz : point x t ∈ closure (b1adrh_supportSet H)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v t', ‖H.spatialMap v - x‖ < ε ∧ |t' - t| < ε ^ 2 ∧
      ((v ∈ H.domain ∧ t' = H.height v) ∨ ∃ i, v ∈ H.cube i ∧ t' = H.height (H.anchor i)) := by
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hz ε hε
  obtain ⟨v, t', rfl, hcase⟩ := b1adrh_supportSet_cases H hb
  have hmem : point (H.spatialMap v) t' ∈ Metric.ball (point x t) ε := by
    rw [Metric.mem_ball, dist_comm]
    exact hdist
  rw [mem_ball_point _ _ _ _ _ hε] at hmem
  exact ⟨v, t', hmem.1, hmem.2, hcase⟩

/-- **The support set is closed.** -/
theorem b1adrh_isClosed_supportSet (H : HorizontalReference n k L) :
    IsClosed (b1adrh_supportSet H) := by
  have hL := b1adrh_L_pos H
  apply isClosed_of_closure_subset
  rintro ⟨x, ⟨t⟩⟩ hz
  change point x t ∈ closure (b1adrh_supportSet H) at hz
  change point x t ∈ H.map '' H.domain ∪
    ⋃ i, (fun u => point (H.spatialMap u) (H.height (H.anchor i))) '' H.cube i
  -- The spatial limit `x` is `F u`.
  have hx : x ∈ Set.range H.spatialMap := by
    apply (b1adrh_isClosed_range H).closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨v, t', h1, -, -⟩ := b1adrh_approx H hz hε
    exact ⟨H.spatialMap v, ⟨v, rfl⟩, by rw [dist_eq_norm, norm_sub_rev]; exact h1⟩
  obtain ⟨u, rfl⟩ := hx
  -- Approximating base points converge to `u`.
  have hbase : ∀ v : Spatial k, ∀ ε : ℝ, ‖H.spatialMap v - H.spatialMap u‖ < ε →
      dist v u < L * ε := by
    intro v ε h
    rw [← dist_eq_norm] at h
    calc dist v u ≤ L * dist (H.spatialMap v) (H.spatialMap u) :=
          (H.spatialMap_bilipschitz v u).1
      _ < L * ε := mul_lt_mul_of_pos_left h hL
  by_cases hu : u ∈ H.domain
  · -- A trace limit: the time is `τ u`.
    have ht : t = H.height u := by
      by_contra hne
      have hδ : 0 < |t - H.height u| := abs_pos.2 (sub_ne_zero.2 hne)
      have hC : (0 : ℝ) < 1 + 9 * L ^ 4 := by positivity
      obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
          (1 + 9 * L ^ 4) * ε ≤ |t - H.height u| := by
        refine ⟨min 1 (|t - H.height u| / (1 + 9 * L ^ 4)),
          lt_min one_pos (div_pos hδ hC), min_le_left _ _, ?_⟩
        rw [← le_div_iff₀' hC]
        exact min_le_right _ _
      obtain ⟨v, t', h1, h2, hcase⟩ := b1adrh_approx H hz hε
      have hvu := hbase v ε h1
      have h3 : |t' - H.height u| ≤ 9 * L ^ 2 * dist v u ^ 2 := by
        rcases hcase with ⟨_, rfl⟩ | ⟨i, hv, rfl⟩
        · exact b1adrh_height_sub_le H hu v
        · exact b1adrh_anchor_height_sub_le H hu i hv
      have h4 : dist v u ^ 2 ≤ (L * ε) ^ 2 := pow_le_pow_left₀ dist_nonneg hvu.le 2
      have h5 : 9 * L ^ 2 * dist v u ^ 2 ≤ 9 * L ^ 2 * (L * ε) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h6 : |t - H.height u| ≤ |t' - t| + |t' - H.height u| := by
        have := abs_sub (t' - H.height u) (t' - t)
        have he : t' - H.height u - (t' - t) = t - H.height u := by ring
        rw [he] at this
        linarith
      have h7 : ε ^ 2 ≤ ε := by nlinarith
      have h8 : (1 + 9 * L ^ 4) * ε ^ 2 ≤ (1 + 9 * L ^ 4) * ε :=
        mul_le_mul_of_nonneg_left h7 hC.le
      have h9 : 9 * L ^ 2 * (L * ε) ^ 2 = 9 * L ^ 4 * ε ^ 2 := by ring
      linarith
    exact Or.inl ⟨u, hu, by rw [ht, HorizontalReference.map]⟩
  · -- A limit off `D`: one of finitely many closed cubes, at its own plateau height.
    have hd : 0 < Metric.infDist u H.domain :=
      (H.domain_compact.isClosed.notMem_iff_infDist_pos H.domain_nonempty).1 hu
    have hI := b1adrh_locallyFinite H hu
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ {i : H.cubeIndex |
        (H.cube i ∩ Metric.ball u (Metric.infDist u H.domain / 2)).Nonempty},
        (u ∉ H.cube i → L * ε < Metric.infDist u (H.cube i)) ∧
          (t ≠ H.height (H.anchor i) → ε ^ 2 < |t - H.height (H.anchor i)|) := by
      refine (Filter.eventually_all_finite hI).2 fun i _ => ?_
      refine Filter.Eventually.and ?_ ?_
      · by_cases hui : u ∈ H.cube i
        · exact Filter.Eventually.of_forall fun _ h => absurd hui h
        · obtain ⟨x, hx, -⟩ := H.anchor_nearest i
          have hg : 0 < Metric.infDist u (H.cube i) :=
            ((b1adrh_isClosed_cube H i).notMem_iff_infDist_pos ⟨x, hx⟩).1 hui
          filter_upwards [Ioo_mem_nhdsGT (div_pos hg hL)] with ε hε _
          exact (lt_div_iff₀' hL).1 hε.2
      · by_cases hti : t = H.height (H.anchor i)
        · exact Filter.Eventually.of_forall fun _ h => absurd hti h
        · have hδ : 0 < |t - H.height (H.anchor i)| := abs_pos.2 (sub_ne_zero.2 hti)
          filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hδ)] with ε hε _
          have he1 : ε ≤ 1 := hε.2.le.trans (min_le_left _ _)
          have he2 : ε < |t - H.height (H.anchor i)| := hε.2.trans_le (min_le_right _ _)
          have he0 : 0 < ε := hε.1
          nlinarith
    have hsmall : 0 < Metric.infDist u H.domain / (2 * L) := by positivity
    obtain ⟨ε, hP, hε0, hεd⟩ := (hev.and (Ioo_mem_nhdsGT hsmall)).exists
    obtain ⟨v, t', h1, h2, hcase⟩ := b1adrh_approx H hz hε0
    have hvu := hbase v ε h1
    have hLε : L * ε < Metric.infDist u H.domain / 2 := by
      rw [lt_div_iff₀' (by positivity : (0 : ℝ) < 2 * L)] at hεd
      linarith
    have hvu' : dist v u < Metric.infDist u H.domain / 2 := hvu.trans hLε
    rcases hcase with ⟨hv, -⟩ | ⟨i, hv, rfl⟩
    · exfalso
      have := Metric.infDist_le_dist_of_mem (x := u) hv
      rw [dist_comm] at this
      linarith
    · have hiI : (H.cube i ∩ Metric.ball u (Metric.infDist u H.domain / 2)).Nonempty :=
        ⟨v, hv, by rw [Metric.mem_ball]; exact hvu'⟩
      obtain ⟨hP1, hP2⟩ := hP i hiI
      have hui : u ∈ H.cube i := by
        by_contra hui
        have h3 := hP1 hui
        have h4 : Metric.infDist u (H.cube i) ≤ dist u v := Metric.infDist_le_dist_of_mem hv
        rw [dist_comm] at h4
        linarith
      have hti : t = H.height (H.anchor i) := by
        by_contra hti
        have h3 := hP2 hti
        rw [abs_sub_comm] at h3
        linarith
      exact Or.inr (mem_iUnion.2 ⟨i, u, hui, by rw [hti]⟩)

/-! ### The support description -/

/-- `supp σ ⊆ S`: `S` is closed and contains the range of `(F,T)`, so `σ(Sᶜ) = 0`. -/
theorem b1adrh_carrier_subset (H : HorizontalReference n k L) :
    H.carrier ⊆ b1adrh_supportSet H := by
  have hS := b1adrh_isClosed_supportSet H
  rw [HorizontalReference.carrier]
  apply Measure.support_subset_of_isClosed hS
  rw [mem_ae_iff, HorizontalReference.measure,
    Measure.map_apply (b1adrh_measurable_map H) hS.isOpen_compl.measurableSet]
  have he : H.map ⁻¹' (b1adrh_supportSet H)ᶜ = ∅ :=
    eq_empty_iff_forall_notMem.2 fun v hv => hv (b1adrh_map_mem_supportSet H v)
  rw [he, measure_empty]

/-- `S ⊆ supp σ`: trace points by `b1adrh_map_mem_carrier`, closed plateau points by the
plateau lower bound. -/
theorem b1adrh_supportSet_subset (H : HorizontalReference n k L) :
    b1adrh_supportSet H ⊆ H.carrier := by
  have hmeas := b1adrh_measurable_map H
  have hL := b1adrh_L_pos H
  intro z hz
  unfold b1adrh_supportSet at hz
  rcases hz with ⟨u, hu, rfl⟩ | hz
  · exact b1adrh_map_mem_carrier H hu
  · obtain ⟨i, v, hv, rfl⟩ := mem_iUnion.1 hz
    rw [HorizontalReference.carrier, Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
    have hc := b1adrh_lowerConst_pos k hL
    calc (0 : ℝ≥0∞) < ENNReal.ofReal (b1adrh_lowerConst k L * r ^ k) :=
          ENNReal.ofReal_pos.2 (by positivity)
      _ ≤ H.measure (Metric.ball (point (H.spatialMap v) (H.height (H.anchor i))) r) :=
          b1adrh_lower_plateau H hmeas i hv hr
      _ ≤ H.measure U := measure_mono hrU

/-- **Support description**: the closed carrier of a
horizontal `L`-reference is the trace together with the closed plateau faces, each closed cube
`Q_i` at its own plateau height `τ(a_i)`:
`Γ = {(F a, τ a) : a ∈ D} ∪ ⋃_i {(F u, τ(a_i)) : u ∈ Q_i}`. -/
theorem b1adrh_carrier_eq (H : HorizontalReference n k L) :
    H.carrier = H.map '' H.domain ∪
      ⋃ i, (fun u => point (H.spatialMap u) (H.height (H.anchor i))) '' H.cube i :=
  Subset.antisymm (b1adrh_carrier_subset H) (b1adrh_supportSet_subset H)

end ParabolicRectifiability.QuantitativeCharacterization
