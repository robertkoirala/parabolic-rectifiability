import ParabolicRectifiability.Geometry.Neck.HoleGrid

/-!
# Collapsed tube cover

`collapsed_children_proof` has the type of `ChargeCollapse.collapsed_children`.

Construction. Let `M` be the lower model (`L × {τ}` or `L × ℝ`, `L` of spatial rank
`m = T.rank k - 1`; its parabolic dimension is `k - 1`). Discard the points of `A`
whose squared distance to `M` is at least `(ρd/2)^2`; by Chebyshev their mass is at most
`K d^{k+2} / (ρd/2)^2 = 4 K d^k / ρ^2`. A retained point `z = (x,t)` has
`|x - P_L x| < ρd/2` (and `|t - τ| < (ρd/2)^2` in the horizontal case). Cells: the
floors of the `m` orthonormal coordinates of `x - x_c` along `L` at spacing
`ρd/(m+1)` (and, vertically, of `(t - t_c)/(ρd)^2`). Two retained points in one cell
are within spatial distance `ρd/2 + ρd + ρd/2 = 2ρd` and time distance below `(ρd)^2`,
hence within `3ρd`. The occupied cells number at most `(2⌈(m+1)/ρ⌉)^m` (times
`2⌈1/ρ^2⌉` vertically), so the count times `ρ^{k-1}` is at most `4 (2n+4)^n`.
Each child is the retained part of one occupied cell, centered at one of its points.
-/

noncomputable section

namespace ParabolicRectifiability

namespace ChargeCollapse

open MeasureTheory Set
open scoped ENNReal

/-- The discarded tube complement of a collapsed assignment and its Chebyshev bound. -/
theorem gm2_collapsed_discard {n : ℕ} (k : ℕ) (μ : Measure (Space n)) {A : Set (Space n)}
    (hA : MeasurableSet A) (M : Set (Space n)) {d K ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ)
    (hint : ∫⁻ z in A, Metric.infEDist z M ^ 2 ∂μ ≤ ENNReal.ofReal (K * d ^ (k + 2))) :
    MeasurableSet (A ∩ {z | ENNReal.ofReal ((ρ * d / 2) ^ 2) ≤ Metric.infEDist z M ^ 2}) ∧
      μ (A ∩ {z | ENNReal.ofReal ((ρ * d / 2) ^ 2) ≤ Metric.infEDist z M ^ 2}) ≤
        ENNReal.ofReal (4 * K * d ^ k / ρ ^ 2) := by
  have hfm : Measurable fun z => Metric.infEDist z M ^ 2 := measurable_infEDist.pow_const 2
  refine ⟨hA.inter (measurableSet_le measurable_const hfm), ?_⟩
  have h := gm2_measure_le_of_lintegral μ hfm (by positivity : 0 < (ρ * d / 2) ^ 2) hint
  have heq : K * d ^ (k + 2) / (ρ * d / 2) ^ 2 = 4 * K * d ^ k / ρ ^ 2 := by
    field_simp
    ring
  rwa [heq] at h

/-- The final count for collapsed holes: `(2⌈(m+1)/ρ⌉)^m ρ^m ≤ (2n+4)^n`
for `m ≤ n`. -/
theorem gm2_collapsed_count {n m : ℕ} (hmn : m ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (2 * (⌈((m : ℝ) + 1) / ρ⌉₊ : ℝ)) ^ m * ρ ^ m ≤ (2 * n + 4) ^ n := by
  have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
  calc (2 * (⌈((m : ℝ) + 1) / ρ⌉₊ : ℝ)) ^ m * ρ ^ m ≤ (2 * ((m : ℝ) + 1 + 1)) ^ m :=
        gm2_pow_bound hρ hρ1 (by positivity) m
    _ ≤ (2 * n + 4) ^ m := by
        gcongr
        linarith
    _ ≤ (2 * n + 4) ^ n := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        hmn

/-- The horizontal case of the collapsed tube cover: `T.rank k - 1 = k - 1`, model `L × {τ}`. -/
theorem gm2_collapsed_horizontal {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (μ : Measure (Space n)) (A : Set (Space n)) (hA : MeasurableSet A)
    (c : Space n) (d : ℝ) (hd : 0 < d) (hAc : A ⊆ Metric.ball c d)
    (L : AffineSpatialPlane n (k - 1)) (τ K : ℝ)
    (hint : ∫⁻ z in A, Metric.infEDist z (NeckType.horizontal.collapseModelSet L τ) ^ 2 ∂μ ≤
      ENNReal.ofReal (K * d ^ (k + 2)))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Hc : HoleChildren μ A (3 * ρ * d),
      μ Hc.discard ≤ ENNReal.ofReal (4 * K * d ^ k / ρ ^ 2) ∧
        (Hc.count : ℝ) * ρ ^ (k - 1) ≤ 4 * (2 * n + 4) ^ n := by
  classical
  set M := NeckType.horizontal.collapseModelSet L τ
  obtain ⟨hDm, hdisc⟩ := gm2_collapsed_discard k μ hA M hd hρ hint
  set D := A ∩ {z | ENNReal.ofReal ((ρ * d / 2) ^ 2) ≤ Metric.infEDist z M ^ 2}
  have hr : 0 < ρ * d / 2 := by positivity
  have hret : ∀ z ∈ A \ D,
      ‖z.1 - L.projection z.1‖ < ρ * d / 2 ∧ |z.2.val - τ| < (ρ * d / 2) ^ 2 := by
    intro z hz
    have hnot : ¬ ENNReal.ofReal ((ρ * d / 2) ^ 2) ≤ Metric.infEDist z M ^ 2 :=
      fun h => hz.2 ⟨hz.1, h⟩
    obtain ⟨w, hw, hzw⟩ := gm2_exists_near M z hr hnot
    have hw' : w.1 ∈ L.toSet ∧ w.2.val = τ := hw
    rw [gm2_dist_eq, max_lt_iff, Real.sqrt_lt' hr] at hzw
    refine ⟨(L.nearest z.1 hw'.1).trans_lt hzw.1, ?_⟩
    rw [← hw'.2]
    exact hzw.2
  set h₀ : ℝ := ρ * d / (((k - 1 : ℕ) : ℝ) + 1) with hh₀
  have hh₀pos : 0 < h₀ := by rw [hh₀]; positivity
  have hmh : ((k - 1 : ℕ) : ℝ) * h₀ ≤ ρ * d := gm2_mul_spacing_le _ (by positivity)
  set N : ℕ := ⌈(((k - 1 : ℕ) : ℝ) + 1) / ρ⌉₊
  let key : Space n → (Fin (Module.finrank ℝ L.direction) → ℤ) := fun z =>
    gm2_cell (gm2_planeBasis L) c.1 h₀ z.1
  have hmeas : Measurable key := gm2_measurable_cell _ _ _ continuous_fst
  set S := Fintype.piFinset fun _ : Fin (Module.finrank ℝ L.direction) =>
    Finset.Ico (-(N : ℤ)) (N : ℤ) with hSdef
  have hS : ∀ z ∈ A \ D, key z ∈ S := by
    intro z hz
    refine gm2_cell_mem (gm2_planeBasis_norm L) hh₀pos (gm2_mem_ball hd (hAc hz.1)).1
      (le_of_eq ?_)
    rw [hh₀]
    field_simp
  have hclose : ∀ z ∈ A \ D, ∀ w ∈ A \ D, key z = key w → dist z w < 3 * ρ * d := by
    intro z hz w hw hzw
    have h1 := gm2_plane_cell_close L hh₀pos hzw (hret z hz).1 (hret w hw).1
    have h2 : |z.2.val - w.2.val| < (ρ * d / 2) ^ 2 + (ρ * d / 2) ^ 2 := by
      calc |z.2.val - w.2.val| ≤ |z.2.val - τ| + |τ - w.2.val| := abs_sub_le _ _ _
        _ < (ρ * d / 2) ^ 2 + (ρ * d / 2) ^ 2 := by
          rw [abs_sub_comm τ]
          exact add_lt_add (hret z hz).2 (hret w hw).2
    have hp : 0 ≤ (ρ * d) ^ 2 := sq_nonneg _
    refine gm2_dist_lt (by positivity) (by linarith) (lt_of_lt_of_le h2 ?_)
    calc (ρ * d / 2) ^ 2 + (ρ * d / 2) ^ 2 = (ρ * d) ^ 2 / 2 := by ring
      _ ≤ 9 * (ρ * d) ^ 2 := by linarith
      _ = (3 * ρ * d) ^ 2 := by ring
  obtain ⟨Hc, hHd, hcount⟩ := gm2_holeChildren_of_key μ hA hDm inter_subset_left key
    (fun a => hmeas (measurableSet_singleton a)) S hS hclose
  refine ⟨Hc, by rw [hHd]; exact hdisc, ?_⟩
  have hcard : S.card = (2 * N) ^ (k - 1) := by
    rw [hSdef, gm2_card_box, L.rank_eq]
  have hc1 : (Hc.count : ℝ) ≤ (2 * (N : ℝ)) ^ (k - 1) := by
    have := hcount.trans hcard.le
    exact_mod_cast this
  have hcnt := gm2_collapsed_count (n := n) (m := k - 1) (by omega) hρ hρ1
  have hpos : 0 ≤ (2 * (n : ℝ) + 4) ^ n := by positivity
  calc (Hc.count : ℝ) * ρ ^ (k - 1) ≤ (2 * (N : ℝ)) ^ (k - 1) * ρ ^ (k - 1) := by gcongr
    _ ≤ (2 * n + 4) ^ n := hcnt
    _ ≤ 4 * (2 * n + 4) ^ n := by linarith

/-- The vertical case of the collapsed tube cover: `T.rank k - 1 = k - 2 - 1`, model `L × ℝ`. -/
theorem gm2_collapsed_vertical {n k : ℕ} (hk1 : 1 ≤ k - 2) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) (A : Set (Space n)) (hA : MeasurableSet A)
    (c : Space n) (d : ℝ) (hd : 0 < d) (hAc : A ⊆ Metric.ball c d)
    (L : AffineSpatialPlane n (k - 2 - 1)) (τ K : ℝ)
    (hint : ∫⁻ z in A, Metric.infEDist z (NeckType.vertical.collapseModelSet L τ) ^ 2 ∂μ ≤
      ENNReal.ofReal (K * d ^ (k + 2)))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Hc : HoleChildren μ A (3 * ρ * d),
      μ Hc.discard ≤ ENNReal.ofReal (4 * K * d ^ k / ρ ^ 2) ∧
        (Hc.count : ℝ) * ρ ^ (k - 1) ≤ 4 * (2 * n + 4) ^ n := by
  classical
  set M := NeckType.vertical.collapseModelSet L τ
  obtain ⟨hDm, hdisc⟩ := gm2_collapsed_discard k μ hA M hd hρ hint
  set D := A ∩ {z | ENNReal.ofReal ((ρ * d / 2) ^ 2) ≤ Metric.infEDist z M ^ 2}
  have hr : 0 < ρ * d / 2 := by positivity
  have hret : ∀ z ∈ A \ D, ‖z.1 - L.projection z.1‖ < ρ * d / 2 := by
    intro z hz
    have hnot : ¬ ENNReal.ofReal ((ρ * d / 2) ^ 2) ≤ Metric.infEDist z M ^ 2 :=
      fun h => hz.2 ⟨hz.1, h⟩
    obtain ⟨w, hw, hzw⟩ := gm2_exists_near M z hr hnot
    have hw' : w.1 ∈ L.toSet := hw
    rw [gm2_dist_eq, max_lt_iff] at hzw
    exact (L.nearest z.1 hw').trans_lt hzw.1
  set h₀ : ℝ := ρ * d / (((k - 2 - 1 : ℕ) : ℝ) + 1) with hh₀
  have hh₀pos : 0 < h₀ := by rw [hh₀]; positivity
  have hmh : ((k - 2 - 1 : ℕ) : ℝ) * h₀ ≤ ρ * d := gm2_mul_spacing_le _ (by positivity)
  have hht : 0 < (ρ * d) ^ 2 := by positivity
  set N : ℕ := ⌈(((k - 2 - 1 : ℕ) : ℝ) + 1) / ρ⌉₊
  set Nt : ℕ := ⌈(1 : ℝ) / ρ ^ 2⌉₊ with hNt
  let key : Space n → (Fin (Module.finrank ℝ L.direction) → ℤ) × ℤ := fun z =>
    (gm2_cell (gm2_planeBasis L) c.1 h₀ z.1, ⌊(z.2.val - c.2.val) / (ρ * d) ^ 2⌋)
  have hmeas : Measurable key :=
    (gm2_measurable_cell _ _ _ continuous_fst).prodMk
      ((measurable_time.sub_const _).div_const _).floor
  set S := (Fintype.piFinset fun _ : Fin (Module.finrank ℝ L.direction) =>
    Finset.Ico (-(N : ℤ)) (N : ℤ)) ×ˢ Finset.Ico (-(Nt : ℤ)) (Nt : ℤ) with hSdef
  have hS : ∀ z ∈ A \ D, key z ∈ S := by
    intro z hz
    have hb := gm2_mem_ball hd (hAc hz.1)
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · refine gm2_cell_mem (gm2_planeBasis_norm L) hh₀pos hb.1 (le_of_eq ?_)
      rw [hh₀]
      field_simp
    · refine gm2_floor_mem_Ico hht hb.2 (le_of_eq ?_)
      field_simp
  have hclose : ∀ z ∈ A \ D, ∀ w ∈ A \ D, key z = key w → dist z w < 3 * ρ * d := by
    intro z hz w hw hzw
    obtain ⟨hzw1, hzw2⟩ := Prod.ext_iff.1 hzw
    have h1 := gm2_plane_cell_close L hh₀pos hzw1 (hret z hz) (hret w hw)
    have h2 := gm2_abs_sub_lt_of_floor_eq hht hzw2
    rw [sub_sub_sub_cancel_right] at h2
    have hp : 0 ≤ (ρ * d) ^ 2 := sq_nonneg _
    refine gm2_dist_lt (by positivity) (by linarith) (lt_of_lt_of_le h2 ?_)
    calc (ρ * d) ^ 2 ≤ 9 * (ρ * d) ^ 2 := by linarith
      _ = (3 * ρ * d) ^ 2 := by ring
  obtain ⟨Hc, hHd, hcount⟩ := gm2_holeChildren_of_key μ hA hDm inter_subset_left key
    (fun a => hmeas (measurableSet_singleton a)) S hS hclose
  refine ⟨Hc, by rw [hHd]; exact hdisc, ?_⟩
  have hcard : S.card = (2 * N) ^ (k - 2 - 1) * (2 * Nt) := by
    rw [hSdef, Finset.card_product, gm2_card_box, gm2_card_Ico, L.rank_eq]
  have hc1 : (Hc.count : ℝ) ≤ (2 * (N : ℝ)) ^ (k - 2 - 1) * (2 * (Nt : ℝ)) := by
    have := hcount.trans hcard.le
    exact_mod_cast this
  have hcnt := gm2_collapsed_count (n := n) (m := k - 2 - 1) (by omega) hρ hρ1
  have htime : (2 * (Nt : ℝ)) * ρ ^ 2 ≤ 4 := by
    have h := gm2_pow_bound (ρ := ρ ^ 2) (y := 1) (by positivity)
      (pow_le_one₀ hρ.le hρ1) zero_le_one 1
    simp only [pow_one] at h
    rw [← hNt] at h
    linarith
  have hk : k - 1 = (k - 2 - 1) + 2 := by omega
  have hB0 : 0 ≤ (2 * (Nt : ℝ)) * ρ ^ 2 := by positivity
  calc (Hc.count : ℝ) * ρ ^ (k - 1)
      ≤ (2 * (N : ℝ)) ^ (k - 2 - 1) * (2 * (Nt : ℝ)) * ρ ^ (k - 1) := by gcongr
    _ = ((2 * (N : ℝ)) ^ (k - 2 - 1) * ρ ^ (k - 2 - 1)) * ((2 * (Nt : ℝ)) * ρ ^ 2) := by
        rw [hk, pow_add]
        ring
    _ ≤ (2 * n + 4) ^ n * 4 := mul_le_mul hcnt htime hB0 (by positivity)
    _ = 4 * (2 * n + 4) ^ n := mul_comm _ _

/-- **Collapsed tube cover.** The type of `ChargeCollapse.collapsed_children`,
with `C = 4 (2n+4)^n`. -/
theorem collapsed_children_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ} {T : NeckType}, T.Available n k → 1 ≤ T.rank k →
      ∀ (μ : Measure (Space n)) [IsFiniteMeasure μ] (A : Set (Space n)), MeasurableSet A →
      ∀ (c : Space n) (d : ℝ), 0 < d → A ⊆ Metric.ball c d →
      ∀ (L : AffineSpatialPlane n (T.rank k - 1)) (τ K : ℝ),
        ∫⁻ z in A, Metric.infEDist z (T.collapseModelSet L τ) ^ 2 ∂μ ≤
          ENNReal.ofReal (K * d ^ (k + 2)) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∃ Hc : HoleChildren μ A (3 * ρ * d),
          μ Hc.discard ≤ ENNReal.ofReal (4 * K * d ^ k / ρ ^ 2) ∧
            (Hc.count : ℝ) * ρ ^ (k - 1) ≤ C := by
  refine ⟨4 * (2 * n + 4) ^ n, by positivity, ?_⟩
  intro k T hT hrank μ _ A hA c d hd hAc L τ K hint ρ hρ hρ1
  cases T with
  | horizontal =>
    obtain ⟨_, hkn⟩ := hT
    exact gm2_collapsed_horizontal hrank hkn μ A hA c d hd hAc L τ K hint ρ hρ hρ1
  | vertical =>
    obtain ⟨_, hkn⟩ := hT
    exact gm2_collapsed_vertical hrank hkn μ A hA c d hd hAc L τ K hint ρ hρ hρ1

end ChargeCollapse

end ParabolicRectifiability
