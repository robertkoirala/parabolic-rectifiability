import ParabolicRectifiability.Geometry.Neck.HoleGrid

/-!
# Terminal tube cover

`terminal_children_proof` has the type of `ChargeCollapse.terminal_children`.

Construction. Discard the points of `A` with `d_P(z,L_H)^2 + d_P(z,L_V)^2 ≥ (εd)^2`; by
Chebyshev their mass is at most `K d^k / ε^2 ≤ 2 K d^k / ε^2` (both sides vanish for
`K < 0`). A retained point `z = (x,t)` has `|x - P_V x| < εd` (vertical tube about the
spatial `(k-2)`-plane `V` of `L_V`) and `|t - τ_H| < (εd)^2` (horizontal tube). Cells:
the floors of the `m = k - 2` orthonormal coordinates of `x - x_c` along `V` at spacing
`εd/(2(m+1))`, together with the floors of the `n` standard coordinates of the residual
`x - P_V x` at spacing `εd/(2(n+1))`. Two retained points in one cell satisfy
`|x - x'| ≤ |P_V x - P_V x'| + |(x - P_V x) - (x' - P_V x')| ≤ εd/2 + εd/2` and
`|t - t'| < 2(εd)^2`, so they lie within `2εd`. The plane cells number at most
`(2⌈2(m+1)/ε⌉)^m` and the residual cells at most `(2(2n+3))^n` (the residual has norm
`< εd`), so the count times `ε^{k-2}` is at most `(4n+6)^n (4n+6)^n`. No alignment of
the two planes is used; the horizontal model enters only through its time.
-/

noncomputable section

namespace ParabolicRectifiability

namespace ChargeCollapse

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

/-- **Terminal tube cover.** The type of `ChargeCollapse.terminal_children`,
with `C = (4n+6)^n (4n+6)^n`. -/
theorem terminal_children_proof (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 2 ≤ k → k ≤ n →
      ∀ (μ : Measure (Space n)) [IsFiniteMeasure μ] (A : Set (Space n)), MeasurableSet A →
      ∀ (c : Space n) (d : ℝ), 0 < d → A ⊆ Metric.ball c d →
      ∀ (LH : HorizontalModel n k) (LV : VerticalModel n k) (K : ℝ),
        ∫⁻ z in A, (modelCost (T := .horizontal) LH z + modelCost (T := .vertical) LV z) ∂μ ≤
          ENNReal.ofReal (K * d ^ (k + 2)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ Hc : HoleChildren μ A (2 * ε * d),
          μ Hc.discard ≤ ENNReal.ofReal (2 * K * d ^ k / ε ^ 2) ∧
            (Hc.count : ℝ) * ε ^ (k - 2) ≤ C := by
  refine ⟨(4 * n + 6) ^ n * (4 * n + 6) ^ n, by positivity, ?_⟩
  intro k hk2 hkn μ _ A hA c d hd hAc LH LV K hint ε hε hε1
  classical
  set f : Space n → ℝ≥0∞ := fun z =>
    modelCost (T := .horizontal) LH z + modelCost (T := .vertical) LV z
  have hfm : Measurable f :=
    (measurable_modelCost (T := .horizontal) LH).add (measurable_modelCost (T := .vertical) LV)
  have hr : 0 < ε * d := by positivity
  set D := A ∩ {z | ENNReal.ofReal ((ε * d) ^ 2) ≤ f z}
  have hDm : MeasurableSet D := hA.inter (measurableSet_le measurable_const hfm)
  -- the discarded mass
  have hdisc : μ D ≤ ENNReal.ofReal (2 * K * d ^ k / ε ^ 2) := by
    refine (gm2_measure_le_of_lintegral μ hfm (by positivity : 0 < (ε * d) ^ 2) hint).trans ?_
    have heq : K * d ^ (k + 2) / (ε * d) ^ 2 = K * d ^ k / ε ^ 2 := by
      field_simp
      ring
    rw [heq]
    by_cases hK : 0 ≤ K * d ^ k / ε ^ 2
    · apply ENNReal.ofReal_le_ofReal
      have h2 : 2 * K * d ^ k / ε ^ 2 = 2 * (K * d ^ k / ε ^ 2) := by ring
      linarith
    · rw [ENNReal.ofReal_eq_zero.2 (by linarith)]
      exact zero_le
  -- retained points lie in both tubes
  set m : ℕ := LV.spatialRank with hm
  set P : AffineSpatialPlane n m := LV.spatial
  have hkm : k - 2 = m := by have := LV.rank_eq; omega
  have hmn : m ≤ n := by have := LV.rank_eq; omega
  have hret : ∀ z ∈ A \ D,
      ‖z.1 - P.projection z.1‖ < ε * d ∧ |z.2.val - LH.time| < (ε * d) ^ 2 := by
    intro z hz
    have hlt : f z < ENNReal.ofReal ((ε * d) ^ 2) := not_le.1 fun h => hz.2 ⟨hz.1, h⟩
    have hV : ENNReal.ofReal (‖z.1 - P.projection z.1‖ ^ 2) < ENNReal.ofReal ((ε * d) ^ 2) :=
      (gm2_spatial_le_cost_vertical LV z).trans_lt (le_add_self.trans_lt hlt)
    have hH : ENNReal.ofReal |z.2.val - LH.time| < ENNReal.ofReal ((ε * d) ^ 2) :=
      (gm2_time_le_cost_horizontal LH z).trans_lt (le_self_add.trans_lt hlt)
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hV hH
    exact ⟨lt_of_pow_lt_pow_left₀ 2 hr.le hV, hH⟩
  -- the cells
  set h₁ : ℝ := ε * d / (2 * ((m : ℝ) + 1)) with hh₁
  set h₂ : ℝ := ε * d / (2 * ((n : ℝ) + 1)) with hh₂
  have hh₁pos : 0 < h₁ := by rw [hh₁]; positivity
  have hh₂pos : 0 < h₂ := by rw [hh₂]; positivity
  have hmh₁ : (m : ℝ) * h₁ ≤ ε * d / 2 := by
    have := gm2_mul_spacing_le m (s := ε * d / 2) (by positivity)
    rw [hh₁]
    calc (m : ℝ) * (ε * d / (2 * ((m : ℝ) + 1))) = (m : ℝ) * (ε * d / 2 / ((m : ℝ) + 1)) := by
          rw [div_div]
      _ ≤ ε * d / 2 := this
  have hnh₂ : (n : ℝ) * h₂ ≤ ε * d / 2 := by
    have := gm2_mul_spacing_le n (s := ε * d / 2) (by positivity)
    rw [hh₂]
    calc (n : ℝ) * (ε * d / (2 * ((n : ℝ) + 1))) = (n : ℝ) * (ε * d / 2 / ((n : ℝ) + 1)) := by
          rw [div_div]
      _ ≤ ε * d / 2 := this
  set N₁ : ℕ := ⌈(2 * ((m : ℝ) + 1)) / ε⌉₊
  set N₂ : ℕ := ⌈(2 * ((n : ℝ) + 1))⌉₊
  let e : Fin n → Spatial n := fun j => EuclideanSpace.basisFun (Fin n) ℝ j
  have he : ∀ j, ‖e j‖ ≤ 1 := fun j => ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 j).le
  let key : Space n → (Fin (Module.finrank ℝ P.direction) → ℤ) × (Fin n → ℤ) := fun z =>
    (gm2_cell (gm2_planeBasis P) c.1 h₁ z.1, gm2_cell e 0 h₂ (z.1 - P.projection z.1))
  have hmeas : Measurable key :=
    (gm2_measurable_cell _ _ _ continuous_fst).prodMk
      (gm2_measurable_cell _ _ _
        (continuous_fst.sub (P.continuous_projection.comp continuous_fst)))
  set S := (Fintype.piFinset fun _ : Fin (Module.finrank ℝ P.direction) =>
    Finset.Ico (-(N₁ : ℤ)) (N₁ : ℤ)) ×ˢ
      (Fintype.piFinset fun _ : Fin n => Finset.Ico (-(N₂ : ℤ)) (N₂ : ℤ)) with hSdef
  have hS : ∀ z ∈ A \ D, key z ∈ S := by
    intro z hz
    have hb := gm2_mem_ball hd (hAc hz.1)
    refine Finset.mem_product.2 ⟨?_, ?_⟩
    · refine gm2_cell_mem (gm2_planeBasis_norm P) hh₁pos hb.1 (le_of_eq ?_)
      rw [hh₁]
      field_simp
    · refine gm2_cell_mem he hh₂pos (by rw [sub_zero]; exact (hret z hz).1) (le_of_eq ?_)
      rw [hh₂]
      field_simp
  have hclose : ∀ z ∈ A \ D, ∀ w ∈ A \ D, key z = key w → dist z w < 2 * ε * d := by
    intro z hz w hw hzw
    obtain ⟨hzw1, hzw2⟩ := Prod.ext_iff.1 hzw
    have hp := gm2_projection_close P hh₁pos hzw1
    have hres : ‖(z.1 - P.projection z.1) - (w.1 - P.projection w.1)‖ ≤ n * h₂ := by
      refine (gm2_norm_le_sum (EuclideanSpace.basisFun (Fin n) ℝ) _).trans ?_
      have h := gm2_sum_abs_le fun j => gm2_cell_close hh₂pos hzw2 j
      rwa [Fintype.card_fin] at h
    have hsp : ‖z.1 - w.1‖ ≤ ε * d := by
      have hsplit : z.1 - w.1 = (P.projection z.1 - P.projection w.1) +
          ((z.1 - P.projection z.1) - (w.1 - P.projection w.1)) := by abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      linarith
    have ht : |z.2.val - w.2.val| < (ε * d) ^ 2 + (ε * d) ^ 2 := by
      calc |z.2.val - w.2.val| ≤ |z.2.val - LH.time| + |LH.time - w.2.val| := abs_sub_le _ _ _
        _ < (ε * d) ^ 2 + (ε * d) ^ 2 := by
          rw [abs_sub_comm LH.time]
          exact add_lt_add (hret z hz).2 (hret w hw).2
    have hp2 : 0 ≤ (ε * d) ^ 2 := sq_nonneg _
    refine gm2_dist_lt (by positivity) (by linarith) (lt_of_lt_of_le ht ?_)
    calc (ε * d) ^ 2 + (ε * d) ^ 2 ≤ 4 * (ε * d) ^ 2 := by linarith
      _ = (2 * ε * d) ^ 2 := by ring
  obtain ⟨Hc, hHd, hcount⟩ := gm2_holeChildren_of_key μ hA hDm inter_subset_left key
    (fun a => hmeas (measurableSet_singleton a)) S hS hclose
  refine ⟨Hc, by rw [hHd]; exact hdisc, ?_⟩
  have hcard : S.card = (2 * N₁) ^ m * (2 * N₂) ^ n := by
    rw [hSdef, Finset.card_product, gm2_card_box, gm2_card_box, P.rank_eq]
  have hc1 : (Hc.count : ℝ) ≤ (2 * (N₁ : ℝ)) ^ m * (2 * (N₂ : ℝ)) ^ n := by
    have := hcount.trans hcard.le
    exact_mod_cast this
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hplane : (2 * (N₁ : ℝ)) ^ m * ε ^ m ≤ (4 * n + 6) ^ n := by
    calc (2 * (N₁ : ℝ)) ^ m * ε ^ m ≤ (2 * (2 * ((m : ℝ) + 1) + 1)) ^ m :=
          gm2_pow_bound hε hε1 (by positivity) m
      _ ≤ (4 * n + 6) ^ m := by
          gcongr
          linarith
      _ ≤ (4 * n + 6) ^ n := pow_le_pow_right₀
          (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hmn
  have hres : (2 * (N₂ : ℝ)) ^ n ≤ (4 * n + 6) ^ n := by
    have hc : (N₂ : ℝ) < 2 * ((n : ℝ) + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
    gcongr
    linarith
  rw [hkm]
  calc (Hc.count : ℝ) * ε ^ m ≤ (2 * (N₁ : ℝ)) ^ m * (2 * (N₂ : ℝ)) ^ n * ε ^ m := by gcongr
    _ = ((2 * (N₁ : ℝ)) ^ m * ε ^ m) * (2 * (N₂ : ℝ)) ^ n := by ring
    _ ≤ (4 * n + 6) ^ n * (4 * n + 6) ^ n :=
        mul_le_mul hplane hres (by positivity) (by positivity)

end ChargeCollapse

end ParabolicRectifiability
