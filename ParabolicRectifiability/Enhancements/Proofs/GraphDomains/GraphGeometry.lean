import ParabolicRectifiability.Foundations.GraphDomainCover
import ParabolicRectifiability.Metric.BaseVolume
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.GraphImageBorel

/-! # Per-graph geometry of horizontal and vertical graphs

Proofs of `Enhancements.GraphDomainTree.horizontalGraph_geometry` and `verticalGraph_geometry`,
as `horizontalGraph_geometry_proof` and `verticalGraph_geometry_proof`.

* Whole-image Borelness is taken from the Borel-image facts for graphs
  (`fgenv_horizontal_image_measurableSet_of_isClosed_proof`,
  `fgenv_vertical_image_measurableSet_proof`), together with their continuity facts for
  the two graph maps. Borel images of Borel subsets follow from `Φ(A ∩ D) = Γ ∩ π⁻¹(A)` and
  `Φ(A) = Γ ∩ Π⁻¹(A)`, with the continuous shifted orthogonal projections `π`, `Π` inverting
  the graph maps.
* The two-sided `√2` distance bound (orthogonality) and the two base comparisons are proved here.
  The slope bound is never squared: only `ε * a ≤ a` for `a ≥ 0` and `ε ≤ 1` is used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.GraphDomainTree

open ParabolicRectifiability.Foundations

/-! ## Generic facts -/

/-- If `g ∘ f = v`, then `f '' (v⁻¹ A) = range f ∩ g⁻¹ A`. -/
theorem gdbhv_image_preimage_eq {α β γ : Type*} {f : α → β} {g : β → γ} {v : α → γ}
    (h : ∀ x, g (f x) = v x) (A : Set γ) : f '' (v ⁻¹' A) = range f ∩ g ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by simpa [mem_preimage, h x] using hx⟩
  · rintro ⟨⟨x, rfl⟩, hy⟩
    exact ⟨x, by simpa [mem_preimage, h x] using hy, rfl⟩

/-- Orthogonal sums: `‖x‖ ≤ ‖x + y‖`, and `‖x + y‖ ≤ √2 c` when `‖x‖, ‖y‖ ≤ c`. -/
theorem gdbhv_norm_orthogonal_add {n : ℕ} {K : Submodule ℝ (Spatial n)} {x y : Spatial n}
    (hx : x ∈ K) (hy : y ∈ Kᗮ) :
    ‖x‖ ≤ ‖x + y‖ ∧ ∀ c : ℝ, ‖x‖ ≤ c → ‖y‖ ≤ c → ‖x + y‖ ≤ Real.sqrt 2 * c := by
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y
    (Submodule.inner_right_of_mem_orthogonal hx hy)
  refine ⟨?_, fun c hxc hyc => ?_⟩
  · rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), hp]
    nlinarith [mul_self_nonneg ‖y‖]
  · have hc : 0 ≤ c := le_trans (norm_nonneg _) hxc
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [mul_self_le_mul_self_iff (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hc), hp]
    have hxx := mul_self_le_mul_self (norm_nonneg x) hxc
    have hyy := mul_self_le_mul_self (norm_nonneg y) hyc
    have e : Real.sqrt 2 * c * (Real.sqrt 2 * c) = 2 * (c * c) := by
      rw [show Real.sqrt 2 * c * (Real.sqrt 2 * c) = (Real.sqrt 2 * Real.sqrt 2) * (c * c) by ring,
        h2]
    rw [e]
    linarith

theorem gdbhv_sqrt_two_le_two : (NNReal.sqrt 2 : ℝ≥0∞) ≤ 2 := by
  have : NNReal.sqrt 2 ≤ 2 := NNReal.sqrt_le_iff_le_sq.2 (by norm_num)
  exact_mod_cast this

theorem gdbhv_coe_sqrt_two : ((NNReal.sqrt 2 : ℝ≥0) : ℝ) = Real.sqrt 2 := by
  rw [Real.coe_sqrt]
  norm_num

/-! ## Horizontal graphs -/

section Horizontal

variable {n k : ℕ} {ε : ℝ}

/-- The shifted orthogonal projection `x ↦ P_U(x_spatial - a)`, inverse to the graph map. -/
def gdbhv_horizontalProj (G : HorizontalGraph n k ε) (x : Space n) : G.direction :=
  G.direction.orthogonalProjectionOnto (x.1 - G.offset)

theorem gdbhv_horizontalProj_continuous (G : HorizontalGraph n k ε) :
    Continuous (gdbhv_horizontalProj G) :=
  G.direction.orthogonalProjectionOnto.continuous.comp (continuous_fst.sub continuous_const)

theorem gdbhv_horizontalProj_map (G : HorizontalGraph n k ε) (u : G.domain) :
    gdbhv_horizontalProj G (horizontalGraphMap G u) = (u : G.direction) := by
  have e : (horizontalGraphMap G u).1 - G.offset =
      ((u : G.direction) : Spatial n) + (G.normal u : Spatial n) := by
    simp only [horizontalGraphMap, point]
    abel
  rw [gdbhv_horizontalProj, e, map_add,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (G.normal u).2, add_zero]

theorem gdbhv_horizontalGraphMap_continuous (G : HorizontalGraph n k ε) :
    Continuous (horizontalGraphMap G) :=
  bf1genv2_horizontalMap_continuous G

theorem gdbhv_horizontal_dist (hε : ε ≤ 1) (G : HorizontalGraph n k ε) (u w : G.domain) :
    dist (u : G.direction) (w : G.direction) ≤
        dist (horizontalGraphMap G u) (horizontalGraphMap G w) ∧
      dist (horizontalGraphMap G u) (horizontalGraphMap G w) ≤
        Real.sqrt 2 * dist (u : G.direction) (w : G.direction) := by
  set x : Spatial n := ((u : G.direction) : Spatial n) - ((w : G.direction) : Spatial n) with hx
  set y : Spatial n := (G.normal u : Spatial n) - (G.normal w : Spatial n) with hy
  have hxK : x ∈ G.direction := G.direction.sub_mem (u : G.direction).2 (w : G.direction).2
  have hyK : y ∈ G.directionᗮ := G.directionᗮ.sub_mem (G.normal u).2 (G.normal w).2
  have hd : dist (u : G.direction) (w : G.direction) = ‖x‖ := by
    rw [hx, Subtype.dist_eq, dist_eq_norm]
  have hD : dist (horizontalGraphMap G u) (horizontalGraphMap G w) =
      max ‖x + y‖ (Real.sqrt |G.time u - G.time w|) := by
    have e : G.offset + ((u : G.direction) : Spatial n) + (G.normal u : Spatial n) -
        (G.offset + ((w : G.direction) : Spatial n) + (G.normal w : Spatial n)) = x + y := by
      rw [hx, hy]
      abel
    simp only [horizontalGraphMap]
    rw [dist_point, e]
  have hs := G.small_slope u w
  have hny : ‖y‖ = ‖G.normal u - G.normal w‖ := by rw [hy]; simp
  have hxn : ‖x‖ = ‖((u : G.direction) : Spatial n) - ((w : G.direction) : Spatial n)‖ := by
    rw [hx]
  -- `ε a ≤ a` for `a ≥ 0` and `ε ≤ 1` (the slope bound is not squared)
  have hεx : ε * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) hε
  rw [← hxn] at hs
  have hyx : ‖y‖ ≤ ‖x‖ := by
    rw [hny]; exact le_trans (le_trans (le_max_left _ _) hs) hεx
  have htx : Real.sqrt |G.time u - G.time w| ≤ ‖x‖ :=
    le_trans (le_trans (le_max_right _ _) hs) hεx
  obtain ⟨hlow, hup⟩ := gdbhv_norm_orthogonal_add hxK hyK
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [hd, hD]
  refine ⟨le_trans hlow (le_max_left _ _), max_le (hup _ le_rfl hyx) ?_⟩
  exact le_trans htx (le_mul_of_one_le_left (norm_nonneg _) h1)

theorem gdbhv_horizontal_lipschitz (hε : ε ≤ 1) (G : HorizontalGraph n k ε) :
    LipschitzWith (NNReal.sqrt 2) (horizontalGraphMap G) := by
  refine LipschitzWith.of_dist_le_mul fun u w => ?_
  rw [gdbhv_coe_sqrt_two, Subtype.dist_eq u w]
  exact (gdbhv_horizontal_dist hε G u w).2

theorem gdbhv_horizontal_antilipschitz (hε : ε ≤ 1) (G : HorizontalGraph n k ε) :
    AntilipschitzWith (1 : ℝ≥0)⁻¹ (horizontalGraphMap G) := by
  refine AntilipschitzWith.of_le_mul_dist fun u w => ?_
  rw [inv_one, NNReal.coe_one, one_mul, Subtype.dist_eq u w]
  exact (gdbhv_horizontal_dist hε G u w).1

theorem gdbhv_horizontalPreimage_eq (G : HorizontalGraph n k ε) (F : Set (Space n)) :
    horizontalPreimage G F = Subtype.val '' (horizontalGraphMap G ⁻¹' F) := by
  ext u
  constructor
  · rintro ⟨h, hF⟩
    exact ⟨⟨u, h⟩, hF, rfl⟩
  · rintro ⟨⟨v, h⟩, hF, rfl⟩
    exact ⟨h, hF⟩

theorem horizontalGraph_geometry_proof {n k : ℕ} {ε : ℝ} (hε : ε ≤ 1) (G : HorizontalGraph n k ε)
    (hD : IsClosed G.domain) :
    (∀ F : Set (Space n), MeasurableSet F → MeasurableSet (horizontalPreimage G F)) ∧
    (∀ A : Set G.direction, MeasurableSet A →
      MeasurableSet (horizontalGraphMap G '' {u : G.domain | (u : G.direction) ∈ A})) ∧
    (∀ u w : G.domain,
      dist (u : G.direction) (w : G.direction) ≤
          dist (horizontalGraphMap G u) (horizontalGraphMap G w) ∧
        dist (horizontalGraphMap G u) (horizontalGraphMap G w) ≤
          Real.sqrt 2 * dist (u : G.direction) (w : G.direction)) ∧
    (∀ A : Set G.domain,
      volume (Subtype.val '' A : Set G.direction) ≤
        omega k * hausdorffP n k (horizontalGraphMap G '' A)) ∧
    (∀ A : Set G.domain,
      hausdorffP n k (horizontalGraphMap G '' A) ≤
        2 ^ k * horizontalHausdorffConstant k * volume (Subtype.val '' A : Set G.direction)) := by
  have hcomp := fun E : Set G.direction => horizontal_base_hausdorff_comparison G.direction E
  simp only [G.rank_eq] at hcomp
  refine ⟨fun F hF => ?_, fun A hA => ?_, gdbhv_horizontal_dist hε G, fun A => ?_, fun A => ?_⟩
  · -- (1) `Φ⁻¹(F)` is the image of a Borel subset of the closed (Borel) domain
    rw [gdbhv_horizontalPreimage_eq]
    exact hD.measurableSet.subtype_image
      ((gdbhv_horizontalGraphMap_continuous G).measurable hF)
  · -- (2) `Φ(A ∩ D) = Γ ∩ π⁻¹(A)`, with `Γ` Borel (Borel images of closed-domain horizontal graphs)
    have e : horizontalGraphMap G '' {u : G.domain | (u : G.direction) ∈ A} =
        range (horizontalGraphMap G) ∩ gdbhv_horizontalProj G ⁻¹' A :=
      gdbhv_image_preimage_eq (gdbhv_horizontalProj_map G) A
    rw [e]
    have hΓ : MeasurableSet (range (horizontalGraphMap G)) :=
      fgenv_horizontal_image_measurableSet_of_isClosed_proof n k ε G hD
    exact hΓ.inter ((gdbhv_horizontalProj_continuous G).measurable hA)
  · -- (4) lower comparison
    have hge := hausdorffMeasure_subtype_image_ge (l := 1) one_pos
      (gdbhv_horizontal_antilipschitz hε G) k A
    rw [ENNReal.coe_one, one_pow, one_mul] at hge
    have hlow := (hcomp (Subtype.val '' A)).1
    have h0 : omega k ≠ 0 := (omega_pos k).ne'
    have ht : omega k ≠ ∞ := (omega_lt_top k).ne
    rw [hausdorffP_eq]
    calc volume (Subtype.val '' A : Set G.direction)
        = omega k * ((omega k)⁻¹ * volume (Subtype.val '' A : Set G.direction)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul]
      _ ≤ omega k * Measure.hausdorffMeasure (k : ℝ) (Subtype.val '' A : Set G.direction) := by
          gcongr
      _ ≤ omega k * Measure.hausdorffMeasure (k : ℝ) (horizontalGraphMap G '' A) := by
          gcongr
  · -- (5) upper comparison, `(√2)^k ≤ 2^k`
    have hle := hausdorffMeasure_subtype_image_le (gdbhv_horizontal_lipschitz hε G) k A
    have hup := (hcomp (Subtype.val '' A)).2
    rw [hausdorffP_eq]
    calc Measure.hausdorffMeasure (k : ℝ) (horizontalGraphMap G '' A)
        ≤ (NNReal.sqrt 2 : ℝ≥0∞) ^ k *
            Measure.hausdorffMeasure (k : ℝ) (Subtype.val '' A : Set G.direction) := hle
      _ ≤ (NNReal.sqrt 2 : ℝ≥0∞) ^ k *
            (horizontalHausdorffConstant k * volume (Subtype.val '' A : Set G.direction)) := by
          gcongr
      _ ≤ 2 ^ k * (horizontalHausdorffConstant k * volume (Subtype.val '' A : Set G.direction)) := by
          gcongr
          exact gdbhv_sqrt_two_le_two
      _ = 2 ^ k * horizontalHausdorffConstant k * volume (Subtype.val '' A : Set G.direction) := by
          rw [mul_assoc]

end Horizontal

/-! ## Vertical graphs -/

section Vertical

variable {n k : ℕ} {ε : ℝ}

/-- The shifted projection `x ↦ (P_W(x_spatial - a), x_time)`, inverse to the graph map. -/
def gdbhv_verticalProj (G : GeneralRegularVerticalGraph n k ε) (x : Space n) :
    SubspaceSpace G.direction :=
  (G.direction.orthogonalProjectionOnto (x.1 - G.offset), x.2)

theorem gdbhv_verticalProj_continuous (G : GeneralRegularVerticalGraph n k ε) :
    Continuous (gdbhv_verticalProj G) :=
  (G.direction.orthogonalProjectionOnto.continuous.comp
    (continuous_fst.sub continuous_const)).prodMk continuous_snd

theorem gdbhv_verticalProj_map (G : GeneralRegularVerticalGraph n k ε)
    (p : SubspaceSpace G.direction) : gdbhv_verticalProj G (G.map p) = p := by
  have e : (G.map p).1 - G.offset = (p.1 : Spatial n) + (G.function p : Spatial n) := by
    simp only [GeneralRegularVerticalGraph.map]
    abel
  refine Prod.ext ?_ rfl
  change G.direction.orthogonalProjectionOnto ((G.map p).1 - G.offset) = p.1
  rw [e, map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (G.function p).2, add_zero]

/-- Only the Lipschitz part of the regularity certificate: `Lip G ≤ L ≤ ε ≤ 1`. -/
theorem gdbhv_vertical_function_dist (hε : ε ≤ 1) (G : GeneralRegularVerticalGraph n k ε)
    (p q : SubspaceSpace G.direction) :
    ‖(G.function p : Spatial n) - (G.function q : Spatial n)‖ ≤ dist p q := by
  obtain ⟨g, L, B, hL, -, -, hLB⟩ := G.regular
  have hL1 : (L : ℝ) ≤ 1 := by
    have hB : (0 : ℝ) ≤ B := B.2
    linarith
  have h := hL.dist_le_mul p q
  have hn : ‖(G.function p : Spatial n) - (G.function q : Spatial n)‖ =
      dist (G.function p) (G.function q) := by
    rw [dist_eq_norm]; simp
  rw [hn]
  exact le_trans h (mul_le_of_le_one_left dist_nonneg hL1)

theorem gdbhv_vertical_dist (hε : ε ≤ 1) (G : GeneralRegularVerticalGraph n k ε)
    (p q : SubspaceSpace G.direction) :
    dist p q ≤ dist (G.map p) (G.map q) ∧ dist (G.map p) (G.map q) ≤ Real.sqrt 2 * dist p q := by
  set x : Spatial n := (p.1 : Spatial n) - (q.1 : Spatial n) with hx
  set y : Spatial n := (G.function p : Spatial n) - (G.function q : Spatial n) with hy
  have hxK : x ∈ G.direction := G.direction.sub_mem p.1.2 q.1.2
  have hyK : y ∈ G.directionᗮ := G.directionᗮ.sub_mem (G.function p).2 (G.function q).2
  have hd : dist p q = max ‖x‖ (dist p.2 q.2) := by
    rw [Prod.dist_eq, hx, Subtype.dist_eq, dist_eq_norm]
  have hD : dist (G.map p) (G.map q) = max ‖x + y‖ (dist p.2 q.2) := by
    have e : G.offset + (p.1 : Spatial n) + (G.function p : Spatial n) -
        (G.offset + (q.1 : Spatial n) + (G.function q : Spatial n)) = x + y := by
      rw [hx, hy]
      abel
    simp only [GeneralRegularVerticalGraph.map]
    rw [Prod.dist_eq, dist_eq_norm, e]
  have hyd : ‖y‖ ≤ dist p q := by rw [hy]; exact gdbhv_vertical_function_dist hε G p q
  have hxd : ‖x‖ ≤ dist p q := by rw [hd]; exact le_max_left _ _
  have htd : dist p.2 q.2 ≤ dist p q := by rw [hd]; exact le_max_right _ _
  obtain ⟨hlow, hup⟩ := gdbhv_norm_orthogonal_add hxK hyK
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hD, hd]
    exact max_le_max hlow le_rfl
  · rw [hD]
    exact max_le (hup _ hxd hyd) (le_trans htd (le_mul_of_one_le_left dist_nonneg h1))

theorem gdbhv_vertical_lipschitz (hε : ε ≤ 1) (G : GeneralRegularVerticalGraph n k ε) :
    LipschitzWith (NNReal.sqrt 2) G.map := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [gdbhv_coe_sqrt_two]
  exact (gdbhv_vertical_dist hε G p q).2

theorem gdbhv_vertical_antilipschitz (hε : ε ≤ 1) (G : GeneralRegularVerticalGraph n k ε) :
    AntilipschitzWith 1 G.map := by
  refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
  rw [NNReal.coe_one, one_mul]
  exact (gdbhv_vertical_dist hε G p q).1

theorem verticalGraph_geometry_proof {n k : ℕ} {ε : ℝ} (hε : ε ≤ 1)
    (G : GeneralRegularVerticalGraph n k ε) :
    (∀ F : Set (Space n), MeasurableSet F → MeasurableSet (G.map ⁻¹' F)) ∧
    (∀ A : Set (SubspaceSpace G.direction), MeasurableSet A → MeasurableSet (G.map '' A)) ∧
    (∀ p q : SubspaceSpace G.direction,
      dist p q ≤ dist (G.map p) (G.map q) ∧ dist (G.map p) (G.map q) ≤ Real.sqrt 2 * dist p q) ∧
    (∀ A : Set (SubspaceSpace G.direction),
      intrinsicParabolicVolume G.direction A ≤ 2 * omega (k - 2) * hausdorffP n k (G.map '' A)) ∧
    (∀ A : Set (SubspaceSpace G.direction),
      hausdorffP n k (G.map '' A) ≤
        2 ^ k * verticalHausdorffConstant (k - 2) * intrinsicParabolicVolume G.direction A) := by
  -- `dim W + 2 = k`; at `dim W = 0` the base measure is `dt` and nothing changes below
  have hm : k - 2 = Module.finrank ℝ G.direction := by
    have := G.rank_eq
    omega
  have hcomp := fun E : Set (SubspaceSpace G.direction) =>
    vertical_base_hausdorff_comparison G.direction E
  simp only [G.rank_eq] at hcomp
  rw [hm]
  set m := Module.finrank ℝ G.direction
  refine ⟨fun F hF => (bf1genv2_vertical_map_continuous G).measurable hF, fun A hA => ?_,
    gdbhv_vertical_dist hε G, fun A => ?_, fun A => ?_⟩
  · -- (2) `Φ(A) = Γ ∩ Π⁻¹(A)`, with `Γ` Borel (Borel images of vertical graphs)
    have e : G.map '' A = range G.map ∩ gdbhv_verticalProj G ⁻¹' A :=
      gdbhv_image_preimage_eq (v := id) (gdbhv_verticalProj_map G) A
    rw [e]
    have hΓ : MeasurableSet (range G.map) := fgenv_vertical_image_measurableSet_proof n k ε G
    exact hΓ.inter ((gdbhv_verticalProj_continuous G).measurable hA)
  · -- (4) lower comparison
    have hge := (gdbhv_vertical_antilipschitz hε G).le_hausdorffMeasure_image
      (Nat.cast_nonneg k) A
    rw [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hge
    have hlow := (hcomp A).1
    have h0 : 2 * omega m ≠ 0 := mul_ne_zero two_ne_zero (omega_pos m).ne'
    have ht : 2 * omega m ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (omega_lt_top m).ne
    rw [hausdorffP_eq]
    calc intrinsicParabolicVolume G.direction A
        = 2 * omega m * ((2 * omega m)⁻¹ * intrinsicParabolicVolume G.direction A) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul]
      _ ≤ 2 * omega m * Measure.hausdorffMeasure (k : ℝ) A := by gcongr
      _ ≤ 2 * omega m * Measure.hausdorffMeasure (k : ℝ) (G.map '' A) := by gcongr
  · -- (5) upper comparison, `(√2)^k ≤ 2^k`
    have hle := (gdbhv_vertical_lipschitz hε G).hausdorffMeasure_image_le (Nat.cast_nonneg k) A
    rw [ENNReal.rpow_natCast] at hle
    have hup := (hcomp A).2
    rw [hausdorffP_eq]
    calc Measure.hausdorffMeasure (k : ℝ) (G.map '' A)
        ≤ (NNReal.sqrt 2 : ℝ≥0∞) ^ k * Measure.hausdorffMeasure (k : ℝ) A := hle
      _ ≤ (NNReal.sqrt 2 : ℝ≥0∞) ^ k *
            (verticalHausdorffConstant m * intrinsicParabolicVolume G.direction A) := by
          gcongr
      _ ≤ 2 ^ k * (verticalHausdorffConstant m * intrinsicParabolicVolume G.direction A) := by
          gcongr
          exact gdbhv_sqrt_two_le_two
      _ = 2 ^ k * verticalHausdorffConstant m * intrinsicParabolicVolume G.direction A := by
          rw [mul_assoc]

end Vertical

end ParabolicRectifiability.Enhancements.GraphDomainTree
