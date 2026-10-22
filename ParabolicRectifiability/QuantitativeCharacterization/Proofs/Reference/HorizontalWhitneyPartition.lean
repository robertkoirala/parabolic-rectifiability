import ParabolicRectifiability.QuantitativeCharacterization.References
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The quantitative Whitney partition of a horizontal reference

For the statement `ba1_horizontal_interpolation`. Let `H` be a
horizontal reference with domain `D` and Whitney cubes `Q_i` (closed cubes of one translated and
dilated dyadic grid, disjoint interiors, covering `Dᶜ`, `4 diam Q ≤ dist(Q,D) ≤ 10 diam Q`).

* Scales: `s_i = diam Q_i > 0` (positivity from the anchor, whose nearest point would otherwise
  lie in `Q_i ⊆ Dᶜ`), and `s_i ≤ √k ℓ_i` for the side `ℓ_i = λ 2^{j_i}`; the interior of `Q_i`
  has volume at least `ℓ_i^k`.
* Centres: `p_i ∈ Q_i` is the point realizing `dist(Q_i, D) = |p_i - a_i|`.
* At a point `y` with `|y - p_i| < 2 s_i`: `2 s_i ≤ d(y)` and `|y - a_i| ≤ 12 s_i`
  (`b1hint_near`), where `d = dist(·, D)`.
* Packing (`b1hint_card_le`): cubes inside `B(x, 72ρ)` with `s_i ≥ ρ` number at most
  `N_k = |B_1| (72 √k)^k`, by comparing the volumes of their disjoint interiors.
* Local finiteness off `D` (`b1hint_activeSet_finite`): the indices whose cutoff support meets
  `B(x, d(x)/2)` form a finite set of at most `N_k` elements, all with `d(x)/24 ≤ s_i`,
  `|x - a_i| ≤ 10 d(x)` and `Q_i ⊆ B̄(x, 3 d(x))`.
* Cutoffs: `ψ_i(y) = ψ₀((y - p_i)/s_i)` for a fixed smooth bump `ψ₀` (one on the closed unit ball,
  support the open ball of radius two), so `ψ_i = 1` on `Q_i`, `ψ_i = 0` off `B(p_i, 2 s_i)`, and
  `‖∇ψ_i‖ ≤ M_k / s_i` with `M_k = sup ‖∇ψ₀‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace ParabolicRectifiability.QuantitativeCharacterization

variable {n k : ℕ} {L : ℝ}

/-! ### Dyadic cubes -/

/-- The side `λ 2^j` of the Whitney cube `Q_i`. -/
def b1hint_side (H : HorizontalReference n k L) (i : H.cubeIndex) : ℝ :=
  H.gridScale * (2 : ℝ) ^ H.cubeLevel i

theorem b1hint_side_pos (H : HorizontalReference n k L) (i : H.cubeIndex) :
    0 < b1hint_side H i :=
  mul_pos H.gridScale_pos (zpow_pos two_pos _)

theorem b1hint_coord_bounds (H : HorizontalReference n k L) (i : H.cubeIndex) {y : Spatial k}
    (hy : y ∈ H.cube i) (α : Fin k) :
    H.gridOrigin α + b1hint_side H i * (H.cubeCorner i α : ℝ) ≤ y α ∧
      y α ≤ H.gridOrigin α + b1hint_side H i * (H.cubeCorner i α : ℝ) + b1hint_side H i := by
  rw [H.cube_eq i] at hy
  simp only [dyadicCube, Set.mem_ofPred_eq] at hy
  obtain ⟨h1, h2⟩ := hy α
  rw [mul_add, mul_one, ← add_assoc] at h2
  exact ⟨h1, h2⟩

theorem b1hint_abs_coord_sub_le (H : HorizontalReference n k L) (i : H.cubeIndex)
    {y z : Spatial k} (hy : y ∈ H.cube i) (hz : z ∈ H.cube i) (α : Fin k) :
    |y α - z α| ≤ b1hint_side H i := by
  obtain ⟨hy1, hy2⟩ := b1hint_coord_bounds H i hy α
  obtain ⟨hz1, hz2⟩ := b1hint_coord_bounds H i hz α
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem b1hint_dist_le (H : HorizontalReference n k L) (i : H.cubeIndex) {y z : Spatial k}
    (hy : y ∈ H.cube i) (hz : z ∈ H.cube i) : dist y z ≤ √(k : ℝ) * b1hint_side H i := by
  rw [EuclideanSpace.dist_eq]
  calc √(∑ α, dist (y α) (z α) ^ 2) ≤ √(∑ _α : Fin k, b1hint_side H i ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro α _
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (b1hint_abs_coord_sub_le H i hy hz α) 2
    _ = √(k : ℝ) * b1hint_side H i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (b1hint_side_pos H i).le]

theorem b1hint_isBounded (H : HorizontalReference n k L) (i : H.cubeIndex) :
    Bornology.IsBounded (H.cube i) :=
  Metric.isBounded_iff.2 ⟨_, fun _ hy _ hz => b1hint_dist_le H i hy hz⟩

theorem b1hint_diam_le (H : HorizontalReference n k L) (i : H.cubeIndex) :
    Metric.diam (H.cube i) ≤ √(k : ℝ) * b1hint_side H i :=
  Metric.diam_le_of_forall_dist_le (mul_nonneg (Real.sqrt_nonneg _) (b1hint_side_pos H i).le)
    fun _ hy _ hz => b1hint_dist_le H i hy hz

/-- The interior of `Q_i` contains the open box of side `ℓ_i`, of volume `ℓ_i^k`. -/
theorem b1hint_volume_interior_ge (H : HorizontalReference n k L) (i : H.cubeIndex) :
    ENNReal.ofReal (b1hint_side H i ^ k) ≤ volume (interior (H.cube i)) := by
  have hs := b1hint_side_pos H i
  let lo : Fin k → ℝ := fun α => H.gridOrigin α + b1hint_side H i * (H.cubeCorner i α : ℝ)
  have hsub : (WithLp.ofLp ⁻¹' (Set.pi univ fun α => Ioo (lo α) (lo α + b1hint_side H i)) :
      Set (Spatial k)) ⊆ interior (H.cube i) := by
    apply interior_maximal
    · intro y hy
      rw [H.cube_eq i]
      simp only [dyadicCube, Set.mem_ofPred_eq]
      intro α
      have hα := hy α (Set.mem_univ α)
      simp only [lo, Set.mem_Ioo] at hα
      refine ⟨hα.1.le, ?_⟩
      rw [mul_add, mul_one, ← add_assoc]
      exact hα.2.le
    · exact (isOpen_set_pi Set.finite_univ fun α _ => isOpen_Ioo).preimage
        (PiLp.continuous_ofLp 2 (fun _ : Fin k => ℝ))
  have hvol : volume (WithLp.ofLp ⁻¹' (Set.pi univ fun α => Ioo (lo α) (lo α + b1hint_side H i)) :
      Set (Spatial k)) = ENNReal.ofReal (b1hint_side H i ^ k) := by
    rw [(PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
      (MeasurableSet.univ_pi fun α => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow hs.le]
  rw [← hvol]
  exact measure_mono hsub

/-! ### Whitney scales and centres -/

/-- The Whitney scale `s_i = diam Q_i`. -/
def b1hint_scale (H : HorizontalReference n k L) (i : H.cubeIndex) : ℝ :=
  Metric.diam (H.cube i)

/-- The point `p_i ∈ Q_i` with `|p_i - a_i| = dist(Q_i, D)`. -/
def b1hint_center (H : HorizontalReference n k L) (i : H.cubeIndex) : Spatial k :=
  (H.anchor_nearest i).choose

theorem b1hint_center_mem (H : HorizontalReference n k L) (i : H.cubeIndex) :
    b1hint_center H i ∈ H.cube i :=
  (H.anchor_nearest i).choose_spec.1

theorem b1hint_center_dist (H : HorizontalReference n k L) (i : H.cubeIndex) :
    dist (b1hint_center H i) (H.anchor i) = setDist (H.cube i) H.domain :=
  (H.anchor_nearest i).choose_spec.2

theorem b1hint_cube_subset_compl (H : HorizontalReference n k L) (i : H.cubeIndex) :
    H.cube i ⊆ H.domainᶜ := by
  rw [← H.cubes_cover]
  exact subset_iUnion (fun j => H.cube j) i

theorem b1hint_setDist_le (H : HorizontalReference n k L) (i : H.cubeIndex) {y : Spatial k}
    (hy : y ∈ H.cube i) : setDist (H.cube i) H.domain ≤ infDist y H.domain := by
  unfold setDist
  exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact infDist_nonneg⟩ (⟨y, hy⟩ : H.cube i)

theorem b1hint_scale_pos (H : HorizontalReference n k L) (i : H.cubeIndex) :
    0 < b1hint_scale H i := by
  rcases (Metric.diam_nonneg (s := H.cube i)).lt_or_eq with h | h
  · exact h
  · exfalso
    have h1 := H.whitney_upper i
    rw [← h] at h1
    have h2 : dist (b1hint_center H i) (H.anchor i) ≤ 0 := by
      rw [b1hint_center_dist]; linarith
    have h3 : b1hint_center H i = H.anchor i := dist_le_zero.1 h2
    have h4 : b1hint_center H i ∈ H.domain := by rw [h3]; exact H.anchor_mem i
    exact b1hint_cube_subset_compl H i (b1hint_center_mem H i) h4

theorem b1hint_dist_le_scale (H : HorizontalReference n k L) (i : H.cubeIndex)
    {y z : Spatial k} (hy : y ∈ H.cube i) (hz : z ∈ H.cube i) : dist y z ≤ b1hint_scale H i :=
  Metric.dist_le_diam_of_mem (b1hint_isBounded H i) hy hz

/-- Whitney bounds within `2 s_i` of the centre: `2 s_i ≤ d(y)` and `|y - a_i| ≤ 12 s_i`. -/
theorem b1hint_near (H : HorizontalReference n k L) (i : H.cubeIndex) {y : Spatial k}
    (hy : dist y (b1hint_center H i) < 2 * b1hint_scale H i) :
    2 * b1hint_scale H i ≤ infDist y H.domain ∧
      dist y (H.anchor i) ≤ 12 * b1hint_scale H i := by
  have hlow := H.whitney_lower i
  have hup := H.whitney_upper i
  have hp := b1hint_setDist_le H i (b1hint_center_mem H i)
  have htri : infDist (b1hint_center H i) H.domain ≤
      infDist y H.domain + dist (b1hint_center H i) y := infDist_le_infDist_add_dist
  rw [dist_comm] at htri
  have hca := b1hint_center_dist H i
  have htri2 := dist_triangle y (b1hint_center H i) (H.anchor i)
  unfold b1hint_scale at *
  constructor <;> linarith

/-- Near a point `x ∉ D`: every cube whose `2 s_i`-ball around its centre meets
`B(x, d(x)/2)` has `d(x)/24 ≤ s_i`, anchor within `10 d(x)` of `x`, and lies in
`B̄(x, 3 d(x))`. -/
theorem b1hint_active (H : HorizontalReference n k L) {x : Spatial k} (i : H.cubeIndex)
    {y : Spatial k} (hyx : dist y x < infDist x H.domain / 2)
    (hyp : dist y (b1hint_center H i) < 2 * b1hint_scale H i) :
    infDist x H.domain / 24 ≤ b1hint_scale H i ∧
      dist x (H.anchor i) ≤ 10 * infDist x H.domain ∧
      H.cube i ⊆ closedBall x (3 * infDist x H.domain) := by
  obtain ⟨h1, h2⟩ := b1hint_near H i hyp
  have h0 : 0 ≤ dist y x := dist_nonneg
  have h3 : infDist y H.domain ≤ dist y (H.anchor i) := infDist_le_dist_of_mem (H.anchor_mem i)
  have h4 : infDist x H.domain ≤ infDist y H.domain + dist x y := infDist_le_infDist_add_dist
  have h5 : infDist y H.domain ≤ infDist x H.domain + dist y x := infDist_le_infDist_add_dist
  rw [dist_comm x y] at h4
  have h6 := dist_triangle x y (H.anchor i)
  rw [dist_comm x y] at h6
  refine ⟨by linarith, by linarith, ?_⟩
  intro z hz
  rw [mem_closedBall]
  have h7 := b1hint_dist_le_scale H i hz (b1hint_center_mem H i)
  have h8 := dist_triangle z (b1hint_center H i) x
  have h9 := dist_triangle (b1hint_center H i) y x
  rw [dist_comm (b1hint_center H i) y] at h9
  linarith

/-! ### Packing -/

/-- The overlap constant `N_k = |B_1| (72 √k)^k`. -/
def b1hint_overlap (k : ℕ) : ℝ :=
  (volume (closedBall (0 : Spatial k) 1)).toReal * (72 * √(k : ℝ)) ^ k

theorem b1hint_overlap_nonneg (k : ℕ) : 0 ≤ b1hint_overlap k :=
  mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (by positivity) _)

/-- Cubes inside `B̄(x, 72ρ)` with scale at least `ρ` number at most `N_k`. -/
theorem b1hint_card_le (H : HorizontalReference n k L) (x : Spatial k) {ρ : ℝ} (hρ : 0 < ρ)
    (t : Finset H.cubeIndex)
    (ht : ∀ i ∈ t, H.cube i ⊆ closedBall x (72 * ρ) ∧ ρ ≤ b1hint_scale H i) :
    (t.card : ℝ) ≤ b1hint_overlap k := by
  have hk1 : 1 ≤ k := H.available.1
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hcpos : 0 < ρ / √(k : ℝ) := div_pos hρ hsk
  have hvol : ∀ i ∈ t, ENNReal.ofReal ((ρ / √(k : ℝ)) ^ k) ≤ volume (interior (H.cube i)) := by
    intro i hi
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (b1hint_volume_interior_ge H i)
    apply pow_le_pow_left₀ hcpos.le
    rw [div_le_iff₀ hsk]
    calc ρ ≤ b1hint_scale H i := (ht i hi).2
      _ ≤ √(k : ℝ) * b1hint_side H i := b1hint_diam_le H i
      _ = b1hint_side H i * √(k : ℝ) := mul_comm _ _
  have hdisj : (t : Set H.cubeIndex).PairwiseDisjoint fun i => interior (H.cube i) :=
    fun i _ j _ hij => H.cube_interior_disjoint i j hij
  have hU : volume (⋃ i ∈ t, interior (H.cube i)) = ∑ i ∈ t, volume (interior (H.cube i)) :=
    measure_biUnion_finset hdisj fun i _ => isOpen_interior.measurableSet
  have hsub : (⋃ i ∈ t, interior (H.cube i)) ⊆ closedBall x (72 * ρ) :=
    iUnion₂_subset fun i hi => interior_subset.trans (ht i hi).1
  have h72 : (0 : ℝ) ≤ 72 * ρ := by positivity
  have hball : volume (closedBall x (72 * ρ)) =
      ENNReal.ofReal ((72 * ρ) ^ k) * volume (closedBall (0 : Spatial k) 1) := by
    rw [Measure.addHaar_closedBall' volume x h72, finrank_euclideanSpace_fin]
  have hV : volume (closedBall (0 : Spatial k) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have key : (t.card : ℝ≥0∞) * ENNReal.ofReal ((ρ / √(k : ℝ)) ^ k) ≤
      ENNReal.ofReal ((72 * ρ) ^ k) * volume (closedBall (0 : Spatial k) 1) := by
    calc (t.card : ℝ≥0∞) * ENNReal.ofReal ((ρ / √(k : ℝ)) ^ k)
          = ∑ _i ∈ t, ENNReal.ofReal ((ρ / √(k : ℝ)) ^ k) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ t, volume (interior (H.cube i)) := Finset.sum_le_sum hvol
      _ = volume (⋃ i ∈ t, interior (H.cube i)) := hU.symm
      _ ≤ volume (closedBall x (72 * ρ)) := measure_mono hsub
      _ = _ := hball
  rw [← ENNReal.ofReal_toReal hV, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (pow_nonneg h72 k),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg h72 k) ENNReal.toReal_nonneg)] at key
  have h72' : (72 * ρ) ^ k = (72 * √(k : ℝ)) ^ k * (ρ / √(k : ℝ)) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [h72'] at key
  have hck : 0 < (ρ / √(k : ℝ)) ^ k := pow_pos hcpos k
  have key' : (t.card : ℝ) * (ρ / √(k : ℝ)) ^ k ≤ b1hint_overlap k * (ρ / √(k : ℝ)) ^ k := by
    unfold b1hint_overlap
    linarith
  exact le_of_mul_le_mul_right key' hck

/-! ### Local finiteness -/

/-- The indices whose open `2 s_i`-ball around the centre meets `B(x, d(x)/2)`. -/
def b1hint_activeSet (H : HorizontalReference n k L) (x : Spatial k) : Set H.cubeIndex :=
  {i | ∃ y, dist y x < infDist x H.domain / 2 ∧ dist y (b1hint_center H i) < 2 * b1hint_scale H i}

theorem b1hint_infDist_pos (H : HorizontalReference n k L) {x : Spatial k} (hx : x ∉ H.domain) :
    0 < infDist x H.domain :=
  (H.domain_compact.isClosed.notMem_iff_infDist_pos H.domain_nonempty).1 hx

theorem b1hint_activeSet_props (H : HorizontalReference n k L) {x : Spatial k} {i : H.cubeIndex}
    (hi : i ∈ b1hint_activeSet H x) :
    infDist x H.domain / 24 ≤ b1hint_scale H i ∧
      dist x (H.anchor i) ≤ 10 * infDist x H.domain ∧
      H.cube i ⊆ closedBall x (3 * infDist x H.domain) := by
  obtain ⟨y, hyx, hyp⟩ := hi
  exact b1hint_active H i hyx hyp

theorem b1hint_activeSet_finite (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) : (b1hint_activeSet H x).Finite := by
  have hd := b1hint_infDist_pos H hx
  by_contra hinf
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊b1hint_overlap k⌋₊ + 1)
  have hcard := b1hint_card_le H x (ρ := infDist x H.domain / 24) (by positivity) t
    (fun i hi => by
      obtain ⟨h1, -, h3⟩ := b1hint_activeSet_props H (hts (Finset.mem_coe.2 hi))
      refine ⟨?_, h1⟩
      have h72 : 72 * (infDist x H.domain / 24) = 3 * infDist x H.domain := by ring
      rw [h72]
      exact h3)
  rw [htc] at hcard
  push_cast at hcard
  linarith [Nat.lt_floor_add_one (b1hint_overlap k)]

/-- The finite active set near `x ∉ D`, as a finset. -/
def b1hint_activeFinset (H : HorizontalReference n k L) {x : Spatial k} (hx : x ∉ H.domain) :
    Finset H.cubeIndex :=
  (b1hint_activeSet_finite H hx).toFinset

theorem b1hint_mem_activeFinset (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) {i : H.cubeIndex} :
    i ∈ b1hint_activeFinset H hx ↔ i ∈ b1hint_activeSet H x :=
  Set.Finite.mem_toFinset _

theorem b1hint_card_activeFinset_le (H : HorizontalReference n k L) {x : Spatial k}
    (hx : x ∉ H.domain) : ((b1hint_activeFinset H hx).card : ℝ) ≤ b1hint_overlap k := by
  have hd := b1hint_infDist_pos H hx
  refine b1hint_card_le H x (ρ := infDist x H.domain / 24) (by positivity) _ fun i hi => ?_
  obtain ⟨h1, -, h3⟩ := b1hint_activeSet_props H ((b1hint_mem_activeFinset H hx).1 hi)
  refine ⟨?_, h1⟩
  have h72 : 72 * (infDist x H.domain / 24) = 3 * infDist x H.domain := by ring
  rw [h72]
  exact h3

/-! ### The cutoffs -/

/-- The fixed bump `ψ₀ : ℝ^k → [0,1]`: one on the closed unit ball, support the open ball of
radius two. -/
def b1hint_bump (k : ℕ) : ContDiffBump (0 : Spatial k) := ⟨1, 2, one_pos, one_lt_two⟩

theorem b1hint_exists_bump_deriv_bound (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖fderiv ℝ (b1hint_bump k) z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (((b1hint_bump k).contDiff (n := 1)).continuous_fderiv one_ne_zero
    ).bounded_above_of_compact_support
      (HasCompactSupport.fderiv (𝕜 := ℝ) (b1hint_bump k).hasCompactSupport)
  exact ⟨max M 0, le_max_right _ _, fun z => (hM z).trans (le_max_left _ _)⟩

/-- `M_k = sup ‖∇ψ₀‖` (an upper bound, chosen once for each `k`). -/
def b1hint_M (k : ℕ) : ℝ := (b1hint_exists_bump_deriv_bound k).choose

theorem b1hint_M_nonneg (k : ℕ) : 0 ≤ b1hint_M k :=
  (b1hint_exists_bump_deriv_bound k).choose_spec.1

theorem b1hint_norm_fderiv_bump_le (k : ℕ) (z : Spatial k) :
    ‖fderiv ℝ (b1hint_bump k) z‖ ≤ b1hint_M k :=
  (b1hint_exists_bump_deriv_bound k).choose_spec.2 z

/-- The cutoff `ψ_i(y) = ψ₀((y - p_i)/s_i)`. -/
def b1hint_weight (H : HorizontalReference n k L) (i : H.cubeIndex) (y : Spatial k) : ℝ :=
  b1hint_bump k ((b1hint_scale H i)⁻¹ • (y - b1hint_center H i))

theorem b1hint_weight_nonneg (H : HorizontalReference n k L) (i : H.cubeIndex) (y : Spatial k) :
    0 ≤ b1hint_weight H i y :=
  (b1hint_bump k).nonneg

theorem b1hint_norm_smul_sub (H : HorizontalReference n k L) (i : H.cubeIndex) (y : Spatial k) :
    ‖(b1hint_scale H i)⁻¹ • (y - b1hint_center H i)‖ =
      (b1hint_scale H i)⁻¹ * dist y (b1hint_center H i) := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (b1hint_scale_pos H i), ← dist_eq_norm]

theorem b1hint_weight_eq_one (H : HorizontalReference n k L) (i : H.cubeIndex) {y : Spatial k}
    (hy : y ∈ H.cube i) : b1hint_weight H i y = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  have hr : (b1hint_bump k).rIn = 1 := rfl
  rw [mem_closedBall_zero_iff, b1hint_norm_smul_sub, hr, inv_mul_le_iff₀ (b1hint_scale_pos H i),
    mul_one]
  exact b1hint_dist_le_scale H i hy (b1hint_center_mem H i)

theorem b1hint_weight_eq_zero (H : HorizontalReference n k L) (i : H.cubeIndex) {y : Spatial k}
    (hy : 2 * b1hint_scale H i ≤ dist y (b1hint_center H i)) : b1hint_weight H i y = 0 := by
  apply ContDiffBump.zero_of_le_dist
  have hr : (b1hint_bump k).rOut = 2 := rfl
  rw [dist_zero_right, b1hint_norm_smul_sub, hr, le_inv_mul_iff₀ (b1hint_scale_pos H i),
    mul_comm]
  exact hy

theorem b1hint_dist_lt_of_weight_ne_zero (H : HorizontalReference n k L) (i : H.cubeIndex)
    {y : Spatial k} (h : b1hint_weight H i y ≠ 0) :
    dist y (b1hint_center H i) < 2 * b1hint_scale H i := by
  by_contra hc
  exact h (b1hint_weight_eq_zero H i (not_lt.1 hc))

theorem b1hint_contDiff_weight (H : HorizontalReference n k L) (i : H.cubeIndex) :
    ContDiff ℝ 1 (b1hint_weight H i) :=
  ((b1hint_bump k).contDiff (n := 1)).comp
    ((contDiff_id.sub contDiff_const).const_smul (b1hint_scale H i)⁻¹)

theorem b1hint_hasFDerivAt_weight (H : HorizontalReference n k L) (i : H.cubeIndex)
    (y : Spatial k) :
    HasFDerivAt (b1hint_weight H i)
      ((fderiv ℝ (b1hint_bump k) ((b1hint_scale H i)⁻¹ • (y - b1hint_center H i))).comp
        ((b1hint_scale H i)⁻¹ • ContinuousLinearMap.id ℝ (Spatial k))) y := by
  have hin : HasFDerivAt (fun y : Spatial k => (b1hint_scale H i)⁻¹ • (y - b1hint_center H i))
      ((b1hint_scale H i)⁻¹ • ContinuousLinearMap.id ℝ (Spatial k)) y :=
    ((hasFDerivAt_id y).sub_const (b1hint_center H i)).const_smul (b1hint_scale H i)⁻¹
  have hout := (((b1hint_bump k).contDiff (n := 1)).differentiable one_ne_zero
    ((b1hint_scale H i)⁻¹ • (y - b1hint_center H i))).hasFDerivAt
  exact hout.comp y hin

/-- `‖∇ψ_i‖ ≤ M_k / s_i`. -/
theorem b1hint_norm_fderiv_weight_le (H : HorizontalReference n k L) (i : H.cubeIndex)
    (y : Spatial k) : ‖fderiv ℝ (b1hint_weight H i) y‖ ≤ b1hint_M k / b1hint_scale H i := by
  have hs := b1hint_scale_pos H i
  rw [(b1hint_hasFDerivAt_weight H i y).fderiv]
  calc _ ≤ ‖fderiv ℝ (b1hint_bump k) ((b1hint_scale H i)⁻¹ • (y - b1hint_center H i))‖ *
        ‖(b1hint_scale H i)⁻¹ • ContinuousLinearMap.id ℝ (Spatial k)‖ :=
        ContinuousLinearMap.opNorm_comp_le ..
    _ ≤ b1hint_M k * (b1hint_scale H i)⁻¹ := by
        apply mul_le_mul (b1hint_norm_fderiv_bump_le k _) _ (norm_nonneg _) (b1hint_M_nonneg k)
        calc _ ≤ ‖(b1hint_scale H i)⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Spatial k)‖ :=
              norm_smul_le _ _
          _ ≤ (b1hint_scale H i)⁻¹ * 1 := by
              rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
              exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_pos.2 hs).le
          _ = _ := mul_one _
    _ = _ := (div_eq_mul_inv _ _).symm

/-- Off the active set of `x`, the cutoff vanishes on `B(x, d(x)/2)`. -/
theorem b1hint_weight_eq_zero_of_not_mem (H : HorizontalReference n k L) {x : Spatial k}
    {i : H.cubeIndex} (hi : i ∉ b1hint_activeSet H x) {y : Spatial k}
    (hy : dist y x < infDist x H.domain / 2) : b1hint_weight H i y = 0 := by
  by_contra h
  exact hi ⟨y, hy, b1hint_dist_lt_of_weight_ne_zero H i h⟩

end ParabolicRectifiability.QuantitativeCharacterization
