import ParabolicRectifiability.QuantitativeCharacterization.References

/-! # Dyadic cube geometry for the Whitney plateau completion 

Infrastructure for `b2_whitney_plateau_completion`. We work on the standard dyadic grid of `ℝ^k` (origin `0`, scale `1`), i.e. the cubes
`dyadicCube 0 1 j m` of the reference models:

* membership, closedness, boundedness, compactness, nonemptiness;
* the exact diameter `diam Q = 2^j √k`;
* the interior of a closed cube lies in the open box;
* the dyadic nesting property: if the open box of one cube meets another closed cube, the
  finer of the two closed cubes lies in the coarser (and at equal levels they coincide);
* every point lies in a cube of each level, and every cube lies in its parent.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

variable {k : ℕ}

/-- The standard dyadic cube of level `j` and corner `m`: `dyadicCube 0 1 j m`. -/
abbrev b2plat_cube (j : ℤ) (m : Fin k → ℤ) : Set (Spatial k) :=
  dyadicCube (0 : Spatial k) 1 j m

theorem b2plat_mem_cube_iff {j : ℤ} {m : Fin k → ℤ} {x : Spatial k} :
    x ∈ b2plat_cube j m ↔
      ∀ α, (2 : ℝ) ^ j * (m α : ℝ) ≤ x α ∧ x α ≤ (2 : ℝ) ^ j * ((m α : ℝ) + 1) := by
  simp only [b2plat_cube, dyadicCube, Set.mem_ofPred_eq, one_mul, PiLp.zero_apply, zero_add]

theorem b2plat_side_pos (j : ℤ) : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos two_pos j

theorem b2plat_dist_le {j : ℤ} {m : Fin k → ℤ} {x y : Spatial k}
    (hx : x ∈ b2plat_cube j m) (hy : y ∈ b2plat_cube j m) :
    dist x y ≤ (2 : ℝ) ^ j * √(k : ℝ) := by
  rw [b2plat_mem_cube_iff] at hx hy
  have hs := (b2plat_side_pos j).le
  rw [EuclideanSpace.dist_eq]
  calc √(∑ α, dist (x α) (y α) ^ 2) ≤ √(∑ _α : Fin k, ((2 : ℝ) ^ j) ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro α _
        obtain ⟨h1, h2⟩ := hx α
        obtain ⟨h3, h4⟩ := hy α
        have e : (2 : ℝ) ^ j * ((m α : ℝ) + 1) = (2 : ℝ) ^ j * (m α : ℝ) + (2 : ℝ) ^ j := by
          ring
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) 2
    _ = (2 : ℝ) ^ j * √(k : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq hs, mul_comm]

/-- The lower corner of a cube. -/
def b2plat_lo (j : ℤ) (m : Fin k → ℤ) : Spatial k :=
  WithLp.toLp 2 (fun α => (2 : ℝ) ^ j * (m α : ℝ))

/-- The upper corner of a cube. -/
def b2plat_hi (j : ℤ) (m : Fin k → ℤ) : Spatial k :=
  WithLp.toLp 2 (fun α => (2 : ℝ) ^ j * ((m α : ℝ) + 1))

theorem b2plat_lo_mem (j : ℤ) (m : Fin k → ℤ) : b2plat_lo j m ∈ b2plat_cube j m := by
  rw [b2plat_mem_cube_iff]
  intro α
  simp only [b2plat_lo, PiLp.toLp_apply]
  have hs := b2plat_side_pos j
  constructor
  · exact le_rfl
  · nlinarith

theorem b2plat_hi_mem (j : ℤ) (m : Fin k → ℤ) : b2plat_hi j m ∈ b2plat_cube j m := by
  rw [b2plat_mem_cube_iff]
  intro α
  simp only [b2plat_hi, PiLp.toLp_apply]
  have hs := b2plat_side_pos j
  constructor
  · nlinarith
  · exact le_rfl

theorem b2plat_cube_nonempty (j : ℤ) (m : Fin k → ℤ) : (b2plat_cube j m).Nonempty :=
  ⟨_, b2plat_lo_mem j m⟩

theorem b2plat_dist_lo_hi (j : ℤ) (m : Fin k → ℤ) :
    dist (b2plat_lo (k := k) j m) (b2plat_hi j m) = (2 : ℝ) ^ j * √(k : ℝ) := by
  have hs := b2plat_side_pos j
  have h : ∀ α, dist (b2plat_lo (k := k) j m α) (b2plat_hi j m α) ^ 2 = ((2 : ℝ) ^ j) ^ 2 := by
    intro α
    simp only [b2plat_lo, b2plat_hi, PiLp.toLp_apply, Real.dist_eq]
    rw [show (2 : ℝ) ^ j * (m α : ℝ) - (2 : ℝ) ^ j * ((m α : ℝ) + 1) = -((2 : ℝ) ^ j) by ring,
      abs_neg, abs_of_pos hs]
  rw [EuclideanSpace.dist_eq, Finset.sum_congr rfl (fun α _ => h α), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg k),
    Real.sqrt_sq hs.le, mul_comm]

theorem b2plat_isBounded (j : ℤ) (m : Fin k → ℤ) : Bornology.IsBounded (b2plat_cube j m) :=
  Metric.isBounded_iff.2 ⟨_, fun _ hx _ hy => b2plat_dist_le hx hy⟩

/-- The exact diameter `diam Q = 2^j √k`. -/
theorem b2plat_diam (j : ℤ) (m : Fin k → ℤ) :
    Metric.diam (b2plat_cube j m) = (2 : ℝ) ^ j * √(k : ℝ) := by
  have hs := b2plat_side_pos j
  refine le_antisymm (Metric.diam_le_of_forall_dist_le (by positivity)
    fun x hx y hy => b2plat_dist_le hx hy) ?_
  rw [← b2plat_dist_lo_hi j m]
  exact Metric.dist_le_diam_of_mem (b2plat_isBounded j m) (b2plat_lo_mem j m) (b2plat_hi_mem j m)

theorem b2plat_diam_pos (hk : 1 ≤ k) (j : ℤ) (m : Fin k → ℤ) :
    0 < Metric.diam (b2plat_cube j m) := by
  rw [b2plat_diam]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact mul_pos (b2plat_side_pos j) (Real.sqrt_pos.2 hk')

theorem b2plat_coord_continuous (α : Fin k) : Continuous fun x : Spatial k => x α := by
  fun_prop

theorem b2plat_isClosed (j : ℤ) (m : Fin k → ℤ) : IsClosed (b2plat_cube j m) := by
  have e : b2plat_cube (k := k) j m = ⋂ α, ({x : Spatial k | (2 : ℝ) ^ j * (m α : ℝ) ≤ x α} ∩
      {x : Spatial k | x α ≤ (2 : ℝ) ^ j * ((m α : ℝ) + 1)}) := by
    ext x
    simp only [b2plat_mem_cube_iff, mem_iInter, mem_inter_iff, mem_ofPred_eq]
  rw [e]
  exact isClosed_iInter fun α =>
    (isClosed_le continuous_const (b2plat_coord_continuous α)).inter
      (isClosed_le (b2plat_coord_continuous α) continuous_const)

theorem b2plat_isCompact (j : ℤ) (m : Fin k → ℤ) : IsCompact (b2plat_cube j m) :=
  Metric.isCompact_of_isClosed_isBounded (b2plat_isClosed j m) (b2plat_isBounded j m)

/-- The interior of a closed cube lies in the open box. -/
theorem b2plat_open_of_mem_interior {j : ℤ} {m : Fin k → ℤ} {x : Spatial k}
    (hx : x ∈ interior (b2plat_cube j m)) :
    ∀ α, (2 : ℝ) ^ j * (m α : ℝ) < x α ∧ x α < (2 : ℝ) ^ j * ((m α : ℝ) + 1) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
  obtain ⟨ε, hε, hball⟩ := hx
  intro α
  have key : ∀ c : ℝ, |c| < ε → x - PiLp.single 2 α c ∈ b2plat_cube j m := by
    intro c hc
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, PiLp.norm_single,
      Real.norm_eq_abs]
    exact hc
  have hcoord : ∀ c : ℝ, (x - PiLp.single 2 α c : Spatial k) α = x α - c := by
    intro c
    rw [PiLp.sub_apply, PiLp.single_eq_same]
  have hε2 : |ε / 2| < ε := by
    rw [abs_of_pos (by positivity)]
    linarith
  have hε2' : |-(ε / 2)| < ε := by rwa [abs_neg]
  have h1 := ((b2plat_mem_cube_iff.1 (key (ε / 2) hε2)) α).1
  have h2 := ((b2plat_mem_cube_iff.1 (key (-(ε / 2)) hε2')) α).2
  rw [hcoord] at h1 h2
  constructor <;> linarith

/-- Every point lies in the cube of level `j` with corner `⌊x / 2^j⌋`. -/
theorem b2plat_mem_floor_cube (j : ℤ) (x : Spatial k) :
    x ∈ b2plat_cube j (fun α => ⌊x α / (2 : ℝ) ^ j⌋) := by
  rw [b2plat_mem_cube_iff]
  intro α
  have hs := b2plat_side_pos j
  have e : (2 : ℝ) ^ j * (x α / (2 : ℝ) ^ j) = x α := by field_simp
  constructor
  · calc (2 : ℝ) ^ j * (⌊x α / (2 : ℝ) ^ j⌋ : ℝ) ≤ (2 : ℝ) ^ j * (x α / (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left (Int.floor_le _) hs.le
      _ = x α := e
  · calc x α = (2 : ℝ) ^ j * (x α / (2 : ℝ) ^ j) := e.symm
      _ ≤ (2 : ℝ) ^ j * ((⌊x α / (2 : ℝ) ^ j⌋ : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (Int.lt_floor_add_one _).le hs.le

/-- One-dimensional nesting, open fine interval against a closed coarse interval. -/
theorem b2plat_int_nest_A {a t : ℝ} {N m1 m2 : ℤ} (ha : 0 < a)
    (h1 : a * (m1 : ℝ) < t) (h2 : t < a * ((m1 : ℝ) + 1))
    (h3 : a * (N : ℝ) * (m2 : ℝ) ≤ t) (h4 : t ≤ a * (N : ℝ) * ((m2 : ℝ) + 1)) :
    N * m2 ≤ m1 ∧ m1 + 1 ≤ N * (m2 + 1) := by
  rw [mul_assoc] at h3 h4
  have e1 : ((N * m2 : ℤ) : ℝ) < ((m1 + 1 : ℤ) : ℝ) := by
    push_cast
    exact lt_of_mul_lt_mul_left (h3.trans_lt h2) ha.le
  have e2 : ((m1 : ℤ) : ℝ) < ((N * (m2 + 1) : ℤ) : ℝ) := by
    push_cast
    exact lt_of_mul_lt_mul_left (h1.trans_le h4) ha.le
  have f1 := Int.cast_lt.1 e1
  have f2 := Int.cast_lt.1 e2
  constructor <;> omega

/-- One-dimensional nesting, open coarse interval against a closed fine interval. -/
theorem b2plat_int_nest_B {a t : ℝ} {N m1 m2 : ℤ} (ha : 0 < a)
    (h1 : a * (N : ℝ) * (m1 : ℝ) < t) (h2 : t < a * (N : ℝ) * ((m1 : ℝ) + 1))
    (h3 : a * (m2 : ℝ) ≤ t) (h4 : t ≤ a * ((m2 : ℝ) + 1)) :
    N * m1 ≤ m2 ∧ m2 + 1 ≤ N * (m1 + 1) := by
  rw [mul_assoc] at h1 h2
  have e1 : ((N * m1 : ℤ) : ℝ) < ((m2 + 1 : ℤ) : ℝ) := by
    push_cast
    exact lt_of_mul_lt_mul_left (h1.trans_le h4) ha.le
  have e2 : ((m2 : ℤ) : ℝ) < ((N * (m1 + 1) : ℤ) : ℝ) := by
    push_cast
    exact lt_of_mul_lt_mul_left (h3.trans_lt h2) ha.le
  have f1 := Int.cast_lt.1 e1
  have f2 := Int.cast_lt.1 e2
  constructor <;> omega

theorem b2plat_zpow_exists {j1 j2 : ℤ} (h : j1 ≤ j2) :
    ∃ N : ℤ, (2 : ℝ) ^ j2 = (2 : ℝ) ^ j1 * (N : ℝ) := by
  refine ⟨(2 : ℤ) ^ (j2 - j1).toNat, ?_⟩
  rw [Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 h),
    ← zpow_add₀ two_ne_zero, show j1 + (j2 - j1) = j2 by ring]

/-- If the open box of a cube at level `j1` meets a closed cube at a level `j2 ≥ j1`, the
first closed cube lies in the second. -/
theorem b2plat_subset_of_open_mem_le {j1 j2 : ℤ} {m1 m2 : Fin k → ℤ} (hj : j1 ≤ j2)
    {x : Spatial k}
    (hx : ∀ α, (2 : ℝ) ^ j1 * (m1 α : ℝ) < x α ∧ x α < (2 : ℝ) ^ j1 * ((m1 α : ℝ) + 1))
    (hx2 : x ∈ b2plat_cube j2 m2) : b2plat_cube j1 m1 ⊆ b2plat_cube j2 m2 := by
  obtain ⟨N, hN⟩ := b2plat_zpow_exists hj
  have ha := b2plat_side_pos j1
  intro y hy
  rw [b2plat_mem_cube_iff] at hx2 hy ⊢
  intro α
  obtain ⟨h1, h2⟩ := hx α
  obtain ⟨h3, h4⟩ := hx2 α
  rw [hN] at h3 h4 ⊢
  obtain ⟨c1, c2⟩ := b2plat_int_nest_A ha h1 h2 h3 h4
  have c1' : ((N * m2 α : ℤ) : ℝ) ≤ ((m1 α : ℤ) : ℝ) := Int.cast_le.2 c1
  have c2' : ((m1 α + 1 : ℤ) : ℝ) ≤ ((N * (m2 α + 1) : ℤ) : ℝ) := Int.cast_le.2 c2
  push_cast at c1' c2'
  obtain ⟨h5, h6⟩ := hy α
  constructor
  · calc (2 : ℝ) ^ j1 * (N : ℝ) * (m2 α : ℝ) = (2 : ℝ) ^ j1 * ((N : ℝ) * (m2 α : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ j1 * (m1 α : ℝ) := mul_le_mul_of_nonneg_left c1' ha.le
      _ ≤ y α := h5
  · calc y α ≤ (2 : ℝ) ^ j1 * ((m1 α : ℝ) + 1) := h6
      _ ≤ (2 : ℝ) ^ j1 * ((N : ℝ) * ((m2 α : ℝ) + 1)) := mul_le_mul_of_nonneg_left c2' ha.le
      _ = (2 : ℝ) ^ j1 * (N : ℝ) * ((m2 α : ℝ) + 1) := by ring

/-- If the open box of a cube at level `j1` meets a closed cube at a level `j2 ≤ j1`, the
second closed cube lies in the first. -/
theorem b2plat_subset_of_open_mem_ge {j1 j2 : ℤ} {m1 m2 : Fin k → ℤ} (hj : j2 ≤ j1)
    {x : Spatial k}
    (hx : ∀ α, (2 : ℝ) ^ j1 * (m1 α : ℝ) < x α ∧ x α < (2 : ℝ) ^ j1 * ((m1 α : ℝ) + 1))
    (hx2 : x ∈ b2plat_cube j2 m2) : b2plat_cube j2 m2 ⊆ b2plat_cube j1 m1 := by
  obtain ⟨N, hN⟩ := b2plat_zpow_exists hj
  have ha := b2plat_side_pos j2
  intro y hy
  rw [b2plat_mem_cube_iff] at hx2 hy ⊢
  intro α
  obtain ⟨h1, h2⟩ := hx α
  obtain ⟨h3, h4⟩ := hx2 α
  rw [hN] at h1 h2 ⊢
  obtain ⟨c1, c2⟩ := b2plat_int_nest_B ha h1 h2 h3 h4
  have c1' : ((N * m1 α : ℤ) : ℝ) ≤ ((m2 α : ℤ) : ℝ) := Int.cast_le.2 c1
  have c2' : ((m2 α + 1 : ℤ) : ℝ) ≤ ((N * (m1 α + 1) : ℤ) : ℝ) := Int.cast_le.2 c2
  push_cast at c1' c2'
  obtain ⟨h5, h6⟩ := hy α
  constructor
  · calc (2 : ℝ) ^ j2 * (N : ℝ) * (m1 α : ℝ) = (2 : ℝ) ^ j2 * ((N : ℝ) * (m1 α : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ j2 * (m2 α : ℝ) := mul_le_mul_of_nonneg_left c1' ha.le
      _ ≤ y α := h5
  · calc y α ≤ (2 : ℝ) ^ j2 * ((m2 α : ℝ) + 1) := h6
      _ ≤ (2 : ℝ) ^ j2 * ((N : ℝ) * ((m1 α : ℝ) + 1)) := mul_le_mul_of_nonneg_left c2' ha.le
      _ = (2 : ℝ) ^ j2 * (N : ℝ) * ((m1 α : ℝ) + 1) := by ring

/-- At equal levels, an open box meeting a closed cube forces equal corners. -/
theorem b2plat_eq_of_open_mem {j : ℤ} {m1 m2 : Fin k → ℤ} {x : Spatial k}
    (hx : ∀ α, (2 : ℝ) ^ j * (m1 α : ℝ) < x α ∧ x α < (2 : ℝ) ^ j * ((m1 α : ℝ) + 1))
    (hx2 : x ∈ b2plat_cube j m2) : m1 = m2 := by
  funext α
  rw [b2plat_mem_cube_iff] at hx2
  obtain ⟨h1, h2⟩ := hx α
  obtain ⟨h3, h4⟩ := hx2 α
  have ha := b2plat_side_pos j
  have h3' : (2 : ℝ) ^ j * ((1 : ℤ) : ℝ) * (m2 α : ℝ) ≤ x α := by simpa using h3
  have h4' : x α ≤ (2 : ℝ) ^ j * ((1 : ℤ) : ℝ) * ((m2 α : ℝ) + 1) := by simpa using h4
  obtain ⟨c1, c2⟩ := b2plat_int_nest_A ha h1 h2 h3' h4'
  omega

/-- The parent of a cube: level `j + 1`, corner `⌊m / 2⌋`. -/
theorem b2plat_subset_parent (j : ℤ) (m : Fin k → ℤ) :
    b2plat_cube j m ⊆ b2plat_cube (j + 1) (fun α => m α / 2) := by
  intro y hy
  rw [b2plat_mem_cube_iff] at hy ⊢
  intro α
  obtain ⟨h5, h6⟩ := hy α
  have e : (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := zpow_add_one₀ two_ne_zero j
  have c1 : ((2 * (m α / 2) : ℤ) : ℝ) ≤ ((m α : ℤ) : ℝ) := Int.cast_le.2 (by omega)
  have c2 : ((m α + 1 : ℤ) : ℝ) ≤ ((2 * (m α / 2 + 1) : ℤ) : ℝ) := Int.cast_le.2 (by omega)
  push_cast at c1 c2
  have ha := b2plat_side_pos j
  rw [e]
  constructor
  · calc (2 : ℝ) ^ j * 2 * ((m α / 2 : ℤ) : ℝ) = (2 : ℝ) ^ j * (2 * ((m α / 2 : ℤ) : ℝ)) := by
          ring
      _ ≤ (2 : ℝ) ^ j * (m α : ℝ) := mul_le_mul_of_nonneg_left c1 ha.le
      _ ≤ y α := h5
  · calc y α ≤ (2 : ℝ) ^ j * ((m α : ℝ) + 1) := h6
      _ ≤ (2 : ℝ) ^ j * (2 * (((m α / 2 : ℤ) : ℝ) + 1)) := mul_le_mul_of_nonneg_left c2 ha.le
      _ = (2 : ℝ) ^ j * 2 * (((m α / 2 : ℤ) : ℝ) + 1) := by ring

/-- The parent has twice the diameter. -/
theorem b2plat_diam_parent (j : ℤ) (m : Fin k → ℤ) :
    Metric.diam (b2plat_cube (j + 1) (fun α => m α / 2)) = 2 * Metric.diam (b2plat_cube j m) := by
  rw [b2plat_diam, b2plat_diam, zpow_add_one₀ two_ne_zero]
  ring

end ParabolicRectifiability.QuantitativeCharacterization
