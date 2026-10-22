import ParabolicRectifiability.Metric.Measure
import ParabolicRectifiability.Foundations.HalfTimeDerivative
import ParabolicRectifiability.Characterization.Proofs.Fourier.BMOGrowthStopping

/-! # Parabolic grid cells

Dyadic cells used in the proof of `ba1_bmo_growth_proof`. The parabolic rectangles
(spatial side `ℓ`, time side `ℓ²`) are the half-open cells of a grid with origin
`(a, s)` and side `σ`:
`cell a s σ z = {w | ⌊(w_i - a_i)/σ⌋ = ⌊(z_i - a_i)/σ⌋ ∀ i, ⌊(w_t - s)/σ²⌋ = ⌊(z_t - s)/σ²⌋}`.
The level-`k` cells of the grid of side `ℓ` are the cells of side `ℓ / 2^k`; each has
`2^(m+2)` equal-volume children. This file proves the measurability, nestedness and the exact
volume `σ^(m+2)` of the cells, the inclusion of a cell in the parabolic ball of radius
`(m+1)σ` about any of its points, the root cell containing a given ball, the passage from
ball to cell mean oscillation, the truncation estimate and the dyadic differentiation
theorem along the cells of a point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-! ## Floors -/

theorem b1bmo_floor_mul_lt (n : ℕ) (hn : 0 < n) {x y : ℝ} (h : ⌊x⌋ < ⌊y⌋) :
    ⌊(n : ℝ) * x⌋ < ⌊(n : ℝ) * y⌋ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h1 : (⌊x⌋ : ℝ) + 1 ≤ y := by
    have h' : ⌊x⌋ + 1 ≤ ⌊y⌋ := h
    have h'' : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ (⌊y⌋ : ℝ) := Int.cast_le.mpr h'
    push_cast at h''
    exact h''.trans (Int.floor_le y)
  have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  calc ⌊(n : ℝ) * x⌋ < (n : ℤ) * (⌊x⌋ + 1) := by
        rw [Int.floor_lt]
        push_cast
        exact mul_lt_mul_of_pos_left h2 hn'
    _ ≤ ⌊(n : ℝ) * y⌋ := by
        rw [Int.le_floor]
        push_cast
        exact mul_le_mul_of_nonneg_left h1 hn'.le

theorem b1bmo_floor_eq_of_mul (n : ℕ) (hn : 0 < n) {x y : ℝ}
    (h : ⌊(n : ℝ) * x⌋ = ⌊(n : ℝ) * y⌋) : ⌊x⌋ = ⌊y⌋ := by
  rcases lt_trichotomy ⌊x⌋ ⌊y⌋ with hxy | hxy | hxy
  · exact absurd h (b1bmo_floor_mul_lt n hn hxy).ne
  · exact hxy
  · exact absurd h (b1bmo_floor_mul_lt n hn hxy).ne'

theorem b1bmo_floor_div_eq_iff {τ : ℝ} (hτ : 0 < τ) (u c : ℝ) (q : ℤ) :
    ⌊(u - c) / τ⌋ = q ↔ u ∈ Ico (c + q * τ) (c + (q + 1) * τ) := by
  rw [Int.floor_eq_iff, le_div_iff₀ hτ, div_lt_iff₀ hτ, mem_Ico]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem b1bmo_abs_sub_lt_of_floor_eq {τ : ℝ} (hτ : 0 < τ) {u v c : ℝ}
    (h : ⌊(u - c) / τ⌋ = ⌊(v - c) / τ⌋) : |u - v| < τ := by
  have := Int.abs_sub_lt_one_of_floor_eq_floor h
  rwa [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hτ, div_lt_one hτ] at this

/-! ## Grid indices and cells -/

variable {m : ℕ}

/-- The grid index of a point of ordinary coordinates, for the grid with origin `(a, s)`
and side `σ` (spatial side `σ`, time side `σ²`). -/
def b1bmo_idxC (a : Spatial m) (s σ : ℝ) (y : Coordinates m) : (Fin m → ℤ) × ℤ :=
  (fun i => ⌊(y.1 i - a i) / σ⌋, ⌊(y.2 - s) / σ ^ 2⌋)

/-- The grid index on parabolic space. -/
def b1bmo_idx (a : Spatial m) (s σ : ℝ) (w : Space m) : (Fin m → ℤ) × ℤ :=
  b1bmo_idxC a s σ (coordinatesMeasurableEquiv m w)

/-- The level-`k` index map of the grid with origin `(a, s)` and root side `ℓ`. -/
def b1bmo_gridIdx (a : Spatial m) (s ℓ : ℝ) (k : ℕ) : Space m → (Fin m → ℤ) × ℤ :=
  b1bmo_idx a s (ℓ / 2 ^ k)

/-- The parabolic cell of side `σ` containing `z` in the grid with origin `(a, s)`. -/
def b1bmo_cell (a : Spatial m) (s σ : ℝ) (z : Space m) : Set (Space m) :=
  b1bmo_cellOf (b1bmo_idx a s σ) z

theorem b1bmo_measurable_idxC (a : Spatial m) (s σ : ℝ) : Measurable (b1bmo_idxC a s σ) := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun i => ?_) ?_
  · have hc : Continuous fun y : Coordinates m => y.1 i :=
      (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
    exact ((hc.measurable.sub_const _).div_const _).floor
  · exact ((measurable_snd.sub_const _).div_const _).floor

theorem b1bmo_measurable_idx (a : Spatial m) (s σ : ℝ) : Measurable (b1bmo_idx a s σ) :=
  (b1bmo_measurable_idxC a s σ).comp (coordinatesMeasurableEquiv m).measurable

theorem b1bmo_measurableSet_cell (a : Spatial m) (s σ : ℝ) (z : Space m) :
    MeasurableSet (b1bmo_cell a s σ z) :=
  b1bmo_measurableSet_cellOf (b1bmo_measurable_idx a s σ) z

theorem b1bmo_gridIdx_nest (a : Spatial m) (s ℓ : ℝ) (hℓ : 0 < ℓ) (k : ℕ) (z w : Space m)
    (h : b1bmo_gridIdx a s ℓ (k + 1) w = b1bmo_gridIdx a s ℓ (k + 1) z) :
    b1bmo_gridIdx a s ℓ k w = b1bmo_gridIdx a s ℓ k z := by
  have hk : (0 : ℝ) < ℓ / 2 ^ k := by positivity
  have h2 : ∀ u : ℝ, u / (ℓ / 2 ^ (k + 1)) = (2 : ℕ) * (u / (ℓ / 2 ^ k)) := by
    intro u
    push_cast
    field_simp
    ring
  have h4 : ∀ u : ℝ, u / (ℓ / 2 ^ (k + 1)) ^ 2 = (4 : ℕ) * (u / (ℓ / 2 ^ k) ^ 2) := by
    intro u
    push_cast
    field_simp
    ring
  simp only [b1bmo_gridIdx, b1bmo_idx, b1bmo_idxC, Prod.mk.injEq, funext_iff] at h ⊢
  refine ⟨fun i => ?_, ?_⟩
  · have hi := h.1 i
    rw [h2, h2] at hi
    exact b1bmo_floor_eq_of_mul 2 two_pos hi
  · have ht := h.2
    rw [h4, h4] at ht
    exact b1bmo_floor_eq_of_mul 4 (by norm_num) ht

theorem b1bmo_cell_eq_gridCell (a : Spatial m) (s ℓ : ℝ) (k : ℕ) (z : Space m) :
    b1bmo_cellOf (b1bmo_gridIdx a s ℓ k) z = b1bmo_cell a s (ℓ / 2 ^ k) z := rfl

theorem b1bmo_cell_gridIdx_zero (a : Spatial m) (s ℓ : ℝ) (z : Space m) :
    b1bmo_cellOf (b1bmo_gridIdx a s ℓ 0) z = b1bmo_cell a s ℓ z := by
  rw [b1bmo_cell_eq_gridCell, pow_zero, div_one]

theorem b1bmo_gridCell_succ_subset (a : Spatial m) (s ℓ : ℝ) (hℓ : 0 < ℓ) (k : ℕ)
    (z : Space m) : b1bmo_cell a s (ℓ / 2 ^ (k + 1)) z ⊆ b1bmo_cell a s (ℓ / 2 ^ k) z :=
  fun w hw => b1bmo_gridIdx_nest a s ℓ hℓ k z w hw

/-! ## Volume of a cell -/

theorem b1bmo_fibre_eq (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (p : (Fin m → ℤ) × ℤ) :
    {y : Coordinates m | b1bmo_idxC a s σ y = p} =
      (WithLp.ofLp ⁻¹' (univ.pi fun i => Ico (a i + p.1 i * σ) (a i + (p.1 i + 1) * σ))) ×ˢ
        Ico (s + p.2 * σ ^ 2) (s + (p.2 + 1) * σ ^ 2) := by
  ext ⟨x, t⟩
  simp only [mem_ofPred_eq, b1bmo_idxC, Prod.ext_iff, funext_iff, mem_prod, mem_preimage,
    mem_univ_pi]
  rw [b1bmo_floor_div_eq_iff (pow_pos hσ 2)]
  simp only [b1bmo_floor_div_eq_iff hσ]

theorem b1bmo_volume_cell (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Space m) :
    parabolicVolume m (b1bmo_cell a s σ z) = ENNReal.ofReal σ ^ (m + 2) := by
  have hpre : b1bmo_cell a s σ z = coordinatesMeasurableEquiv m ⁻¹'
      {y | b1bmo_idxC a s σ y = b1bmo_idxC a s σ (coordinatesMeasurableEquiv m z)} := rfl
  rw [hpre, (coordinates_measurePreserving m).measure_preimage_equiv, coordinateVolume,
    b1bmo_fibre_eq a s hσ, Measure.prod_prod,
    (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (MeasurableSet.univ_pi fun i => measurableSet_Ico).nullMeasurableSet,
    Real.volume_pi_Ico, Real.volume_Ico]
  have hsp : ∀ i : Fin m, a i + ((b1bmo_idxC a s σ (coordinatesMeasurableEquiv m z)).1 i + 1) * σ
      - (a i + (b1bmo_idxC a s σ (coordinatesMeasurableEquiv m z)).1 i * σ) = σ := by
    intro i
    ring
  simp only [hsp, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show s + ((b1bmo_idxC a s σ (coordinatesMeasurableEquiv m z)).2 + 1) * σ ^ 2 -
      (s + (b1bmo_idxC a s σ (coordinatesMeasurableEquiv m z)).2 * σ ^ 2) = σ ^ 2 by ring,
    ENNReal.ofReal_pow hσ.le, pow_add]

theorem b1bmo_volume_cell_pos (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Space m) :
    parabolicVolume m (b1bmo_cell a s σ z) ≠ 0 := by
  rw [b1bmo_volume_cell a s hσ]
  exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr hσ).ne'

theorem b1bmo_volume_cell_lt_top (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Space m) :
    parabolicVolume m (b1bmo_cell a s σ z) ≠ ∞ := by
  rw [b1bmo_volume_cell a s hσ]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

/-- Each cell has `2^(m+2)` times the volume of its children. -/
theorem b1bmo_volume_gridCell_succ (a : Spatial m) (s ℓ : ℝ) (hℓ : 0 < ℓ) (k : ℕ)
    (z w : Space m) :
    parabolicVolume m (b1bmo_cell a s (ℓ / 2 ^ k) z) =
      2 ^ (m + 2) * parabolicVolume m (b1bmo_cell a s (ℓ / 2 ^ (k + 1)) w) := by
  rw [b1bmo_volume_cell a s (by positivity), b1bmo_volume_cell a s (by positivity), ← mul_pow]
  congr 1
  rw [show ℓ / 2 ^ k = 2 * (ℓ / 2 ^ (k + 1)) by rw [pow_succ]; field_simp,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-! ## Cells and parabolic balls -/

theorem b1bmo_mem_ball_iff (z w : Space m) {r : ℝ} (hr : 0 < r) :
    w ∈ Metric.ball z r ↔ ‖w.1 - z.1‖ < r ∧ |w.2.val - z.2.val| < r ^ 2 := by
  have h := coordinates_symm_preimage_ball z r hr
  have hw : w ∈ Metric.ball z r ↔
      coordinatesMeasurableEquiv m w ∈ (coordinatesMeasurableEquiv m).symm ⁻¹' Metric.ball z r := by
    rw [mem_preimage, MeasurableEquiv.symm_apply_apply]
  rw [hw, h, coordinatesMeasurableEquiv_apply, mem_prod, Metric.mem_ball, dist_eq_norm,
    mem_Ioo, abs_sub_lt_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by linarith, by linarith⟩

theorem b1bmo_norm_lt_of_coord {x : Spatial m} {σ : ℝ} (hσ : 0 < σ) (hx : ∀ i, |x i| < σ) :
    ‖x‖ < ((m : ℝ) + 1) * σ := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_lt' (by positivity)]
  have hsum : ∑ i, ‖x.ofLp i‖ ^ 2 ≤ ∑ _i : Fin m, σ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    have := hx i
    nlinarith [abs_nonneg (x i), sq_abs (x i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hσ2 : 0 < σ ^ 2 := by positivity
  calc ∑ i, ‖x.ofLp i‖ ^ 2 ≤ (m : ℝ) * σ ^ 2 := hsum
    _ < (((m : ℝ) + 1) * σ) ^ 2 := by nlinarith

/-- A cell of side `σ` lies in the parabolic ball of radius `(m+1)σ` about any of its points. -/
theorem b1bmo_cell_subset_ball (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Space m) :
    b1bmo_cell a s σ z ⊆ Metric.ball z (((m : ℝ) + 1) * σ) := by
  intro w hw
  have hw' : b1bmo_idxC a s σ (w.1, w.2.val) = b1bmo_idxC a s σ (z.1, z.2.val) := hw
  simp only [b1bmo_idxC, Prod.mk.injEq, funext_iff] at hw'
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [b1bmo_mem_ball_iff z w (by positivity)]
  refine ⟨b1bmo_norm_lt_of_coord hσ fun i => ?_, ?_⟩
  · have := b1bmo_abs_sub_lt_of_floor_eq hσ (hw'.1 i)
    simpa using this
  · have := b1bmo_abs_sub_lt_of_floor_eq (pow_pos hσ 2) hw'.2
    have hσm : σ ≤ ((m : ℝ) + 1) * σ := by nlinarith
    calc |w.2.val - z.2.val| < σ ^ 2 := this
      _ ≤ (((m : ℝ) + 1) * σ) ^ 2 := pow_le_pow_left₀ hσ.le hσm 2

/-- The volume ratio constant between the ball of radius `(m+1)σ` and a cell of side `σ`. -/
def b1bmo_Kc (m : ℕ) : ℝ≥0∞ := 2 * omega m * ENNReal.ofReal ((m : ℝ) + 1) ^ (m + 2)

theorem b1bmo_Kc_ne_top (m : ℕ) : b1bmo_Kc m ≠ ∞ := by
  unfold b1bmo_Kc
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (omega_lt_top m).ne)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem b1bmo_Kc_ne_zero (m : ℕ) : b1bmo_Kc m ≠ 0 := by
  unfold b1bmo_Kc
  refine mul_ne_zero (mul_ne_zero (by simp) (omega_pos m).ne') (pow_ne_zero _ ?_)
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

theorem b1bmo_volume_ball_cell (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Space m) :
    parabolicVolume m (Metric.ball z (((m : ℝ) + 1) * σ)) =
      b1bmo_Kc m * parabolicVolume m (b1bmo_cell a s σ z) := by
  rw [parabolicVolume_ball z _ (by positivity), b1bmo_volume_cell a s hσ, b1bmo_Kc,
    ENNReal.ofReal_mul (by positivity), mul_pow]
  ring

theorem b1bmo_volume_closedBall_cell (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (z : Space m) :
    parabolicVolume m (Metric.closedBall z (((m : ℝ) + 1) * σ)) =
      b1bmo_Kc m * parabolicVolume m (b1bmo_cell a s σ z) := by
  rw [parabolicVolume_closedBall z _ (by positivity), b1bmo_volume_cell a s hσ, b1bmo_Kc,
    ENNReal.ofReal_mul (by positivity), mul_pow]
  ring

theorem b1bmo_volume_ball_ne_zero (p : Space m) {r : ℝ} (hr : 0 < r) :
    parabolicVolume m (Metric.ball p r) ≠ 0 := by
  rw [parabolicVolume_ball p r hr]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos m).ne')
    (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne')

theorem b1bmo_volume_closedBall_ne_zero (p : Space m) {r : ℝ} (hr : 0 < r) :
    parabolicVolume m (Metric.closedBall p r) ≠ 0 := by
  rw [parabolicVolume_closedBall p r hr.le]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (omega_pos m).ne')
    (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hr).ne')

/-! ## The root cell of a parabolic ball -/

/-- Grid origin of the root cell of `P(p, r)`: spatial corner `p - r`. -/
def b1bmo_rootA (p : Space m) (r : ℝ) : Spatial m := WithLp.toLp 2 fun i => p.1 i - r

/-- Grid origin of the root cell of `P(p, r)`: time corner `t - r²`. -/
def b1bmo_rootS (p : Space m) (r : ℝ) : ℝ := p.2.val - r ^ 2

theorem b1bmo_root_idx (p : Space m) {r : ℝ} (hr : 0 < r) {w : Space m}
    (hw : w ∈ Metric.ball p r) :
    b1bmo_idx (b1bmo_rootA p r) (b1bmo_rootS p r) (2 * r) w = (0, 0) := by
  rw [b1bmo_mem_ball_iff p w hr] at hw
  obtain ⟨h1, h2⟩ := hw
  rw [abs_lt] at h2
  simp only [b1bmo_idx, b1bmo_idxC, coordinatesMeasurableEquiv_apply, b1bmo_rootA,
    b1bmo_rootS, PiLp.toLp_apply, Prod.mk.injEq, funext_iff, Pi.zero_apply,
    Int.floor_eq_zero_iff, mem_Ico]
  refine ⟨fun i => ?_, ?_⟩
  · have hi : |w.1 i - p.1 i| < r := by
      have := PiLp.norm_apply_le (w.1 - p.1) i
      rw [WithLp.ofLp_sub, Pi.sub_apply, Real.norm_eq_abs] at this
      exact this.trans_lt h1
    rw [abs_lt] at hi
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_lt_one (by positivity)]
      linarith
  · constructor
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_lt_one (by positivity)]
      nlinarith

theorem b1bmo_ball_subset_root (p : Space m) {r : ℝ} (hr : 0 < r) :
    Metric.ball p r ⊆ b1bmo_cell (b1bmo_rootA p r) (b1bmo_rootS p r) (2 * r) p := by
  intro w hw
  show b1bmo_idx _ _ _ w = b1bmo_idx _ _ _ p
  rw [b1bmo_root_idx p hr hw, b1bmo_root_idx p hr (Metric.mem_ball_self hr)]

theorem b1bmo_volume_root (p : Space m) {r : ℝ} (hr : 0 < r) :
    parabolicVolume m (b1bmo_cell (b1bmo_rootA p r) (b1bmo_rootS p r) (2 * r) p) =
      2 ^ (m + 2) * ENNReal.ofReal r ^ (m + 2) := by
  rw [b1bmo_volume_cell _ _ (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat, mul_pow]

/-! ## Integrability -/

theorem b1bmo_integrableOn_ball {g : Space m → ℝ} (hg : LocallyIntegrable g (parabolicVolume m))
    (z : Space m) (r : ℝ) : IntegrableOn g (Metric.ball z r) (parabolicVolume m) :=
  (hg.integrableOn_isCompact (isCompact_closedBall z r)).mono_set Metric.ball_subset_closedBall

theorem b1bmo_integrableOn_cell {g : Space m → ℝ} (hg : LocallyIntegrable g (parabolicVolume m))
    (a : Spatial m) (s : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : Space m) :
    IntegrableOn g (b1bmo_cell a s σ z) (parabolicVolume m) :=
  (b1bmo_integrableOn_ball hg z _).mono_set (b1bmo_cell_subset_ball a s hσ z)

/-! ## From balls to cells -/

/-- Mean oscillation on balls in extended form. -/
def b1bmo_ballOsc (m : ℕ) (g : Space m → ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (p : Space m) (r : ℝ), 0 < r →
    ∫⁻ w in Metric.ball p r, ‖g w - b1bmo_avg (parabolicVolume m) (Metric.ball p r) g‖ₑ
      ∂parabolicVolume m ≤ β * parabolicVolume m (Metric.ball p r)

/-- Mean oscillation on all grid cells in extended form. -/
def b1bmo_cellOsc (m : ℕ) (g : Space m → ℝ) (β : ℝ≥0∞) : Prop :=
  ∀ (a : Spatial m) (s σ : ℝ), 0 < σ → ∀ z : Space m,
    ∫⁻ w in b1bmo_cell a s σ z, ‖g w - b1bmo_avg (parabolicVolume m) (b1bmo_cell a s σ z) g‖ₑ
      ∂parabolicVolume m ≤ β * parabolicVolume m (b1bmo_cell a s σ z)

theorem b1bmo_ballOsc_of_bound {g : Space m → ℝ} {B : ℝ}
    (hg : HasStandardParabolicBMOBound m g B) : b1bmo_ballOsc m g (ENNReal.ofReal B) := by
  intro p r hr
  obtain ⟨hB, hloc, hosc⟩ := hg
  have hint : IntegrableOn g (Metric.ball p r) (parabolicVolume m) := b1bmo_integrableOn_ball hloc p r
  have hpos : 0 < (parabolicVolume m (Metric.ball p r)).toReal :=
    ENNReal.toReal_pos (b1bmo_volume_ball_ne_zero p hr) measure_ball_lt_top.ne
  have h := hosc p r hr
  rw [div_le_iff₀ hpos] at h
  have hav : standardBallAverage m g p r = b1bmo_avg (parabolicVolume m) (Metric.ball p r) g := by
    rw [standardBallAverage, b1bmo_avg, smul_eq_mul]
  rw [hav] at h
  have hint' : IntegrableOn (fun w => g w - b1bmo_avg (parabolicVolume m) (Metric.ball p r) g)
      (Metric.ball p r) (parabolicVolume m) := hint.sub (integrableOn_const measure_ball_lt_top.ne)
  have hPt : parabolicVolume m (Metric.ball p r) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ w in Metric.ball p r, ‖g w - b1bmo_avg (parabolicVolume m) (Metric.ball p r) g‖ₑ
        ∂parabolicVolume m
      = ENNReal.ofReal (∫ w in Metric.ball p r,
          ‖g w - b1bmo_avg (parabolicVolume m) (Metric.ball p r) g‖ ∂parabolicVolume m) :=
        (ofReal_integral_norm_eq_lintegral_enorm hint').symm
    _ ≤ ENNReal.ofReal (B * (parabolicVolume m (Metric.ball p r)).toReal) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal B * parabolicVolume m (Metric.ball p r) := by
        rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_toReal hPt]

theorem b1bmo_cellOsc_of_ballOsc {g : Space m → ℝ} (hg : LocallyIntegrable g (parabolicVolume m))
    {β : ℝ≥0∞} (hβ : b1bmo_ballOsc m g β) : b1bmo_cellOsc m g (2 * b1bmo_Kc m * β) := by
  intro a s σ hσ z
  set μ := parabolicVolume m
  set D := b1bmo_cell a s σ z
  set P := Metric.ball z (((m : ℝ) + 1) * σ)
  have hDP : D ⊆ P := b1bmo_cell_subset_ball a s hσ z
  calc ∫⁻ w in D, ‖g w - b1bmo_avg μ D g‖ₑ ∂μ ≤ 2 * ∫⁻ w in D, ‖g w - b1bmo_avg μ P g‖ₑ ∂μ :=
        b1bmo_setLIntegral_osc_le μ (b1bmo_volume_cell_pos a s hσ z)
          (b1bmo_volume_cell_lt_top a s hσ z) (b1bmo_integrableOn_cell hg a s hσ z) _
    _ ≤ 2 * ∫⁻ w in P, ‖g w - b1bmo_avg μ P g‖ₑ ∂μ := by gcongr
    _ ≤ 2 * (β * μ P) := by gcongr; exact hβ z _ (by positivity)
    _ = 2 * b1bmo_Kc m * β * μ D := by
        rw [b1bmo_volume_ball_cell a s hσ z]
        ring

/-! ## Truncation -/

/-- Truncation at height `N`. -/
def b1bmo_trunc (N y : ℝ) : ℝ := max (min N y) (-N)

theorem b1bmo_abs_trunc_sub_le (N x y : ℝ) : |b1bmo_trunc N x - b1bmo_trunc N y| ≤ |x - y| := by
  unfold b1bmo_trunc
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem b1bmo_abs_trunc_le (N y : ℝ) (hN : 0 ≤ N) : |b1bmo_trunc N y| ≤ N := by
  unfold b1bmo_trunc
  rw [abs_le]
  constructor
  · exact le_max_right _ _
  · exact max_le (min_le_left _ _) (by linarith)

theorem b1bmo_abs_trunc_le_abs (N y : ℝ) (hN : 0 ≤ N) : |b1bmo_trunc N y| ≤ |y| := by
  have h0 : b1bmo_trunc N 0 = 0 := by
    unfold b1bmo_trunc
    rw [min_eq_right hN, max_eq_left (by linarith)]
  simpa [h0] using b1bmo_abs_trunc_sub_le N y 0

theorem b1bmo_trunc_eq (N y : ℝ) (hy : |y| ≤ N) : b1bmo_trunc N y = y := by
  unfold b1bmo_trunc
  rw [abs_le] at hy
  rw [min_eq_right hy.2, max_eq_left hy.1]

theorem b1bmo_continuous_trunc (N : ℝ) : Continuous (b1bmo_trunc N) :=
  (continuous_const.min continuous_id).max continuous_const

theorem b1bmo_locallyIntegrable_trunc {g : Space m → ℝ}
    (hg : LocallyIntegrable g (parabolicVolume m)) (N : ℝ) (hN : 0 ≤ N) :
    LocallyIntegrable (fun w => b1bmo_trunc N (g w)) (parabolicVolume m) := by
  refine hg.mono ?_ ?_
  · exact (b1bmo_continuous_trunc N).comp_aestronglyMeasurable hg.aestronglyMeasurable
  · exact Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs] using b1bmo_abs_trunc_le_abs N (g w) hN

/-- Truncation at most doubles the cell oscillation. -/
theorem b1bmo_cellOsc_trunc {g : Space m → ℝ} (hg : LocallyIntegrable g (parabolicVolume m))
    {β : ℝ≥0∞} (hβ : b1bmo_cellOsc m g β) (N : ℝ) (hN : 0 ≤ N) :
    b1bmo_cellOsc m (fun w => b1bmo_trunc N (g w)) (2 * β) := by
  intro a s σ hσ z
  set μ := parabolicVolume m
  set D := b1bmo_cell a s σ z
  calc ∫⁻ w in D, ‖b1bmo_trunc N (g w) - b1bmo_avg μ D (fun w => b1bmo_trunc N (g w))‖ₑ ∂μ
      ≤ 2 * ∫⁻ w in D, ‖b1bmo_trunc N (g w) - b1bmo_trunc N (b1bmo_avg μ D g)‖ₑ ∂μ :=
        b1bmo_setLIntegral_osc_le μ (b1bmo_volume_cell_pos a s hσ z)
          (b1bmo_volume_cell_lt_top a s hσ z)
          (b1bmo_integrableOn_cell (b1bmo_locallyIntegrable_trunc hg N hN) a s hσ z) _
    _ ≤ 2 * ∫⁻ w in D, ‖g w - b1bmo_avg μ D g‖ₑ ∂μ := by
        gcongr with w
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (b1bmo_abs_trunc_sub_le N _ _)
    _ ≤ 2 * (β * μ D) := by gcongr; exact hβ a s σ hσ z
    _ = 2 * β * μ D := by ring

/-! ## Dyadic differentiation -/

/-- The parabolic volume is uniformly locally doubling (constant `2^(m+2)`). -/
theorem b1bmo_isUnifLocDoubling (m : ℕ) : IsUnifLocDoublingMeasure (parabolicVolume m) := by
  refine ⟨⟨2 ^ (m + 2), ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) x
  rw [parabolicVolume_closedBall x (2 * ε) (by positivity), parabolicVolume_closedBall x ε hε.le,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
  apply le_of_eq
  push_cast
  ring

/-- Lebesgue differentiation along the cells of a point, for every grid at once. -/
theorem b1bmo_ae_tendsto_cells {g : Space m → ℝ} (hg : LocallyIntegrable g (parabolicVolume m)) :
    ∀ᵐ z ∂parabolicVolume m, ∀ (a : Spatial m) (s σ : ℝ), 0 < σ →
      Tendsto (fun k : ℕ => (parabolicVolume m (b1bmo_cell a s (σ / 2 ^ k) z))⁻¹ *
        ∫⁻ w in b1bmo_cell a s (σ / 2 ^ k) z, ‖g w - g z‖ₑ ∂parabolicVolume m) atTop (𝓝 0) := by
  have := b1bmo_isUnifLocDoubling m
  set μ := parabolicVolume m
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub μ hg 1] with z hz
  intro a s σ hσ
  set δ : ℕ → ℝ := fun k => ((m : ℝ) + 1) * (σ / 2 ^ k) with hδdef
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hδ : Tendsto δ atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hδpos⟩
    have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have h2 := (h1.const_mul σ).const_mul ((m : ℝ) + 1)
    simp only [mul_zero] at h2
    refine h2.congr fun k => ?_
    simp only [hδdef, div_eq_mul_inv]
  have hlim := hz (fun _ => z) δ hδ (Eventually.of_forall fun k => by
    rw [one_mul]
    exact Metric.mem_closedBall_self (hδpos k).le)
  -- the closed-ball averages in extended form
  have hconv : ∀ k, ENNReal.ofReal (⨍ y in Metric.closedBall z (δ k), ‖g y - g z‖ ∂μ) =
      (μ (Metric.closedBall z (δ k)))⁻¹ *
        ∫⁻ y in Metric.closedBall z (δ k), ‖g y - g z‖ₑ ∂μ := by
    intro k
    have hcb0 : μ (Metric.closedBall z (δ k)) ≠ 0 :=
      b1bmo_volume_closedBall_ne_zero z (hδpos k)
    have hcbt : μ (Metric.closedBall z (δ k)) ≠ ∞ := measure_closedBall_lt_top.ne
    have hint : IntegrableOn (fun y => g y - g z) (Metric.closedBall z (δ k)) μ :=
      (hg.integrableOn_isCompact (isCompact_closedBall z (δ k))).sub
        (integrableOn_const hcbt)
    rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.mpr measureReal_nonneg),
      ofReal_integral_norm_eq_lintegral_enorm hint, measureReal_def,
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hcb0 hcbt), ENNReal.ofReal_toReal hcbt]
  have hlim' : Tendsto (fun k => (μ (Metric.closedBall z (δ k)))⁻¹ *
      ∫⁻ y in Metric.closedBall z (δ k), ‖g y - g z‖ₑ ∂μ) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hlim
    rw [ENNReal.ofReal_zero] at this
    exact this.congr hconv
  have hlim'' := ENNReal.Tendsto.const_mul hlim' (Or.inr (b1bmo_Kc_ne_top m))
  rw [mul_zero] at hlim''
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'' (fun k => zero_le)
    fun k => ?_
  have hk : 0 < σ / 2 ^ k := by positivity
  set D := b1bmo_cell a s (σ / 2 ^ k) z
  have hD0 : μ D ≠ 0 := b1bmo_volume_cell_pos a s hk z
  have hDt : μ D ≠ ∞ := b1bmo_volume_cell_lt_top a s hk z
  have hcb : μ (Metric.closedBall z (δ k)) = b1bmo_Kc m * μ D :=
    b1bmo_volume_closedBall_cell a s hk z
  have hDcb : D ⊆ Metric.closedBall z (δ k) :=
    (b1bmo_cell_subset_ball a s hk z).trans Metric.ball_subset_closedBall
  have hinv : (μ D)⁻¹ = b1bmo_Kc m * (μ (Metric.closedBall z (δ k)))⁻¹ := by
    rw [hcb, ENNReal.mul_inv (Or.inl (b1bmo_Kc_ne_zero m)) (Or.inl (b1bmo_Kc_ne_top m)),
      ← mul_assoc, ENNReal.mul_inv_cancel (b1bmo_Kc_ne_zero m) (b1bmo_Kc_ne_top m), one_mul]
  calc (μ D)⁻¹ * ∫⁻ w in D, ‖g w - g z‖ₑ ∂μ
      ≤ (μ D)⁻¹ * ∫⁻ w in Metric.closedBall z (δ k), ‖g w - g z‖ₑ ∂μ := by
        gcongr
    _ = b1bmo_Kc m * ((μ (Metric.closedBall z (δ k)))⁻¹ *
          ∫⁻ y in Metric.closedBall z (δ k), ‖g y - g z‖ₑ ∂μ) := by
        rw [hinv, mul_assoc]

end ParabolicRectifiability.Characterization
