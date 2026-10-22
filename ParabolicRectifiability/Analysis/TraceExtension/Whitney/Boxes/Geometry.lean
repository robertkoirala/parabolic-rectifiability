import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Boxes.Grid

/-! # Volume and metric geometry of parabolic dyadic boxes

Measurability and the volume `|Q| = r_Q^(m+2)`, the inner ball `P(p_Q, r_Q/2) ⊆ Q`
(also in rank zero), the outer ball `closure Q ⊆ closedBall(p_Q, D_m r_Q)` and the
child–parent center bound. This file assembles these facts as
`parabolicDyadicBox_geometry_proof`.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability

/-! ## The dimensional constant -/

theorem one_le_whitneyD (m : ℕ) : 1 ≤ whitneyD m :=
  le_max_left _ _

theorem whitneyD_pos (m : ℕ) : 0 < whitneyD m :=
  lt_of_lt_of_le one_pos (one_le_whitneyD m)

theorem sqrt_le_whitneyD (m : ℕ) : Real.sqrt m ≤ whitneyD m :=
  le_max_right _ _

/-! ## Coordinates of the parabolic distance -/

theorem dist_eq_max_coord {m : ℕ} (z w : Space m) :
    dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases w with ⟨y, ⟨s⟩⟩
  exact dist_point x y t s

theorem dist_le_of_coord {m : ℕ} {z w : Space m} {s : ℝ} (hs : 0 ≤ s)
    (hx : ‖z.1 - w.1‖ ≤ s) (ht : |z.2.val - w.2.val| ≤ s ^ 2) : dist z w ≤ s := by
  rw [dist_eq_max_coord]
  exact max_le hx ((Real.sqrt_le_left hs).mpr ht)

/-- Coordinatewise bounds `|x_i| ≤ c` give `‖x‖ ≤ √m c`. -/
theorem norm_le_sqrt_mul_of_forall_abs_le {m : ℕ} {x : Spatial m} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |x i| ≤ c) : ‖x‖ ≤ Real.sqrt m * c := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ (m : ℝ) * c ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin m, c ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = (m : ℝ) * c ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((m : ℝ) * c ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt m * c := by rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hc]

namespace ParabolicDyadicBox

variable {m : ℕ}

@[simp]
theorem center_fst_apply (Q : ParabolicDyadicBox m) (i : Fin m) :
    Q.center.1 i = ((Q.space i : ℝ) + 1 / 2) * Q.radius :=
  rfl

@[simp]
theorem center_snd_val (Q : ParabolicDyadicBox m) :
    Q.center.2.val = ((Q.time : ℝ) + 1 / 2) * Q.radius ^ 2 :=
  rfl

/-! ## Center, inner ball and outer ball -/

theorem center_mem (Q : ParabolicDyadicBox m) : Q.center ∈ Q.toSet := by
  have hr := Q.radius_pos
  have hr2 : 0 < Q.radius ^ 2 := pow_pos hr 2
  simp only [toSet, Set.mem_ofPred_eq, center_fst_apply, center_snd_val]
  refine ⟨fun i => ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The open parabolic ball of radius `r_Q/2` about the center lies in `Q`. -/
theorem ball_half_subset (Q : ParabolicDyadicBox m) :
    Metric.ball Q.center (Q.radius / 2) ⊆ Q.toSet := by
  intro z hz
  have hr := Q.radius_pos
  have hr2 : 0 < Q.radius ^ 2 := pow_pos hr 2
  rw [Metric.mem_ball, dist_eq_max_coord, max_lt_iff] at hz
  obtain ⟨hx, ht⟩ := hz
  rw [Real.sqrt_lt (abs_nonneg _) (by linarith)] at ht
  rw [center_snd_val, abs_lt] at ht
  obtain ⟨ht1, ht2⟩ := ht
  simp only [toSet, Set.mem_ofPred_eq]
  refine ⟨fun i => ?_, ?_, ?_⟩
  · have hi : |z.1 i - Q.center.1 i| < Q.radius / 2 :=
      lt_of_le_of_lt (by simpa using PiLp.norm_apply_le (z.1 - Q.center.1) i) hx
    rw [center_fst_apply, abs_lt] at hi
    obtain ⟨hi1, hi2⟩ := hi
    constructor <;> linarith
  · linarith
  · linarith

/-- Coordinate offsets of a point of `Q` from its center. -/
theorem abs_sub_center_le_of_mem {Q : ParabolicDyadicBox m} {z : Space m} (hz : z ∈ Q.toSet) :
    (∀ i, |z.1 i - Q.center.1 i| ≤ Q.radius / 2) ∧
      |z.2.val - Q.center.2.val| ≤ Q.radius ^ 2 / 2 := by
  simp only [toSet, Set.mem_ofPred_eq] at hz
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hz.1 i
    rw [center_fst_apply, abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hz.2
    rw [center_snd_val, abs_le]
    constructor <;> linarith

/-- Coordinate offsets at most `r_Q` and `r_Q²` give distance at most `D_m r_Q`. -/
theorem dist_center_le_of_abs_le {Q : ParabolicDyadicBox m} {z : Space m}
    (hx : ∀ i, |z.1 i - Q.center.1 i| ≤ Q.radius)
    (ht : |z.2.val - Q.center.2.val| ≤ Q.radius ^ 2) :
    dist z Q.center ≤ whitneyD m * Q.radius := by
  have hr := Q.radius_pos
  have hD := one_le_whitneyD m
  apply dist_le_of_coord (mul_nonneg (whitneyD_pos m).le hr.le)
  · calc ‖z.1 - Q.center.1‖ ≤ Real.sqrt m * Q.radius :=
          norm_le_sqrt_mul_of_forall_abs_le hr.le fun i => by simpa using hx i
      _ ≤ whitneyD m * Q.radius := mul_le_mul_of_nonneg_right (sqrt_le_whitneyD m) hr.le
  · calc |z.2.val - Q.center.2.val| ≤ Q.radius ^ 2 := ht
      _ = 1 * Q.radius ^ 2 := (one_mul _).symm
      _ ≤ whitneyD m ^ 2 * Q.radius ^ 2 :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hD) (sq_nonneg _)
      _ = (whitneyD m * Q.radius) ^ 2 := (mul_pow _ _ _).symm

theorem dist_center_le_of_mem {Q : ParabolicDyadicBox m} {z : Space m} (hz : z ∈ Q.toSet) :
    dist z Q.center ≤ whitneyD m * Q.radius := by
  have hr := Q.radius_pos
  have hr2 : 0 < Q.radius ^ 2 := pow_pos hr 2
  obtain ⟨hx, ht⟩ := abs_sub_center_le_of_mem hz
  exact dist_center_le_of_abs_le (fun i => (hx i).trans (by linarith)) (ht.trans (by linarith))

theorem toSet_subset_closedBall (Q : ParabolicDyadicBox m) :
    Q.toSet ⊆ Metric.closedBall Q.center (whitneyD m * Q.radius) :=
  fun _ hz => Metric.mem_closedBall.mpr (dist_center_le_of_mem hz)

theorem closure_toSet_subset (Q : ParabolicDyadicBox m) :
    closure Q.toSet ⊆ Metric.closedBall Q.center (whitneyD m * Q.radius) :=
  closure_minimal Q.toSet_subset_closedBall Metric.isClosed_closedBall

/-- The centers of a box and its parent are within `2 D_m r_Q`. -/
theorem dist_center_parent_center_le_two (Q : ParabolicDyadicBox m) :
    dist Q.center Q.parent.center ≤ 2 * whitneyD m * Q.radius := by
  have h := dist_center_le_of_mem (Q.toSet_subset_parent Q.center_mem)
  rw [parent_radius] at h
  linarith

theorem dist_center_parent_center_le (Q : ParabolicDyadicBox m) :
    dist Q.center Q.parent.center ≤ 3 * whitneyD m * Q.radius := by
  have h := Q.dist_center_parent_center_le_two
  have : 0 ≤ whitneyD m * Q.radius := mul_nonneg (whitneyD_pos m).le Q.radius_nonneg
  linarith

/-! ## Measurability and volume -/

/-- A box is the preimage of a product of half-open intervals in ordinary coordinates. -/
theorem toSet_eq_preimage (Q : ParabolicDyadicBox m) :
    Q.toSet = coordinatesMeasurableEquiv m ⁻¹'
      ((WithLp.ofLp ⁻¹' Set.pi Set.univ fun i =>
          Set.Ico ((Q.space i : ℝ) * Q.radius) (((Q.space i : ℝ) + 1) * Q.radius) :
          Set (Spatial m)) ×ˢ
        Set.Ico ((Q.time : ℝ) * Q.radius ^ 2) (((Q.time : ℝ) + 1) * Q.radius ^ 2)) := by
  ext z
  simp only [toSet, Set.mem_ofPred_eq, Set.mem_preimage, coordinatesMeasurableEquiv_apply,
    Set.mem_prod, Set.mem_univ_pi, Set.mem_Ico]

theorem measurableSet_toSet (Q : ParabolicDyadicBox m) : MeasurableSet Q.toSet := by
  rw [toSet_eq_preimage]
  exact (coordinatesMeasurableEquiv m).measurable
    (((PiLp.volume_preserving_ofLp (Fin m)).measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico)).prod measurableSet_Ico)

theorem volume_toSet (Q : ParabolicDyadicBox m) :
    parabolicVolume m Q.toSet = ENNReal.ofReal (Q.radius ^ (m + 2)) := by
  have hr := Q.radius_pos
  rw [toSet_eq_preimage, (coordinates_measurePreserving m).measure_preimage_equiv,
    coordinateVolume, Measure.prod_prod,
    (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet,
    Real.volume_pi_Ico, Real.volume_Ico]
  have hsp : ∀ i, ((Q.space i : ℝ) + 1) * Q.radius - (Q.space i : ℝ) * Q.radius = Q.radius :=
    fun i => by ring
  have htm : ((Q.time : ℝ) + 1) * Q.radius ^ 2 - (Q.time : ℝ) * Q.radius ^ 2 = Q.radius ^ 2 := by
    ring
  simp only [hsp, htm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (pow_nonneg hr.le m), ← pow_add]

end ParabolicDyadicBox

/-- **Geometry of parabolic dyadic boxes**: partition, nesting, parent, volume,
measurability, inner and outer balls and the child–parent center bound. -/
theorem parabolicDyadicBox_geometry_proof (m : ℕ) :
    (∀ (j : ℤ) (z : Space m), ∃! Q : ParabolicDyadicBox m, Q.level = j ∧ z ∈ Q.toSet) ∧
    (∀ Q Q' : ParabolicDyadicBox m, Q.level ≤ Q'.level →
      Q'.toSet ⊆ Q.toSet ∨ Disjoint Q.toSet Q'.toSet) ∧
    (∀ Q : ParabolicDyadicBox m, Q.toSet ⊆ Q.parent.toSet) ∧
    (∀ Q : ParabolicDyadicBox m, MeasurableSet Q.toSet ∧
      parabolicVolume m Q.toSet = ENNReal.ofReal (Q.radius ^ (m + 2))) ∧
    (∀ Q : ParabolicDyadicBox m, Metric.ball Q.center (Q.radius / 2) ⊆ Q.toSet ∧
      closure Q.toSet ⊆ Metric.closedBall Q.center (whitneyD m * Q.radius)) ∧
    (∀ Q : ParabolicDyadicBox m, dist Q.center Q.parent.center ≤ 3 * whitneyD m * Q.radius) :=
  ⟨ParabolicDyadicBox.existsUnique_level_mem,
    fun _ _ hl => ParabolicDyadicBox.subset_or_disjoint hl,
    ParabolicDyadicBox.toSet_subset_parent,
    fun Q => ⟨Q.measurableSet_toSet, Q.volume_toSet⟩,
    fun Q => ⟨Q.ball_half_subset, Q.closure_toSet_subset⟩,
    ParabolicDyadicBox.dist_center_parent_center_le⟩

end ParabolicRectifiability
