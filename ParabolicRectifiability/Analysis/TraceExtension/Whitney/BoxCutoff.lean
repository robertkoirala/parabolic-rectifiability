import ParabolicRectifiability.Analysis.TraceExtension.Whitney.Data
import ParabolicRectifiability.Analysis.SmoothCutoff.ParabolicBump

/-!
# Smooth product cutoffs of parabolic boxes

Part of the construction of the smooth Whitney partition: for a radius
`r > 0` and a center `c = (x₀, t₀)`, the product cutoff on ordinary coordinates

    θ(x, t) = ∏_i η((x_i - x₀_i)/r) · η((t - t₀)/r²)

with one fixed one-dimensional profile `η`, equal to one on `[-1/2, 1/2]` and
vanishing outside `(-5/8, 5/8)`. It equals one on the closed box of spatial side
`r` and time side `r²` about `c`, and its closed support lies in the closed box of
sides `5r/4` and `5r²/4`, hence inside the open enlargement by the factor `3/2`.

The spatial factor is `U(r⁻¹ • (x - x₀))` with the fixed compactly supported unit
function `U(w) = ∏_i η(w_i)`. As for the round bumps of `SmoothCutoff.ParabolicBump`,
the scaling lemma `norm_iteratedFDeriv_mul_comp_smul_sub_le` gives derivative bounds
`B r⁻ᵏ` in space and `B r⁻²ᵏ` in time, `k ≤ 2`, with one constant `B` depending only
on the dimension.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ParabolicRectifiability

namespace SmoothCutoff

/-! ### The one-dimensional profile -/

/-- The box profile `η(s) = a(32 s - 12) a(-12 - 32 s)`: one on `[-1/2, 1/2]`, zero
outside `(-5/8, 5/8)`. -/
def boxProfile (s : ℝ) : ℝ := spatialProfile (32 * s - 12) * spatialProfile (-12 - 32 * s)

theorem contDiff_boxProfile : ContDiff ℝ ∞ boxProfile :=
  (contDiff_spatialProfile.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (contDiff_spatialProfile.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem boxProfile_nonneg (s : ℝ) : 0 ≤ boxProfile s :=
  mul_nonneg (spatialProfile_nonneg _) (spatialProfile_nonneg _)

theorem boxProfile_le_one (s : ℝ) : boxProfile s ≤ 1 :=
  (mul_le_mul (spatialProfile_le_one _) (spatialProfile_le_one _) (spatialProfile_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

theorem boxProfile_eq_one {s : ℝ} (hs : |s| ≤ 1 / 2) : boxProfile s = 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hs
  rw [boxProfile, spatialProfile_eq_one (by linarith), spatialProfile_eq_one (by linarith),
    mul_one]

theorem boxProfile_eq_zero {s : ℝ} (hs : 5 / 8 ≤ |s|) : boxProfile s = 0 := by
  rcases le_abs'.mp hs with h | h
  · rw [boxProfile, spatialProfile_eq_zero (s := -12 - 32 * s) (by linarith), mul_zero]
  · rw [boxProfile, spatialProfile_eq_zero (s := 32 * s - 12) (by linarith), zero_mul]

theorem hasCompactSupport_boxProfile : HasCompactSupport boxProfile := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 1) ?_
  intro s hs
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hs
  exact boxProfile_eq_zero (by linarith)

/-! ### The unit box bump -/

variable {n : ℕ}

/-- The unit-scale spatial box bump `U(w) = ∏_i η(w_i)`. -/
def unitBoxBump (w : Spatial n) : ℝ := ∏ i, boxProfile (w i)

theorem contDiff_unitBoxBump : ContDiff ℝ ∞ (unitBoxBump (n := n)) :=
  contDiff_prod fun _ _ => contDiff_boxProfile.comp (contDiff_piLp_apply 2)

theorem unitBoxBump_nonneg (w : Spatial n) : 0 ≤ unitBoxBump w :=
  Finset.prod_nonneg fun _ _ => boxProfile_nonneg _

theorem unitBoxBump_le_one (w : Spatial n) : unitBoxBump w ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => boxProfile_nonneg _) fun _ _ => boxProfile_le_one _

theorem unitBoxBump_eq_one {w : Spatial n} (hw : ∀ i, |w i| ≤ 1 / 2) : unitBoxBump w = 1 :=
  Finset.prod_eq_one fun i _ => boxProfile_eq_one (hw i)

theorem unitBoxBump_eq_zero {w : Spatial n} {i : Fin n} (hi : 5 / 8 ≤ |w i|) :
    unitBoxBump w = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (boxProfile_eq_zero hi)

theorem hasCompactSupport_unitBoxBump : HasCompactSupport (unitBoxBump (n := n)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Spatial n) n) ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
  by_contra hne
  have hsmall : ∀ i, |w i| < 1 := by
    intro i
    by_contra h
    exact hne (unitBoxBump_eq_zero (i := i) (by linarith [not_lt.mp h]))
  have hsq : ‖w‖ ^ 2 ≤ n := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have h0 := abs_nonneg (w i)
          have h1 := hsmall i
          nlinarith [sq_abs (w i)]
      _ = n := by simp
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  nlinarith [norm_nonneg w]

theorem exists_boxBump_bound (n : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 2 →
      (∀ w : Spatial n, ‖iteratedFDeriv ℝ k unitBoxBump w‖ ≤ B) ∧
      ∀ u : ℝ, ‖iteratedFDeriv ℝ k boxProfile u‖ ≤ B := by
  have hs : ∀ k : ℕ, ∃ C, ∀ w : Spatial n, ‖iteratedFDeriv ℝ k unitBoxBump w‖ ≤ C :=
    fun k => (contDiff_unitBoxBump.continuous_iteratedFDeriv
      (mod_cast le_top)).bounded_above_of_compact_support
        (hasCompactSupport_unitBoxBump.iteratedFDeriv k)
  have ht : ∀ k : ℕ, ∃ C, ∀ u : ℝ, ‖iteratedFDeriv ℝ k boxProfile u‖ ≤ C :=
    fun k => (contDiff_boxProfile.continuous_iteratedFDeriv
      (mod_cast le_top)).bounded_above_of_compact_support
        (hasCompactSupport_boxProfile.iteratedFDeriv k)
  obtain ⟨S0, hS0⟩ := hs 0
  obtain ⟨S1, hS1⟩ := hs 1
  obtain ⟨S2, hS2⟩ := hs 2
  obtain ⟨T0, hT0⟩ := ht 0
  obtain ⟨T1, hT1⟩ := ht 1
  obtain ⟨T2, hT2⟩ := ht 2
  have a0 := abs_nonneg S0
  have a1 := abs_nonneg S1
  have a2 := abs_nonneg S2
  have b0 := abs_nonneg T0
  have b1 := abs_nonneg T1
  have b2 := abs_nonneg T2
  have c0 := le_abs_self S0
  have c1 := le_abs_self S1
  have c2 := le_abs_self S2
  have d0 := le_abs_self T0
  have d1 := le_abs_self T1
  have d2 := le_abs_self T2
  refine ⟨1 + |S0| + |S1| + |S2| + |T0| + |T1| + |T2|, by linarith, ?_⟩
  intro k hk
  interval_cases k
  · exact ⟨fun w => by linarith [hS0 w], fun u => by linarith [hT0 u]⟩
  · exact ⟨fun w => by linarith [hS1 w], fun u => by linarith [hT1 u]⟩
  · exact ⟨fun w => by linarith [hS2 w], fun u => by linarith [hT2 u]⟩

/-- A fixed bound, depending only on `n`, for the derivatives of order at most two of
the unit box bump and of the box profile. -/
def boxBumpBound (n : ℕ) : ℝ := Classical.choose (exists_boxBump_bound n)

theorem one_le_boxBumpBound (n : ℕ) : 1 ≤ boxBumpBound n :=
  (Classical.choose_spec (exists_boxBump_bound n)).1

theorem boxBumpBound_nonneg (n : ℕ) : 0 ≤ boxBumpBound n :=
  zero_le_one.trans (one_le_boxBumpBound n)

theorem norm_iteratedFDeriv_unitBoxBump_le {k : ℕ} (hk : k ≤ 2) (w : Spatial n) :
    ‖iteratedFDeriv ℝ k unitBoxBump w‖ ≤ boxBumpBound n :=
  ((Classical.choose_spec (exists_boxBump_bound n)).2 k hk).1 w

theorem norm_iteratedFDeriv_boxProfile_le (n : ℕ) {k : ℕ} (hk : k ≤ 2) (u : ℝ) :
    ‖iteratedFDeriv ℝ k boxProfile u‖ ≤ boxBumpBound n :=
  ((Classical.choose_spec (exists_boxBump_bound n)).2 k hk).2 u

/-! ### The box bump at radius `r` and center `c` -/

/-- The product cutoff `θ(x,t) = U(r⁻¹ (x - x₀)) η((t - t₀)/r²)` of center
`c = (x₀, t₀)`, on ordinary coordinates. -/
def boxBump (r : ℝ) (c : Space n) (p : Coordinates n) : ℝ :=
  unitBoxBump (r⁻¹ • (p.1 - c.1)) * boxProfile ((r ^ 2)⁻¹ * (p.2 - c.2.val))

theorem contDiff_boxBump (r : ℝ) (c : Space n) : ContDiff ℝ ∞ (boxBump r c) :=
  (contDiff_unitBoxBump.comp ((contDiff_fst.sub contDiff_const).const_smul _)).mul
    (contDiff_boxProfile.comp (contDiff_const.mul (contDiff_snd.sub contDiff_const)))

theorem boxBump_nonneg (r : ℝ) (c : Space n) (p : Coordinates n) : 0 ≤ boxBump r c p :=
  mul_nonneg (unitBoxBump_nonneg _) (boxProfile_nonneg _)

theorem boxBump_le_one (r : ℝ) (c : Space n) (p : Coordinates n) : boxBump r c p ≤ 1 :=
  (mul_le_mul (unitBoxBump_le_one _) (boxProfile_le_one _) (boxProfile_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

private theorem abs_inv_mul_le_iff {r a b : ℝ} (hr : 0 < r) :
    |r⁻¹ * a| ≤ b ↔ |a| ≤ b * r := by
  rw [abs_mul, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr, mul_comm r b]

private theorem le_abs_inv_mul_iff {r a b : ℝ} (hr : 0 < r) :
    b ≤ |r⁻¹ * a| ↔ b * r ≤ |a| := by
  rw [abs_mul, abs_of_pos (inv_pos.2 hr), le_inv_mul_iff₀ hr, mul_comm r b]

/-- The bump is one on the closed box of spatial side `r` and time side `r²`. -/
theorem boxBump_eq_one {r : ℝ} (hr : 0 < r) {c : Space n} {p : Coordinates n}
    (hx : ∀ i, |p.1 i - c.1 i| ≤ r / 2) (ht : |p.2 - c.2.val| ≤ r ^ 2 / 2) :
    boxBump r c p = 1 := by
  have hr2 : 0 < r ^ 2 := by positivity
  rw [boxBump, unitBoxBump_eq_one, boxProfile_eq_one, mul_one]
  · rw [abs_inv_mul_le_iff hr2]
    linarith
  · intro i
    rw [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, abs_inv_mul_le_iff hr]
    linarith [hx i]

/-- The closed box (sides `5r/4` and `5r²/4`) outside which the bump vanishes. -/
def boxSupportSet (r : ℝ) (c : Space n) : Set (Coordinates n) :=
  {p | (∀ i, |p.1 i - c.1 i| ≤ 5 / 8 * r) ∧ |p.2 - c.2.val| ≤ 5 / 8 * r ^ 2}

theorem isClosed_boxSupportSet (r : ℝ) (c : Space n) : IsClosed (boxSupportSet r c) := by
  have h1 : IsClosed {p : Coordinates n | ∀ i, |p.1 i - c.1 i| ≤ 5 / 8 * r} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (((PiLp.continuous_apply 2 _ i).comp continuous_fst).sub
        continuous_const).abs continuous_const
  exact h1.inter (isClosed_le (continuous_snd.sub continuous_const).abs continuous_const)

theorem boxBump_eq_zero {r : ℝ} (hr : 0 < r) {c : Space n} {p : Coordinates n}
    (hp : p ∉ boxSupportSet r c) : boxBump r c p = 0 := by
  have hr2 : 0 < r ^ 2 := by positivity
  simp only [boxSupportSet, Set.mem_ofPred_eq, not_and_or, not_forall, not_le] at hp
  rcases hp with ⟨i, hi⟩ | h
  · rw [boxBump, unitBoxBump_eq_zero (i := i), zero_mul]
    rw [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, le_abs_inv_mul_iff hr]
    linarith
  · rw [boxBump, boxProfile_eq_zero, mul_zero]
    rw [le_abs_inv_mul_iff hr2]
    linarith

theorem boxBump_eventuallyEq_zero {r : ℝ} (hr : 0 < r) {c : Space n} {p : Coordinates n}
    (hp : p ∉ boxSupportSet r c) : boxBump r c =ᶠ[𝓝 p] fun _ => 0 := by
  filter_upwards [(isClosed_boxSupportSet r c).isOpen_compl.mem_nhds hp] with q hq
  exact boxBump_eq_zero hr hq

theorem mem_boxSupportSet_of_ne_zero {r : ℝ} (hr : 0 < r) {c : Space n} {p : Coordinates n}
    (hp : boxBump r c p ≠ 0) : p ∈ boxSupportSet r c :=
  by_contra fun h => hp (boxBump_eq_zero hr h)

/-! ### Derivative bounds with parabolic scaling -/

/-- Spatial derivatives of order `k ≤ 2` scale like `r⁻ᵏ`. -/
theorem norm_iteratedFDeriv_boxBump_spatial_le {r : ℝ} (hr : 0 < r) (c : Space n)
    (t : ℝ) (x : Spatial n) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun y => boxBump r c (y, t)) x‖ ≤ boxBumpBound n * r⁻¹ ^ k := by
  have hfun : (fun y => boxBump r c (y, t)) = fun y =>
      boxProfile ((r ^ 2)⁻¹ * (t - c.2.val)) * unitBoxBump (r⁻¹ • (y - c.1)) := by
    funext y
    rw [boxBump, mul_comm]
  rw [hfun]
  refine norm_iteratedFDeriv_mul_comp_smul_sub_le contDiff_unitBoxBump
    (fun w => norm_iteratedFDeriv_unitBoxBump_le hk w) ?_ (inv_nonneg.2 hr.le) c.1 x
  rw [abs_of_nonneg (boxProfile_nonneg _)]
  exact boxProfile_le_one _

/-- Time derivatives of order `k ≤ 2` scale like `r⁻²ᵏ`. -/
theorem norm_iteratedFDeriv_boxBump_time_le {r : ℝ} (hr : 0 < r) (c : Space n)
    (x : Spatial n) (t : ℝ) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun s => boxBump r c (x, s)) t‖ ≤
      boxBumpBound n * (r ^ 2)⁻¹ ^ k := by
  have hfun : (fun s => boxBump r c (x, s)) = fun s =>
      unitBoxBump (r⁻¹ • (x - c.1)) * boxProfile ((r ^ 2)⁻¹ • (s - c.2.val)) := by
    funext s
    rw [boxBump, smul_eq_mul]
  rw [hfun]
  refine norm_iteratedFDeriv_mul_comp_smul_sub_le contDiff_boxProfile
    (fun u => norm_iteratedFDeriv_boxProfile_le n hk u) ?_
    (inv_nonneg.2 (by positivity)) c.2.val t
  rw [abs_of_nonneg (unitBoxBump_nonneg _)]
  exact unitBoxBump_le_one _

end SmoothCutoff

/-! ### The cutoff of a parabolic dyadic box -/

namespace WhitneyCutoff

open SmoothCutoff

variable {m : ℕ}

theorem radius_pos (Q : ParabolicDyadicBox m) : 0 < Q.radius :=
  zpow_pos (by norm_num) _

/-- The product cutoff of a box: radius `r_Q` and center `p_Q`. -/
def boxCutoff (Q : ParabolicDyadicBox m) : Coordinates m → ℝ := boxBump Q.radius Q.center

theorem center_fst_apply (Q : ParabolicDyadicBox m) (i : Fin m) :
    Q.center.1 i = ((Q.space i : ℝ) + 1 / 2) * Q.radius := rfl

theorem center_snd_val (Q : ParabolicDyadicBox m) :
    Q.center.2.val = ((Q.time : ℝ) + 1 / 2) * Q.radius ^ 2 := rfl

theorem contDiff_boxCutoff (Q : ParabolicDyadicBox m) : ContDiff ℝ ∞ (boxCutoff Q) :=
  contDiff_boxBump _ _

theorem boxCutoff_nonneg (Q : ParabolicDyadicBox m) (p : Coordinates m) : 0 ≤ boxCutoff Q p :=
  boxBump_nonneg _ _ _

theorem boxCutoff_le_one (Q : ParabolicDyadicBox m) (p : Coordinates m) : boxCutoff Q p ≤ 1 :=
  boxBump_le_one _ _ _

/-- The cutoff of a box is one on the box. -/
theorem boxCutoff_eq_one {Q : ParabolicDyadicBox m} {z : Space m} (hz : z ∈ Q.toSet) :
    boxCutoff Q (z.1, z.2.val) = 1 := by
  obtain ⟨hx, ht1, ht2⟩ := hz
  refine boxBump_eq_one (radius_pos Q) (fun i => ?_) ?_
  · obtain ⟨h1, h2⟩ := hx i
    dsimp only
    rw [center_fst_apply, abs_le]
    constructor <;> linarith
  · dsimp only
    rw [center_snd_val, abs_le]
    constructor <;> linarith

/-- The closed support box lies in the open enlargement by `3/2`. -/
theorem mem_enlarged_of_mem_boxSupportSet {Q : ParabolicDyadicBox m} {z : Space m}
    (hz : (z.1, z.2.val) ∈ boxSupportSet Q.radius Q.center) : z ∈ Q.enlarged (3 / 2) := by
  have hr := radius_pos Q
  have hr2 : 0 < Q.radius ^ 2 := by positivity
  simp only [boxSupportSet, Set.mem_ofPred_eq] at hz
  obtain ⟨hx, ht⟩ := hz
  simp only [ParabolicDyadicBox.enlarged, Set.mem_ofPred_eq]
  refine ⟨fun i => ?_, ?_⟩
  · have := hx i
    linarith
  · linarith

/-- A box lies in its own enlargement by `3/2`. -/
theorem toSet_subset_enlarged (Q : ParabolicDyadicBox m) : Q.toSet ⊆ Q.enlarged (3 / 2) := by
  intro z hz
  have hr := radius_pos Q
  obtain ⟨hx, ht1, ht2⟩ := hz
  simp only [ParabolicDyadicBox.enlarged, Set.mem_ofPred_eq]
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hx i
    rw [center_fst_apply, abs_lt]
    constructor <;> linarith
  · have hr2 : 0 < Q.radius ^ 2 := by positivity
    rw [center_snd_val, abs_lt]
    constructor <;> linarith

/-- Where the cutoff of a box is nonzero, the point lies in the enlargement. -/
theorem mem_enlarged_of_boxCutoff_ne_zero {Q : ParabolicDyadicBox m} {z : Space m}
    (hz : boxCutoff Q (z.1, z.2.val) ≠ 0) : z ∈ Q.enlarged (3 / 2) :=
  mem_enlarged_of_mem_boxSupportSet (mem_boxSupportSet_of_ne_zero (radius_pos Q) hz)

end WhitneyCutoff

end ParabolicRectifiability
