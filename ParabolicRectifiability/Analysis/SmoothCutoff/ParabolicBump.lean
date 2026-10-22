import ParabolicRectifiability.Analysis.SmoothCutoff.Profile
import ParabolicRectifiability.Metric.Space
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Actual parabolic bumps

For a radius `r > 0` and a center `z = (x₀, t₀)` of parabolic space, the bump is the function on ordinary coordinates `Spatial n × ℝ`

    ψ(x, t) = a (‖x - x₀‖² / r²) * b ((t - t₀) / r²).

Smoothness and all derivative statements are on ordinary coordinates; parabolic
space only enters through `point` in the ball statements.

The derivative bounds come from a scaling identity. In the spatial variable the
bump is `β * g (r⁻¹ • (y - x₀))`, with the fixed compactly supported smooth
function `g(w) = a(‖w‖²)` and a factor `β ∈ [0,1]`; in time it is
`α * b ((r²)⁻¹ • (s - t₀))`. A `k`-th derivative of such a function is bounded by
the global bound of the `k`-th derivative of `g` (resp. `b`) times `λ^k`, where
`λ = r⁻¹` (resp. `(r²)⁻¹`). The global bounds exist by compact support and form
one constant `bumpBound n ≥ 1`, depending only on the dimension.

The bump is one on the open parabolic `2r`-ball and vanishes outside the closed
set `{‖x - x₀‖² ≤ 8 r², |t - t₀| ≤ 8 r²}`. Since `8 < 9`, this closed set lies in
the open parabolic `3r`-ball, so the closed support of the bump (and of all of
its derivatives) lies in that open ball.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ParabolicRectifiability

namespace SmoothCutoff

variable {n : ℕ}

/-! ### Fixed unit-scale functions and their derivative bound -/

/-- The unit-scale spatial bump `g(w) = a(‖w‖²)`. -/
def unitSpatialBump (w : Spatial n) : ℝ := spatialProfile (‖w‖ ^ 2)

theorem contDiff_unitSpatialBump : ContDiff ℝ ∞ (unitSpatialBump (n := n)) :=
  contDiff_spatialProfile.comp (contDiff_norm_sq ℝ)

theorem hasCompactSupport_unitSpatialBump : HasCompactSupport (unitSpatialBump (n := n)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Spatial n) 3) ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
  apply spatialProfile_eq_zero
  nlinarith [norm_nonneg w]

theorem exists_unitBump_bound (n : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 2 →
      (∀ w : Spatial n, ‖iteratedFDeriv ℝ k unitSpatialBump w‖ ≤ B) ∧
      ∀ u : ℝ, ‖iteratedFDeriv ℝ k temporalProfile u‖ ≤ B := by
  have hs : ∀ k : ℕ, ∃ C, ∀ w : Spatial n, ‖iteratedFDeriv ℝ k unitSpatialBump w‖ ≤ C :=
    fun k => (contDiff_unitSpatialBump.continuous_iteratedFDeriv
      (mod_cast le_top)).bounded_above_of_compact_support
        (hasCompactSupport_unitSpatialBump.iteratedFDeriv k)
  have ht : ∀ k : ℕ, ∃ C, ∀ u : ℝ, ‖iteratedFDeriv ℝ k temporalProfile u‖ ≤ C :=
    fun k => (contDiff_temporalProfile.continuous_iteratedFDeriv
      (mod_cast le_top)).bounded_above_of_compact_support
        (hasCompactSupport_temporalProfile.iteratedFDeriv k)
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

/-- A fixed bound, depending only on `n`, for the derivatives of order at most two
of the unit-scale spatial bump and of the temporal profile. -/
def bumpBound (n : ℕ) : ℝ := Classical.choose (exists_unitBump_bound n)

theorem one_le_bumpBound (n : ℕ) : 1 ≤ bumpBound n :=
  (Classical.choose_spec (exists_unitBump_bound n)).1

theorem bumpBound_nonneg (n : ℕ) : 0 ≤ bumpBound n := zero_le_one.trans (one_le_bumpBound n)

theorem norm_iteratedFDeriv_unitSpatialBump_le {k : ℕ} (hk : k ≤ 2) (w : Spatial n) :
    ‖iteratedFDeriv ℝ k unitSpatialBump w‖ ≤ bumpBound n :=
  ((Classical.choose_spec (exists_unitBump_bound n)).2 k hk).1 w

theorem norm_iteratedFDeriv_temporalProfile_le (n : ℕ) {k : ℕ} (hk : k ≤ 2) (u : ℝ) :
    ‖iteratedFDeriv ℝ k temporalProfile u‖ ≤ bumpBound n :=
  ((Classical.choose_spec (exists_unitBump_bound n)).2 k hk).2 u

/-! ### Scaling -/

/-- The `k`-th derivative of `y ↦ β * g (c • (y - y₀))` is bounded by the global
bound for the `k`-th derivative of `g` times `c ^ k`, when `|β| ≤ 1` and `c ≥ 0`. -/
theorem norm_iteratedFDeriv_mul_comp_smul_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : E → ℝ} (hg : ContDiff ℝ ∞ g) {k : ℕ} {B : ℝ}
    (hB : ∀ w, ‖iteratedFDeriv ℝ k g w‖ ≤ B) {β : ℝ} (hβ : |β| ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (y₀ x : E) :
    ‖iteratedFDeriv ℝ k (fun y => β * g (c • (y - y₀))) x‖ ≤ B * c ^ k := by
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hLdef
  have hfun : (fun y => β * g (c • (y - y₀))) = fun y => β • (g ∘ L) (y - y₀) := by
    funext y
    simp [L, smul_eq_mul]
  have hk : ((k : ℕ) : ℕ∞ω) ≤ ∞ := mod_cast le_top
  have hgL : ContDiff ℝ ∞ (g ∘ L) := hg.comp L.contDiff
  have hshift : ContDiff ℝ ∞ (fun y => (g ∘ L) (y - y₀)) :=
    hgL.comp (contDiff_id.sub contDiff_const)
  rw [hfun, iteratedFDeriv_const_smul_apply' ((hshift.of_le hk).contDiffAt),
    iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hg _ hk, norm_smul]
  have hL : ‖L‖ ≤ c := by
    refine (norm_smul_le c (ContinuousLinearMap.id ℝ E)).trans ?_
    rw [Real.norm_of_nonneg hc]
    exact mul_le_of_le_one_right hc ContinuousLinearMap.norm_id_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g (L (x - y₀))) (fun _ : Fin k => L)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
  refine (mul_le_mul ?_ ?_ (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · rwa [Real.norm_eq_abs]
  · exact hcomp.trans (mul_le_mul (hB _) (pow_le_pow_left₀ (norm_nonneg _) hL k)
      (by positivity) hB0)

/-! ### The parabolic bump -/

/-- The parabolic bump `ψ(x,t) = a(‖x - x₀‖²/r²) b((t - t₀)/r²)` of center `z = (x₀,t₀)`,
as a function of ordinary coordinates. -/
def parabolicBump (r : ℝ) (z : Space n) (p : Coordinates n) : ℝ :=
  spatialProfile (‖p.1 - z.1‖ ^ 2 / r ^ 2) * temporalProfile ((p.2 - z.2.val) / r ^ 2)

/-- Joint smoothness in ordinary coordinates. -/
theorem contDiff_parabolicBump (r : ℝ) (z : Space n) : ContDiff ℝ ∞ (parabolicBump r z) :=
  (contDiff_spatialProfile.comp
      (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const)).div_const _)).mul
    (contDiff_temporalProfile.comp ((contDiff_snd.sub contDiff_const).div_const _))

theorem parabolicBump_nonneg (r : ℝ) (z : Space n) (p : Coordinates n) :
    0 ≤ parabolicBump r z p :=
  mul_nonneg (spatialProfile_nonneg _) (temporalProfile_nonneg _)

theorem parabolicBump_le_one (r : ℝ) (z : Space n) (p : Coordinates n) :
    parabolicBump r z p ≤ 1 :=
  (mul_le_mul (spatialProfile_le_one _) (temporalProfile_le_one _) (temporalProfile_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

/-- Membership of a coordinate point in a parabolic ball. -/
theorem point_mem_ball_iff {r : ℝ} (hr : 0 < r) (z : Space n) (x : Spatial n) (t : ℝ) :
    point x t ∈ Metric.ball z r ↔ ‖x - z.1‖ < r ∧ |t - z.2.val| < r ^ 2 := by
  rcases z with ⟨y, ⟨s⟩⟩
  exact mem_ball_point y x s t r hr

/-- The bump is one on the open parabolic `2r`-ball. -/
theorem parabolicBump_eq_one {r : ℝ} (hr : 0 < r) {z : Space n} {p : Coordinates n}
    (hp : point p.1 p.2 ∈ Metric.ball z (2 * r)) : parabolicBump r z p = 1 := by
  rw [point_mem_ball_iff (by positivity)] at hp
  obtain ⟨hx, ht⟩ := hp
  have hr2 : 0 < r ^ 2 := by positivity
  rw [parabolicBump, spatialProfile_eq_one, temporalProfile_eq_one, mul_one]
  · rw [abs_div, abs_of_pos hr2, div_le_iff₀ hr2]
    nlinarith
  · rw [div_le_iff₀ hr2]
    nlinarith [norm_nonneg (p.1 - z.1)]

/-- The closed set outside which the bump vanishes. -/
def bumpSupportSet (r : ℝ) (z : Space n) : Set (Coordinates n) :=
  {p | ‖p.1 - z.1‖ ^ 2 ≤ 8 * r ^ 2 ∧ |p.2 - z.2.val| ≤ 8 * r ^ 2}

theorem isClosed_bumpSupportSet (r : ℝ) (z : Space n) : IsClosed (bumpSupportSet r z) :=
  (isClosed_le ((continuous_fst.sub continuous_const).norm.pow 2) continuous_const).inter
    (isClosed_le (continuous_snd.sub continuous_const).abs continuous_const)

theorem parabolicBump_eq_zero {r : ℝ} (hr : 0 < r) {z : Space n} {p : Coordinates n}
    (hp : p ∉ bumpSupportSet r z) : parabolicBump r z p = 0 := by
  have hr2 : 0 < r ^ 2 := by positivity
  simp only [bumpSupportSet, mem_ofPred_eq, not_and_or, not_le] at hp
  rcases hp with h | h
  · rw [parabolicBump, spatialProfile_eq_zero, zero_mul]
    rw [le_div_iff₀ hr2]
    linarith
  · rw [parabolicBump, temporalProfile_eq_zero, mul_zero]
    rw [abs_div, abs_of_pos hr2, le_div_iff₀ hr2]
    linarith

theorem parabolicBump_eventuallyEq_zero {r : ℝ} (hr : 0 < r) {z : Space n}
    {p : Coordinates n} (hp : p ∉ bumpSupportSet r z) :
    parabolicBump r z =ᶠ[𝓝 p] fun _ => 0 := by
  filter_upwards [(isClosed_bumpSupportSet r z).isOpen_compl.mem_nhds hp] with q hq
  exact parabolicBump_eq_zero hr hq

theorem tsupport_parabolicBump_subset {r : ℝ} (hr : 0 < r) (z : Space n) :
    tsupport (parabolicBump r z) ⊆ bumpSupportSet r z :=
  closure_minimal (fun _p hp => by_contra fun h => hp (parabolicBump_eq_zero hr h))
    (isClosed_bumpSupportSet r z)

/-- The margin `8 < 9`: the closed set `bumpSupportSet` lies in the open `3r`-ball. -/
theorem point_mem_ball_of_mem_bumpSupportSet {r : ℝ} (hr : 0 < r) {z : Space n}
    {p : Coordinates n} (hp : p ∈ bumpSupportSet r z) :
    point p.1 p.2 ∈ Metric.ball z (3 * r) := by
  rw [point_mem_ball_iff (by positivity)]
  obtain ⟨h1, h2⟩ := hp
  have hr2 : 0 < r ^ 2 := by positivity
  constructor
  · have h : ‖p.1 - z.1‖ ^ 2 < (3 * r) ^ 2 := by nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  · nlinarith

/-! ### Derivative bounds with parabolic scaling -/

private theorem norm_smul_inv_sq (r : ℝ) (v : Spatial n) :
    ‖r⁻¹ • v‖ ^ 2 = ‖v‖ ^ 2 / r ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, inv_mul_eq_div]

/-- Spatial derivatives of order `k ≤ 2` scale like `r⁻ᵏ`. -/
theorem norm_iteratedFDeriv_parabolicBump_spatial_le {r : ℝ} (hr : 0 < r) (z : Space n)
    (t : ℝ) (x : Spatial n) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun y => parabolicBump r z (y, t)) x‖ ≤ bumpBound n * r⁻¹ ^ k := by
  have hfun : (fun y => parabolicBump r z (y, t)) = fun y =>
      temporalProfile ((t - z.2.val) / r ^ 2) * unitSpatialBump (r⁻¹ • (y - z.1)) := by
    funext y
    rw [parabolicBump, unitSpatialBump, norm_smul_inv_sq, mul_comm]
  rw [hfun]
  refine norm_iteratedFDeriv_mul_comp_smul_sub_le contDiff_unitSpatialBump
    (fun w => norm_iteratedFDeriv_unitSpatialBump_le hk w) ?_ (inv_nonneg.2 hr.le) z.1 x
  rw [abs_of_nonneg (temporalProfile_nonneg _)]
  exact temporalProfile_le_one _

/-- Time derivatives of order `k ≤ 2` scale like `r⁻²ᵏ`. -/
theorem norm_iteratedFDeriv_parabolicBump_time_le {r : ℝ} (hr : 0 < r) (z : Space n)
    (x : Spatial n) (t : ℝ) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun s => parabolicBump r z (x, s)) t‖ ≤
      bumpBound n * (r ^ 2)⁻¹ ^ k := by
  have hfun : (fun s => parabolicBump r z (x, s)) = fun s =>
      spatialProfile (‖x - z.1‖ ^ 2 / r ^ 2) * temporalProfile ((r ^ 2)⁻¹ • (s - z.2.val)) := by
    funext s
    rw [parabolicBump, smul_eq_mul, inv_mul_eq_div]
  rw [hfun]
  refine norm_iteratedFDeriv_mul_comp_smul_sub_le contDiff_temporalProfile
    (fun u => norm_iteratedFDeriv_temporalProfile_le n hk u) ?_
    (inv_nonneg.2 (by positivity)) z.2.val t
  rw [abs_of_nonneg (spatialProfile_nonneg _)]
  exact spatialProfile_le_one _

/-- First spatial derivative: `‖D_x ψ‖ ≤ B / r`. -/
theorem norm_fderiv_parabolicBump_spatial_le {r : ℝ} (hr : 0 < r) (z : Space n) (t : ℝ)
    (x : Spatial n) :
    ‖fderiv ℝ (fun y => parabolicBump r z (y, t)) x‖ ≤ bumpBound n / r := by
  rw [← norm_iteratedFDeriv_one, div_eq_mul_inv, ← pow_one r⁻¹]
  exact norm_iteratedFDeriv_parabolicBump_spatial_le hr z t x (by norm_num)

/-- Second spatial derivative: `‖D_x² ψ‖ ≤ B / r²`. -/
theorem norm_fderiv_fderiv_parabolicBump_spatial_le {r : ℝ} (hr : 0 < r) (z : Space n)
    (t : ℝ) (x : Spatial n) :
    ‖fderiv ℝ (fderiv ℝ fun y => parabolicBump r z (y, t)) x‖ ≤ bumpBound n / r ^ 2 := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, div_eq_mul_inv, ← inv_pow]
  exact norm_iteratedFDeriv_parabolicBump_spatial_le hr z t x le_rfl

/-- Time derivative: `|∂_t ψ| ≤ B / r²`. -/
theorem abs_deriv_parabolicBump_time_le {r : ℝ} (hr : 0 < r) (z : Space n) (x : Spatial n)
    (t : ℝ) :
    |deriv (fun s => parabolicBump r z (x, s)) t| ≤ bumpBound n / r ^ 2 := by
  rw [← Real.norm_eq_abs, norm_deriv_eq_norm_fderiv, ← norm_iteratedFDeriv_one,
    div_eq_mul_inv, ← pow_one (r ^ 2)⁻¹]
  exact norm_iteratedFDeriv_parabolicBump_time_le hr z x t (by norm_num)

end SmoothCutoff

end ParabolicRectifiability
