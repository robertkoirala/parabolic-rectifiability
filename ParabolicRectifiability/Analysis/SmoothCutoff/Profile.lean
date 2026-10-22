import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.IntervalCases

/-!
# The fixed one-variable profiles of the parabolic partition

This file constructs the three fixed profiles of the partition and the normalizer `f`. All of them are built from mathlib's `Real.smoothTransition`
`S`, which vanishes on `(-∞, 0]`, equals one on `[1, ∞)` and is smooth:

* `spatialProfile s = 1 - S ((s - 4) / 4)`, the profile `a`: it takes values in
  `[0,1]`, equals one for `s ≤ 4` and vanishes for `8 ≤ s`;
* `temporalProfile u = a u * a (-u)`, the profile `b`: it takes values in
  `[0,1]`, equals one for `|u| ≤ 4` and vanishes for `8 ≤ |u|`;
* `activation s = S (4 * s - 1)`, the profile `χ`: it takes values in `[0,1]`,
  vanishes for `s ≤ 1/4` and equals one for `1/2 ≤ s`;
* `normalizer s = activation s / s`, the function `f`.

With Lean's convention `s / 0 = 0`, the formula for `normalizer` is literally
the piecewise definition `χ(s)/s` for `s > 0` and `0` otherwise
(`normalizer_eq_ite`). It is smooth on all of `ℝ` because `χ` vanishes on the
open half-line `s < 1/4`, where `normalizer` is therefore locally zero, while on
`s > 0` it is a quotient by a nonvanishing smooth function. No positive lower
bound for the denominator is assumed anywhere; the identity
`s * normalizer s = activation s` holds for every real `s`, including `s = 0`
and the transition region `1/4 < s < 1/2`.

The derivative bounds needed later are bounds for `f, f', f''` on every compact
interval `[0, M]`, obtained from continuity of the iterated derivatives.

-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ParabolicRectifiability.SmoothCutoff

/-! ### The spatial profile `a` -/

/-- The spatial profile `a`: one on `(-∞, 4]`, zero on `[8, ∞)`. -/
def spatialProfile (s : ℝ) : ℝ := 1 - Real.smoothTransition ((s - 4) / 4)

theorem contDiff_spatialProfile : ContDiff ℝ ∞ spatialProfile :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const 4))

theorem spatialProfile_nonneg (s : ℝ) : 0 ≤ spatialProfile s := by
  unfold spatialProfile
  linarith [Real.smoothTransition.le_one ((s - 4) / 4)]

theorem spatialProfile_le_one (s : ℝ) : spatialProfile s ≤ 1 := by
  unfold spatialProfile
  linarith [Real.smoothTransition.nonneg ((s - 4) / 4)]

theorem spatialProfile_eq_one {s : ℝ} (hs : s ≤ 4) : spatialProfile s = 1 := by
  rw [spatialProfile, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem spatialProfile_eq_zero {s : ℝ} (hs : 8 ≤ s) : spatialProfile s = 0 := by
  rw [spatialProfile, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

/-! ### The temporal profile `b` -/

/-- The temporal profile `b(u) = a(u) a(-u)`: one on `[-4, 4]`, zero outside `(-8, 8)`. -/
def temporalProfile (u : ℝ) : ℝ := spatialProfile u * spatialProfile (-u)

theorem contDiff_temporalProfile : ContDiff ℝ ∞ temporalProfile :=
  contDiff_spatialProfile.mul (contDiff_spatialProfile.comp contDiff_neg)

theorem temporalProfile_nonneg (u : ℝ) : 0 ≤ temporalProfile u :=
  mul_nonneg (spatialProfile_nonneg _) (spatialProfile_nonneg _)

theorem temporalProfile_le_one (u : ℝ) : temporalProfile u ≤ 1 :=
  (mul_le_mul (spatialProfile_le_one _) (spatialProfile_le_one _) (spatialProfile_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

theorem temporalProfile_eq_one {u : ℝ} (hu : |u| ≤ 4) : temporalProfile u = 1 := by
  rw [abs_le] at hu
  rw [temporalProfile, spatialProfile_eq_one (by linarith),
    spatialProfile_eq_one (by linarith), mul_one]

theorem temporalProfile_eq_zero {u : ℝ} (hu : 8 ≤ |u|) : temporalProfile u = 0 := by
  rcases le_abs'.mp hu with h | h
  · rw [temporalProfile, spatialProfile_eq_zero (s := -u) (by linarith), mul_zero]
  · rw [temporalProfile, spatialProfile_eq_zero h, zero_mul]

theorem hasCompactSupport_temporalProfile : HasCompactSupport temporalProfile := by
  refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-8 : ℝ) 8)) ?_
  intro u hu
  apply temporalProfile_eq_zero
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-! ### The activation `χ` -/

/-- The activation `χ`: zero on `(-∞, 1/4]`, one on `[1/2, ∞)`. -/
def activation (s : ℝ) : ℝ := Real.smoothTransition (4 * s - 1)

theorem contDiff_activation : ContDiff ℝ ∞ activation :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem activation_nonneg (s : ℝ) : 0 ≤ activation s := Real.smoothTransition.nonneg _

theorem activation_le_one (s : ℝ) : activation s ≤ 1 := Real.smoothTransition.le_one _

theorem activation_eq_zero {s : ℝ} (hs : s ≤ 1 / 4) : activation s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem activation_eq_one {s : ℝ} (hs : 1 / 2 ≤ s) : activation s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-! ### The normalizer `f` -/

/-- The normalizer `f(s) = χ(s)/s`; by Lean's convention its value at `0` is `0`. -/
def normalizer (s : ℝ) : ℝ := activation s / s

/-- The normalizer is exactly the piecewise formula `activation s / s` for `s > 0` and `0` otherwise. -/
theorem normalizer_eq_ite (s : ℝ) :
    normalizer s = if 0 < s then activation s / s else 0 := by
  split_ifs with hs
  · rfl
  · rw [normalizer, activation_eq_zero (by linarith [not_lt.mp hs]), zero_div]

theorem normalizer_eq_zero {s : ℝ} (hs : s ≤ 1 / 4) : normalizer s = 0 := by
  rw [normalizer, activation_eq_zero hs, zero_div]

/-- On the full-mass region the normalizer is the reciprocal. -/
theorem normalizer_eq_inv {s : ℝ} (hs : 1 / 2 ≤ s) : normalizer s = s⁻¹ := by
  rw [normalizer, activation_eq_one hs, one_div]

theorem normalizer_nonneg (s : ℝ) : 0 ≤ normalizer s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [normalizer_eq_zero (by linarith)]
  · exact div_nonneg (activation_nonneg s) hs.le

/-- The defining identity, valid for every real `s`, including `s = 0`. -/
theorem mul_normalizer (s : ℝ) : s * normalizer s = activation s := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [zero_mul, activation_eq_zero (by norm_num)]
  · rw [normalizer, mul_div_cancel₀ _ hs]

/-- The normalizer is locally zero on the open half-line below `1/4`. -/
theorem normalizer_eventuallyEq_zero {s : ℝ} (hs : s < 1 / 4) :
    normalizer =ᶠ[𝓝 s] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds hs] with y hy
  exact normalizer_eq_zero (le_of_lt hy)

/-- `f` is smooth on all of `ℝ`: it is locally zero below `1/4` and a quotient
by a nonvanishing function above `0`. -/
theorem contDiff_normalizer : ContDiff ℝ ∞ normalizer := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_or_ge s (1 / 4) with hs | hs
  · exact contDiffAt_const.congr_of_eventuallyEq (normalizer_eventuallyEq_zero hs)
  · have hs0 : s ≠ 0 := by positivity
    exact contDiff_activation.contDiffAt.div contDiffAt_id hs0

/-- Bounds for `f`, `f'` and `f''` on each compact interval `[0, M]`. -/
theorem exists_normalizer_bound (M : ℝ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ k : ℕ, k ≤ 2 → ∀ s ∈ Icc 0 M,
      ‖iteratedFDeriv ℝ k normalizer s‖ ≤ F := by
  have hc : ∀ k : ℕ, Continuous (iteratedFDeriv ℝ k normalizer) := fun k =>
    contDiff_normalizer.continuous_iteratedFDeriv (mod_cast le_top)
  obtain ⟨F0, h0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 0).continuousOn
    (s := Icc 0 M)
  obtain ⟨F1, h1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 1).continuousOn
    (s := Icc 0 M)
  obtain ⟨F2, h2⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 2).continuousOn
    (s := Icc 0 M)
  refine ⟨max (max F0 F1) (max F2 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro k hk s hs
  interval_cases k
  · exact (h0 s hs).trans (le_max_of_le_left (le_max_left _ _))
  · exact (h1 s hs).trans (le_max_of_le_left (le_max_right _ _))
  · exact (h2 s hs).trans (le_max_of_le_right (le_max_left _ _))

/-- A fixed choice of the bound in `exists_normalizer_bound`. -/
def normalizerBound (M : ℝ) : ℝ := Classical.choose (exists_normalizer_bound M)

theorem normalizerBound_nonneg (M : ℝ) : 0 ≤ normalizerBound M :=
  (Classical.choose_spec (exists_normalizer_bound M)).1

theorem norm_iteratedFDeriv_normalizer_le {M : ℝ} {k : ℕ} (hk : k ≤ 2) {s : ℝ}
    (hs : s ∈ Icc 0 M) : ‖iteratedFDeriv ℝ k normalizer s‖ ≤ normalizerBound M :=
  (Classical.choose_spec (exists_normalizer_bound M)).2 k hk s hs

end ParabolicRectifiability.SmoothCutoff
