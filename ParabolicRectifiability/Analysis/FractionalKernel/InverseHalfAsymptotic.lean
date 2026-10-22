import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Group.Integral

/-! # Asymptotic expansion of `ρ * |·|^{-1/2}`

One-dimensional analysis; this module depends on Mathlib only.

Write `I(x) = |x|^{-1/2}` (Mathlib's `Real.rpow`, so `I(0) = 0`). Main result
(`fhpbb2a_inverseHalf_asymptotic`): for a real Schwartz function `ρ` and every `N`, there is `C`
with, for every `|t| ≥ 1`,
`|∫ ρ(s) I(t - s) ds - Σ_{k<N} ((-1)^k / k!) (∫ s^k ρ(s) ds) I^{(k)}(t)| ≤ C |t|^{-N}`,
where `I^{(k)}` is Mathlib's global `iteratedDeriv`.

Proof. Put `T = |t| ≥ 1` and
`R_N(t,s) = I(t - s) - Σ_{k<N} I^{(k)}(t) (-s)^k / k!`. Then
* the expansion error is `∫ ρ(s) R_N(t,s) ds` (restored polynomial moments,
  `fhpbb2a_moment_identity`);
* on `|s| ≤ T/2` the segment `[t - s, t]` stays in `|·| ≥ T/2`, and the Lagrange remainder gives
  `T^N |R_N| ≤ A |s|^N` (`fhpbb2a_near`; only for `N ≥ 1`);
* on `|s| > T/2`, `T^N ≤ 2^N (1+|s|)^N`, `|I^{(k)}(t)| ≤ c_k`, and
  `T^N |R_N| ≤ 2^N (1+|s|)^N I(t-s) + 2^N S (1+|s|)^{2N}` (restored moments, `fhpbb2a_sum_bound`);
* `N = 0` is handled without any Taylor expansion (`fhpbb2a_pointwise`);
* the remote singularity is controlled by the explicit uniform bound
  `∫ (1+|s|)^{-2} |t - s|^{-1/2} ds ≤ 2 + 4 = 6` for every `t` (`fhpbb2a_remote`), together with
  arbitrary Schwartz decay of `ρ` (`fhpbb2a_decay_weight`).
The Taylor expansion is never taken across `s = t`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Nat Topology SchwartzMap

namespace ParabolicRectifiability.FractionalKernel

/-! ## Derivatives of `|x|^r` away from the origin -/

/-- `|x|^r` is smooth at every nonzero point. -/
theorem fhpbb2a_contDiffAt (r : ℝ) {n : WithTop ℕ∞} {y : ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ n (fun x : ℝ => |x| ^ r) y := by
  rcases hy.lt_or_gt with hy | hy
  · have h : (fun x : ℝ => |x| ^ r) =ᶠ[𝓝 y] (fun x : ℝ => (-x) ^ r) := by
      filter_upwards [Iio_mem_nhds hy] with x hx
      rw [abs_of_neg hx]
    exact ((Real.contDiffAt_rpow_const_of_ne (neg_ne_zero.mpr hy.ne)).comp y
      contDiff_neg.contDiffAt).congr_of_eventuallyEq h
  · have h : (fun x : ℝ => |x| ^ r) =ᶠ[𝓝 y] (fun x : ℝ => x ^ r) := by
      filter_upwards [Ioi_mem_nhds hy] with x hx
      rw [abs_of_pos hx]
    exact (Real.contDiffAt_rpow_const_of_ne hy.ne').congr_of_eventuallyEq h

theorem fhpbb2a_iteratedDeriv_of_pos (r : ℝ) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv k (fun x : ℝ => |x| ^ r) y = (descPochhammer ℝ k).eval r * y ^ (r - k) := by
  have h : (fun x : ℝ => |x| ^ r) =ᶠ[𝓝 y] (fun x : ℝ => x ^ r) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    rw [abs_of_pos hx]
  rw [h.iteratedDeriv_eq k, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

/-- `|I^{(k)}(y)| = |p_k(r)| |y|^{r-k}` for `y ≠ 0`, both signs of `y` (evenness of `|x|^r`). -/
theorem fhpbb2a_abs_iteratedDeriv (r : ℝ) (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    |iteratedDeriv k (fun x : ℝ => |x| ^ r) y| =
      |(descPochhammer ℝ k).eval r| * |y| ^ (r - k) := by
  rcases hy.lt_or_gt with hy | hy
  · have h := iteratedDeriv_comp_neg k (fun x : ℝ => |x| ^ r) y
    simp only [abs_neg] at h
    rw [h, fhpbb2a_iteratedDeriv_of_pos r k (neg_pos.mpr hy), smul_eq_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (neg_pos.mpr hy).le _), abs_of_neg hy]
    simp
  · rw [fhpbb2a_iteratedDeriv_of_pos r k hy, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hy.le _), abs_of_pos hy]

theorem fhpbb2a_abs_iteratedDeriv_mul_pow (r : ℝ) (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    |iteratedDeriv k (fun x : ℝ => |x| ^ r) y| * |y| ^ k =
      |(descPochhammer ℝ k).eval r| * |y| ^ r := by
  have hy' : 0 < |y| := abs_pos.mpr hy
  rw [fhpbb2a_abs_iteratedDeriv r k hy, Real.rpow_sub hy', Real.rpow_natCast, mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero k hy'.ne')]

/-- For each `k`, `|I^{(k)}(y)| |y|^k = c_k I(y)` with a constant `c_k ≥ 0`. -/
theorem fhpbb2a_deriv_bound (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ y : ℝ, y ≠ 0 →
      |iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y| * |y| ^ k =
        c * |y| ^ (-(1 / 2 : ℝ)) :=
  ⟨_, abs_nonneg _, fun _ hy => fhpbb2a_abs_iteratedDeriv_mul_pow _ k hy⟩

theorem fhpbb2a_abs_iteratedDeriv_le {k : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ y : ℝ, y ≠ 0 →
      |iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y| * |y| ^ k =
        c * |y| ^ (-(1 / 2 : ℝ)))
    {t : ℝ} (ht : 1 ≤ |t|) :
    |iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t| ≤ c := by
  have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
  calc |iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t|
      ≤ |iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t| * |t| ^ k :=
        le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ ht)
    _ = c * |t| ^ (-(1 / 2 : ℝ)) := hc t ht0
    _ ≤ c * 1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)) hc0
    _ = c := mul_one c

/-! ## The local Taylor remainder on `|s| ≤ |t|/2` -/

/-- Lagrange form of the Taylor remainder of `I` at `t`, evaluated at `t - s`, when the closed
segment between `t` and `t - s` avoids the origin. -/
theorem fhpbb2a_taylor (n : ℕ) {t s : ℝ} (hs : s ≠ 0) (hseg : ∀ y ∈ uIcc t (t - s), y ≠ 0) :
    ∃ y ∈ uIoo t (t - s),
      |t - s| ^ (-(1 / 2 : ℝ)) - ∑ k ∈ Finset.range (n + 1),
          iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k =
        iteratedDeriv (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y * (-s) ^ (n + 1) /
          ((n + 1)! : ℝ) := by
  have hts : t ≠ t - s := by
    intro h
    apply hs
    linarith
  have hcd : ContDiffOn ℝ (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (uIcc t (t - s)) :=
    fun y hy => (fhpbb2a_contDiffAt _ (hseg y hy)).contDiffWithinAt
  obtain ⟨y, hy, hT⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hts hcd
  refine ⟨y, hy, ?_⟩
  have hsum : taylorWithinEval (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) n (uIcc t (t - s)) t (t - s) =
      ∑ k ∈ Finset.range (n + 1),
        iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hts)
      (fhpbb2a_contDiffAt _ (hseg t left_mem_uIcc)) left_mem_uIcc, smul_eq_mul,
      sub_sub_cancel_left]
    ring
  have h2 : t - s - t = -s := sub_sub_cancel_left t s
  rw [h2] at hT
  rw [← hsum]
  exact hT

/-- **Local Taylor part.** For `N = n + 1`, `|t| ≥ 1`, `0 < |s| ≤ |t|/2`:
`|t|^N |R_N(t,s)| ≤ A |s|^N`. -/
theorem fhpbb2a_near (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t s : ℝ, 1 ≤ |t| → s ≠ 0 → |s| ≤ |t| / 2 →
      |t| ^ (n + 1) * |(|t - s| ^ (-(1 / 2 : ℝ)) - ∑ k ∈ Finset.range (n + 1),
          iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k)| ≤
        A * |s| ^ (n + 1) := by
  obtain ⟨p, hp0, hp⟩ := fhpbb2a_deriv_bound (n + 1)
  have hc0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hfac : (0 : ℝ) < ((n + 1)! : ℝ) := by positivity
  refine ⟨2 ^ (n + 1) * p * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) / ((n + 1)! : ℝ),
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) hp0) hc0) hfac.le,
    fun t s ht hs hst => ?_⟩
  have hseg : ∀ y ∈ uIcc t (t - s), |t| / 2 ≤ |y| := by
    intro y hy
    have h1 : |y - t| ≤ |t - s - t| := abs_sub_left_of_mem_uIcc hy
    rw [sub_sub_cancel_left, abs_neg] at h1
    have h2 : |t| - |y| ≤ |t - y| := abs_sub_abs_le_abs_sub t y
    rw [abs_sub_comm] at h2
    linarith
  have hne : ∀ y ∈ uIcc t (t - s), y ≠ 0 := fun y hy h0 => by
    have h := hseg y hy
    rw [h0, abs_zero] at h
    linarith
  obtain ⟨y, hy, hT⟩ := fhpbb2a_taylor n hs hne
  have hyt : |t| / 2 ≤ |y| := hseg y (uIoo_subset_uIcc_self hy)
  have hy0 : y ≠ 0 := hne y (uIoo_subset_uIcc_self hy)
  have hkey : |t| ^ (n + 1) * |iteratedDeriv (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y| ≤
      2 ^ (n + 1) * p * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have h1 : |t| ^ (n + 1) ≤ (2 * |y|) ^ (n + 1) :=
      pow_le_pow_left₀ (abs_nonneg t) (by linarith) _
    have h2 : |y| ^ (-(1 / 2 : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
    calc |t| ^ (n + 1) * |iteratedDeriv (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y|
        ≤ (2 * |y|) ^ (n + 1) *
            |iteratedDeriv (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = 2 ^ (n + 1) *
            (|iteratedDeriv (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y| * |y| ^ (n + 1)) := by
          ring
      _ = 2 ^ (n + 1) * (p * |y| ^ (-(1 / 2 : ℝ))) := by rw [hp y hy0]
      _ ≤ 2 ^ (n + 1) * (p * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hp0) (by positivity)
      _ = 2 ^ (n + 1) * p * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
  rw [hT, abs_div, abs_mul, abs_pow, abs_neg, Nat.abs_cast]
  calc |t| ^ (n + 1) * (|iteratedDeriv (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y| *
          |s| ^ (n + 1) / ((n + 1)! : ℝ))
      = (|t| ^ (n + 1) * |iteratedDeriv (n + 1) (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) y|) *
          |s| ^ (n + 1) / ((n + 1)! : ℝ) := by ring
    _ ≤ (2 ^ (n + 1) * p * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) * |s| ^ (n + 1) / ((n + 1)! : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkey (by positivity)) hfac.le
    _ = 2 ^ (n + 1) * p * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) / ((n + 1)! : ℝ) * |s| ^ (n + 1) := by
        ring

/-! ## The restored polynomial terms -/

/-- For `|t| ≥ 1`: `|Σ_{k<N} I^{(k)}(t) (-s)^k / k!| ≤ S (1 + |s|)^N`. -/
theorem fhpbb2a_sum_bound (N : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t s : ℝ, 1 ≤ |t| →
      |∑ k ∈ Finset.range N,
          iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k| ≤
        S * (1 + |s|) ^ N := by
  choose c hc0 hc using fhpbb2a_deriv_bound
  refine ⟨∑ k ∈ Finset.range N, c k / (k ! : ℝ),
    Finset.sum_nonneg fun k _ => div_nonneg (hc0 k) (Nat.cast_nonneg _), fun t s ht => ?_⟩
  have hs1 : (1 : ℝ) ≤ 1 + |s| := le_add_of_nonneg_right (abs_nonneg s)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_div, abs_pow, abs_neg, Nat.abs_cast]
  have hsk : |s| ^ k ≤ (1 + |s|) ^ N :=
    (pow_le_pow_left₀ (abs_nonneg s) (by linarith) k).trans
      (pow_le_pow_right₀ hs1 (Finset.mem_range.mp hk).le)
  exact mul_le_mul
    (div_le_div_of_nonneg_right (fhpbb2a_abs_iteratedDeriv_le (hc0 k) (hc k) ht)
      (Nat.cast_nonneg _))
    hsk (by positivity) (div_nonneg (hc0 k) (Nat.cast_nonneg _))

/-! ## The pointwise remainder bound (both regions; `N = 0` separately) -/

/-- For `|t| ≥ 1` and `s ≠ 0`:
`|t|^N |R_N(t,s)| ≤ A (1+|s|)^{2N} + 2^N (1+|s|)^N |t - s|^{-1/2}`. -/
theorem fhpbb2a_pointwise (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t s : ℝ, 1 ≤ |t| → s ≠ 0 →
      |t| ^ N * |(|t - s| ^ (-(1 / 2 : ℝ)) - ∑ k ∈ Finset.range N,
          iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k)| ≤
        A * (1 + |s|) ^ (2 * N) + 2 ^ N * (1 + |s|) ^ N * |t - s| ^ (-(1 / 2 : ℝ)) := by
  cases N with
  | zero =>
    refine ⟨0, le_rfl, fun t s _ _ => ?_⟩
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty, sub_zero, one_mul, zero_mul,
      zero_add, mul_zero]
    exact le_of_eq (abs_of_nonneg (by positivity))
  | succ n =>
    obtain ⟨A0, hA0, hA⟩ := fhpbb2a_near n
    obtain ⟨S, hS0, hS⟩ := fhpbb2a_sum_bound (n + 1)
    refine ⟨A0 + 2 ^ (n + 1) * S, add_nonneg hA0 (mul_nonneg (by positivity) hS0),
      fun t s ht hs => ?_⟩
    have hs1 : (1 : ℝ) ≤ 1 + |s| := le_add_of_nonneg_right (abs_nonneg s)
    have hI0 : 0 ≤ |t - s| ^ (-(1 / 2 : ℝ)) := by positivity
    have hQ0 : 0 ≤ (1 + |s|) ^ (2 * (n + 1)) := by positivity
    have hZ0 : 0 ≤ 2 ^ (n + 1) * (1 + |s|) ^ (n + 1) * |t - s| ^ (-(1 / 2 : ℝ)) := by
      positivity
    have hYQ : 0 ≤ 2 ^ (n + 1) * S * (1 + |s|) ^ (2 * (n + 1)) :=
      mul_nonneg (mul_nonneg (by positivity) hS0) hQ0
    have hAQ : 0 ≤ A0 * (1 + |s|) ^ (2 * (n + 1)) := mul_nonneg hA0 hQ0
    by_cases hst : |s| ≤ |t| / 2
    · have h2 : |s| ^ (n + 1) ≤ (1 + |s|) ^ (2 * (n + 1)) :=
        (pow_le_pow_left₀ (abs_nonneg s) (by linarith) _).trans
          (pow_le_pow_right₀ hs1 (by omega))
      calc _ ≤ A0 * |s| ^ (n + 1) := hA t s ht hs hst
        _ ≤ A0 * (1 + |s|) ^ (2 * (n + 1)) := mul_le_mul_of_nonneg_left h2 hA0
        _ ≤ A0 * (1 + |s|) ^ (2 * (n + 1)) + (2 ^ (n + 1) * S * (1 + |s|) ^ (2 * (n + 1)) +
              2 ^ (n + 1) * (1 + |s|) ^ (n + 1) * |t - s| ^ (-(1 / 2 : ℝ))) :=
            le_add_of_nonneg_right (add_nonneg hYQ hZ0)
        _ = (A0 + 2 ^ (n + 1) * S) * (1 + |s|) ^ (2 * (n + 1)) +
              2 ^ (n + 1) * (1 + |s|) ^ (n + 1) * |t - s| ^ (-(1 / 2 : ℝ)) := by ring
    · have hT : |t| ^ (n + 1) ≤ 2 ^ (n + 1) * (1 + |s|) ^ (n + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg t) (by linarith [not_le.mp hst]) _
      have hR : |(|t - s| ^ (-(1 / 2 : ℝ)) - ∑ k ∈ Finset.range (n + 1),
            iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k)| ≤
          |t - s| ^ (-(1 / 2 : ℝ)) + S * (1 + |s|) ^ (n + 1) := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg hI0]
        exact add_le_add le_rfl (hS t s ht)
      calc _ ≤ (2 ^ (n + 1) * (1 + |s|) ^ (n + 1)) *
              (|t - s| ^ (-(1 / 2 : ℝ)) + S * (1 + |s|) ^ (n + 1)) :=
            mul_le_mul hT hR (abs_nonneg _) (by positivity)
        _ = 2 ^ (n + 1) * S * (1 + |s|) ^ (2 * (n + 1)) +
              2 ^ (n + 1) * (1 + |s|) ^ (n + 1) * |t - s| ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ A0 * (1 + |s|) ^ (2 * (n + 1)) + (2 ^ (n + 1) * S * (1 + |s|) ^ (2 * (n + 1)) +
              2 ^ (n + 1) * (1 + |s|) ^ (n + 1) * |t - s| ^ (-(1 / 2 : ℝ))) :=
            le_add_of_nonneg_left hAQ
        _ = (A0 + 2 ^ (n + 1) * S) * (1 + |s|) ^ (2 * (n + 1)) +
              2 ^ (n + 1) * (1 + |s|) ^ (n + 1) * |t - s| ^ (-(1 / 2 : ℝ)) := by ring

/-! ## The remote singularity: `∫ (1+|s|)^{-2} |t - s|^{-1/2} ds ≤ 6` for every `t` -/

theorem fhpbb2a_integrable_weight : Integrable (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  refine h.congr (ae_of_all _ fun s => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + |s|), Real.rpow_two]

theorem fhpbb2a_integral_Ioi_weight : ∫ y in Ioi (0 : ℝ), ((1 + y) ^ 2)⁻¹ = 1 := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => -(1 + y)⁻¹) (((1 + x) ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hx' : (1 : ℝ) + x ≠ 0 := (by linarith : (0 : ℝ) < 1 + x).ne'
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id' x).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-1 / (1 + x) ^ 2) x := h1.inv hx'
    have h3 : HasDerivAt (fun y : ℝ => -(1 + y)⁻¹) (-(-1 / (1 + x) ^ 2)) x := h2.neg
    exact h3.congr_deriv (by ring)
  have hcont : ContinuousWithinAt (fun y : ℝ => -(1 + y)⁻¹) (Ici 0) 0 := by
    have h : ContinuousAt (fun y : ℝ => -(1 + y)⁻¹) 0 :=
      ((continuousAt_const.add continuousAt_id).inv₀ (by norm_num)).neg
    exact h.continuousWithinAt
  have hint : IntegrableOn (fun y : ℝ => ((1 + y) ^ 2)⁻¹) (Ioi 0) := by
    refine (fhpbb2a_integrable_weight.integrableOn).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := hy
    simp only [abs_of_pos hy0]
  have htend : Tendsto (fun y : ℝ => -(1 + y)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 1 + y) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 tendsto_id
    have h2 := (tendsto_inv_atTop_zero.comp h1).neg
    rw [neg_zero] at h2
    exact h2
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  norm_num

/-- `∫ (1+|s|)^{-2} ds = 2`. -/
theorem fhpbb2a_integral_weight : ∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹ = 2 := by
  have h : ∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹ = 2 * ∫ y in Ioi (0 : ℝ), ((1 + y) ^ 2)⁻¹ :=
    integral_comp_abs (f := fun y : ℝ => ((1 + y) ^ 2)⁻¹)
  rw [h, fhpbb2a_integral_Ioi_weight, mul_one]

theorem fhpbb2a_locallyIntegrable_inverseHalf :
    LocallyIntegrable (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) := by
  refine locallyIntegrable_of_norm_le_rpow (μ := volume) (C := 1) (α := 1 / 2) (by simp)
    (by norm_num) (ae_of_all _ fun x => ?_)
    ((continuous_abs.measurable.pow_const _).aestronglyMeasurable)
  simp only [Real.norm_eq_abs, one_mul]
  exact le_of_eq (abs_of_nonneg (by positivity))

theorem fhpbb2a_integrable_indicator :
    Integrable ((Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))) :=
  (fhpbb2a_locallyIntegrable_inverseHalf.integrableOn_isCompact isCompact_Icc).integrable_indicator
    measurableSet_Icc

/-- `∫_{-1}^{1} |u|^{-1/2} du = 4`. -/
theorem fhpbb2a_integral_indicator :
    ∫ u : ℝ, (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) u = 4 := by
  have hpt : ∀ u : ℝ, (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) u =
      (Iic (1 : ℝ)).indicator (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) |u| := by
    intro u
    by_cases h : |u| ≤ 1
    · rw [Set.indicator_of_mem (show u ∈ Icc (-1 : ℝ) 1 from abs_le.mp h),
        Set.indicator_of_mem (show |u| ∈ Iic (1 : ℝ) from h)]
    · rw [Set.indicator_of_notMem (show u ∉ Icc (-1 : ℝ) 1 from fun hu => h (abs_le.mpr hu)),
        Set.indicator_of_notMem (show |u| ∉ Iic (1 : ℝ) from h)]
  have h1 : ∫ u : ℝ, (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) u =
      2 * ∫ y in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) y := by
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact integral_comp_abs (f := (Iic (1 : ℝ)).indicator (fun y : ℝ => y ^ (-(1 / 2 : ℝ))))
  rw [h1, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, Real.one_rpow,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  norm_num

theorem fhpbb2a_remote_pointwise (t s : ℝ) :
    ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)) ≤
      ((1 + |s|) ^ 2)⁻¹ + (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (t - s) := by
  have hw0 : 0 ≤ ((1 + |s|) ^ 2)⁻¹ := by positivity
  have hw1 : ((1 + |s|) ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg s)))
  have hI0 : 0 ≤ |t - s| ^ (-(1 / 2 : ℝ)) := by positivity
  by_cases h : |t - s| ≤ 1
  · rw [Set.indicator_of_mem (show t - s ∈ Icc (-1 : ℝ) 1 from abs_le.mp h)]
    have h' : ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)) ≤ |t - s| ^ (-(1 / 2 : ℝ)) := by
      calc ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)) ≤ 1 * |t - s| ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hw1 hI0
        _ = |t - s| ^ (-(1 / 2 : ℝ)) := one_mul _
    linarith
  · rw [Set.indicator_of_notMem (show t - s ∉ Icc (-1 : ℝ) 1 from fun hm => h (abs_le.mpr hm)),
      add_zero]
    have hI1 : |t - s| ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt (not_le.mp h)) (by norm_num)
    calc ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)) ≤ ((1 + |s|) ^ 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hI1 hw0
      _ = ((1 + |s|) ^ 2)⁻¹ := mul_one _

/-- **Remote singularity estimate**: for every `t`,
`s ↦ (1+|s|)^{-2} |t - s|^{-1/2}` is integrable and `∫ (1+|s|)^{-2} |t - s|^{-1/2} ds ≤ 6`
(the regions `|t - s| ≤ 1` and `|t - s| > 1` contribute at most `4` and `2`). -/
theorem fhpbb2a_remote (t : ℝ) :
    Integrable (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ))) ∧
      ∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)) ≤ 6 := by
  have hw := fhpbb2a_integrable_weight
  have hJt : Integrable (fun s : ℝ =>
      (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (t - s)) :=
    fhpbb2a_integrable_indicator.comp_sub_left t
  have hdom : Integrable (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹ +
      (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (t - s)) := hw.add hJt
  have hwc : Continuous (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) :=
    Continuous.inv₀ ((continuous_const.add continuous_abs).pow 2) (fun s => by positivity)
  have hmeasI : Measurable (fun s : ℝ => |t - s| ^ (-(1 / 2 : ℝ))) :=
    (continuous_abs.measurable.pow_const _).comp (measurable_const.sub measurable_id)
  have hint : Integrable (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ))) := by
    refine hdom.mono' (hwc.measurable.mul hmeasI).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (by positivity : (0 : ℝ) ≤ ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)))]
    exact fhpbb2a_remote_pointwise t s
  refine ⟨hint, ?_⟩
  calc ∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ))
      ≤ ∫ s : ℝ, (((1 + |s|) ^ 2)⁻¹ +
          (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (t - s)) :=
        integral_mono hint hdom (fun s => fhpbb2a_remote_pointwise t s)
    _ = (∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹) +
          ∫ s : ℝ, (Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) (t - s) :=
        integral_add hw hJt
    _ = 2 + 4 := by
        rw [fhpbb2a_integral_weight,
          integral_sub_left_eq_self
            ((Icc (-1 : ℝ) 1).indicator (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ)))) volume t,
          fhpbb2a_integral_indicator]
    _ = 6 := by norm_num

/-! ## Schwartz decay and the restored moments -/

/-- Arbitrary polynomial decay of a Schwartz function against the weight `(1+|s|)^{-2}`. -/
theorem fhpbb2a_decay_weight (ρ : 𝓢(ℝ, ℝ)) (M : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j ≤ M, ∀ s : ℝ, (1 + |s|) ^ j * |ρ s| ≤ B * ((1 + |s|) ^ 2)⁻¹ := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ s : ℝ, (1 + |s|) ^ (M + 2) * |ρ s| ≤ B := by
    refine ⟨2 ^ (M + 2, 0).1 *
      ((Finset.Iic (M + 2, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ρ, fun s => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (M + 2, 0))
      (k := M + 2) (n := 0) le_rfl le_rfl ρ s
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    exact h
  refine ⟨B, le_trans (by positivity) (hB 0), fun j hj s => ?_⟩
  have hs1 : (1 : ℝ) ≤ 1 + |s| := le_add_of_nonneg_right (abs_nonneg s)
  have hpos : (0 : ℝ) < (1 + |s|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc (1 + |s|) ^ j * |ρ s| * (1 + |s|) ^ 2 = (1 + |s|) ^ (j + 2) * |ρ s| := by ring
    _ ≤ (1 + |s|) ^ (M + 2) * |ρ s| :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs1 (by omega)) (abs_nonneg _)
    _ ≤ B := hB s

theorem fhpbb2a_integrable_mul_pow (ρ : 𝓢(ℝ, ℝ)) (k : ℕ) (c : ℝ) :
    Integrable (fun s : ℝ => ρ s * (c * (-s) ^ k)) := by
  refine ((ρ.integrable_pow_mul volume k).const_mul |c|).mono'
    (ρ.continuous.mul (continuous_const.mul (continuous_neg.pow k))).aestronglyMeasurable
    (ae_of_all _ fun s => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg]
  exact le_of_eq (by ring)

/-- **Restored moments.** The expansion error is the integral of `ρ` against the Taylor
remainder `R_N(t, ·)`, for arbitrary coefficients `D k` (here `D k = I^{(k)}(t)`). -/
theorem fhpbb2a_moment_identity (ρ : 𝓢(ℝ, ℝ)) (N : ℕ) (t : ℝ) (D : ℕ → ℝ)
    (hint : Integrable (fun s : ℝ => ρ s * |t - s| ^ (-(1 / 2 : ℝ)))) :
    (∫ s : ℝ, ρ s * |t - s| ^ (-(1 / 2 : ℝ))) -
        ∑ k ∈ Finset.range N, ((-1 : ℝ) ^ k / (k.factorial : ℝ) * ∫ s : ℝ, s ^ k * ρ s) * D k =
      ∫ s : ℝ, ρ s * (|t - s| ^ (-(1 / 2 : ℝ)) -
        ∑ k ∈ Finset.range N, D k / (k ! : ℝ) * (-s) ^ k) := by
  have hterm : ∀ k ∈ Finset.range N,
      Integrable (fun s : ℝ => ρ s * (D k / (k ! : ℝ) * (-s) ^ k)) :=
    fun k _ => fhpbb2a_integrable_mul_pow ρ k (D k / (k ! : ℝ))
  have hk : ∀ k ∈ Finset.range N,
      ((-1 : ℝ) ^ k / (k.factorial : ℝ) * ∫ s : ℝ, s ^ k * ρ s) * D k =
        ∫ s : ℝ, ρ s * (D k / (k ! : ℝ) * (-s) ^ k) := by
    intro k _
    have h1 : ∫ s : ℝ, ρ s * (D k / (k ! : ℝ) * (-s) ^ k) =
        ∫ s : ℝ, ((-1 : ℝ) ^ k / (k ! : ℝ) * D k) * (s ^ k * ρ s) :=
      integral_congr_ae (ae_of_all _ fun s => by rw [neg_pow]; ring)
    rw [h1, integral_const_mul]
    ring
  have hsum : ∫ s : ℝ, ∑ k ∈ Finset.range N, ρ s * (D k / (k ! : ℝ) * (-s) ^ k) =
      ∑ k ∈ Finset.range N, ∫ s : ℝ, ρ s * (D k / (k ! : ℝ) * (-s) ^ k) :=
    integral_finsetSum _ hterm
  rw [Finset.sum_congr rfl hk, ← hsum, ← integral_sub hint (integrable_finsetSum _ hterm)]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [mul_sub, Finset.mul_sum]

/-! ## The asymptotic expansion -/

/-- **The asymptotic expansion of `ρ * |·|^{-1/2}`**: for a real Schwartz
`ρ` and every `N` there is `C` with, for every `|t| ≥ 1`,
`|∫ ρ(s) |t - s|^{-1/2} ds - Σ_{k<N} ((-1)^k / k!) (∫ s^k ρ) I^{(k)}(t)| ≤ C |t|^{-N}`. -/
theorem fhpbb2a_inverseHalf_asymptotic (ρ : 𝓢(ℝ, ℝ)) (N : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      |(∫ s : ℝ, ρ s * |t - s| ^ (-(1 / 2 : ℝ))) -
          ∑ k ∈ Finset.range N,
            ((-1 : ℝ) ^ k / (k.factorial : ℝ) * ∫ s : ℝ, s ^ k * ρ s) *
              iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t| ≤
        C * |t| ^ (-(N : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := fhpbb2a_pointwise N
  obtain ⟨B, hB0, hB⟩ := fhpbb2a_decay_weight ρ (2 * N)
  refine ⟨B * (A * 2 + 2 ^ N * 6), fun t ht => ?_⟩
  have htN : 0 < |t| ^ N := pow_pos (by linarith) N
  have hrem := fhpbb2a_remote t
  have hw := fhpbb2a_integrable_weight
  have hmeasI : Measurable (fun s : ℝ => |t - s| ^ (-(1 / 2 : ℝ))) :=
    (continuous_abs.measurable.pow_const _).comp (measurable_const.sub measurable_id)
  have hint : Integrable (fun s : ℝ => ρ s * |t - s| ^ (-(1 / 2 : ℝ))) := by
    refine (hrem.1.const_mul B).mono' (ρ.continuous.measurable.mul hmeasI).aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |t - s| ^ (-(1 / 2 : ℝ))), ← mul_assoc]
    have h0 := hB 0 (Nat.zero_le _) s
    rw [pow_zero, one_mul] at h0
    exact mul_le_mul_of_nonneg_right h0 (by positivity)
  rw [fhpbb2a_moment_identity ρ N t _ hint, Real.rpow_neg (abs_nonneg t), Real.rpow_natCast]
  have hg : Integrable (fun s : ℝ => (|t| ^ N)⁻¹ * (B * A * ((1 + |s|) ^ 2)⁻¹ +
      B * 2 ^ N * (((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ))))) :=
    ((hw.const_mul (B * A)).add (hrem.1.const_mul (B * 2 ^ N))).const_mul _
  have hbd : ∀ᵐ s : ℝ, ‖ρ s * (|t - s| ^ (-(1 / 2 : ℝ)) - ∑ k ∈ Finset.range N,
        iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k)‖ ≤
      (|t| ^ N)⁻¹ * (B * A * ((1 + |s|) ^ 2)⁻¹ +
        B * 2 ^ N * (((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)))) := by
    filter_upwards [Measure.ae_ne volume 0] with s hs
    rw [Real.norm_eq_abs, abs_mul, le_inv_mul_iff₀ htN]
    have h1 := hA t s ht hs
    have h2 := hB (2 * N) le_rfl s
    have h3 := hB N (by omega) s
    have hI0 : 0 ≤ |t - s| ^ (-(1 / 2 : ℝ)) := by positivity
    calc _ = |ρ s| * (|t| ^ N * |(|t - s| ^ (-(1 / 2 : ℝ)) - ∑ k ∈ Finset.range N,
            iteratedDeriv k (fun x : ℝ => |x| ^ (-(1 / 2 : ℝ))) t / (k ! : ℝ) * (-s) ^ k)|) := by
          ring
      _ ≤ |ρ s| * (A * (1 + |s|) ^ (2 * N) +
            2 ^ N * (1 + |s|) ^ N * |t - s| ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = A * ((1 + |s|) ^ (2 * N) * |ρ s|) +
            2 ^ N * |t - s| ^ (-(1 / 2 : ℝ)) * ((1 + |s|) ^ N * |ρ s|) := by ring
      _ ≤ A * (B * ((1 + |s|) ^ 2)⁻¹) +
            2 ^ N * |t - s| ^ (-(1 / 2 : ℝ)) * (B * ((1 + |s|) ^ 2)⁻¹) :=
          add_le_add (mul_le_mul_of_nonneg_left h2 hA0)
            (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ = B * A * ((1 + |s|) ^ 2)⁻¹ +
            B * 2 ^ N * (((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ))) := by ring
  refine (le_of_eq (Real.norm_eq_abs _).symm).trans
    ((norm_integral_le_of_norm_le hg hbd).trans ?_)
  rw [integral_const_mul, integral_add (hw.const_mul (B * A)) (hrem.1.const_mul (B * 2 ^ N)),
    integral_const_mul, integral_const_mul, fhpbb2a_integral_weight]
  have h6 : B * 2 ^ N * ∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)) ≤
      B * 2 ^ N * 6 :=
    mul_le_mul_of_nonneg_left hrem.2 (mul_nonneg hB0 (by positivity))
  refine (mul_le_mul_of_nonneg_left (add_le_add le_rfl h6) (inv_nonneg.mpr htN.le)).trans
    (le_of_eq (by ring))

end ParabolicRectifiability.FractionalKernel
