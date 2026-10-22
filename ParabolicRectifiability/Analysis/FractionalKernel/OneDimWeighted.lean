import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The weighted one-dimensional half-derivative estimate

One-dimensional analysis; this module depends on Mathlib only and works
with an arbitrary real normalization `κ`.

For `f : ℝ → ℂ` write `D f(t) = κ ∫ |h|^{-3/2} (f(t) - f(t-h)) dh` (a Bochner integral, `0` at a
time where the `h`-integrand is not integrable; `|0|^{-3/2} = 0` by `Real.rpow`). Main result
(`fhpbb1w_oneDimWeighted`): there is `C ≥ 0` such that for every integrable `C¹` function `f`
with `∫ f = 0`,
`∫⁻ (1 + √|t|) ‖D f(t)‖ₑ dt ≤ C ∫⁻ (1 + |t|) (‖f(t)‖ₑ + ‖f'(t)‖ₑ) dt`.

Proof, in two steps. Split `|h|^{-3/2} = n(h) + a(h)` with the near part
`n = 1_{|h| ≤ 1} |h|^{-3/2}` (`fhpbb1w_near`) and the far part `a = 1_{|h| > 1} |h|^{-3/2}`
(`fhpbb1w_far`).
* Step 1, the shift-weight bound (shiftweight) (`fhpbb1w_shiftWeight`):
  `∫⁻ (1 + √|t|) |a(t-s) - a(t)| dt ≤ (1 + |s|) · 36 ‖a‖₁`. On `|t| ≤ 2|s| + 4` the two terms are
  bounded separately; on the complement both arguments exceed `1`, both lie in `[|t|/2, ∞)`, and
  the mean value theorem for `x^{-3/2}` is used only there (`fhpbb1w_shift_pointwise`).
* Pointwise identity (`fhpbb1w_pointwise`): at a time where the `h`-integrand is integrable,
  `∫ |h|^{-3/2} (f(t) - f(t-h)) dh = ∫ n(h) (f(t) - f(t-h)) dh + ∫ a(h) f(t) dh
  - ∫ (a(t-s) - a(t)) f(s) ds`, the last step using `∫ f = 0`.
* Local part (`fhpbb1w_local`): `f(t) - f(t-h) = -∫_0^1 (-h) f'(t - αh) dα`, the weight comparison
  `1 + √|t| ≤ 2 (1 + |t - αh|)` for `|h| ≤ 1`, Tonelli and translation invariance.
* Far part (`fhpbb1w_far_tonelli`): Tonelli in `(t, s)` and (shiftweight).
Every estimate is an inequality of extended nonnegative integrals; no finiteness of the right
side is assumed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.FractionalKernel

/-! ## The near and far parts of the kernel -/

/-- The near part `1_{|h| ≤ 1} |h|^{-3/2}` of the kernel `|h|^{-3/2}`. -/
def fhpbb1w_near (h : ℝ) : ℝ := if |h| ≤ 1 then |h| ^ (-3 / 2 : ℝ) else 0

/-- The far part `a(h) = 1_{|h| > 1} |h|^{-3/2}` of the kernel `|h|^{-3/2}`. -/
def fhpbb1w_far (h : ℝ) : ℝ := if 1 < |h| then |h| ^ (-3 / 2 : ℝ) else 0

/-- `‖a‖₁` as an extended integral. -/
def fhpbb1w_farMass : ℝ≥0∞ := ∫⁻ h, ENNReal.ofReal (fhpbb1w_far h)

/-- The local constant `∫⁻ n(h) |h| dh = ∫_{|h| ≤ 1} |h|^{-1/2} dh`. -/
def fhpbb1w_nearMass : ℝ≥0∞ := ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖h‖ₑ

theorem fhpbb1w_near_add_far (h : ℝ) : fhpbb1w_near h + fhpbb1w_far h = |h| ^ (-3 / 2 : ℝ) := by
  unfold fhpbb1w_near fhpbb1w_far
  by_cases h1 : |h| ≤ 1
  · rw [ite_eq_left h1, ite_eq_right (not_lt.mpr h1), add_zero]
  · rw [ite_eq_right h1, ite_eq_left (not_le.mp h1), zero_add]

theorem fhpbb1w_near_nonneg (h : ℝ) : 0 ≤ fhpbb1w_near h := by
  unfold fhpbb1w_near
  split_ifs
  · exact Real.rpow_nonneg (abs_nonneg h) _
  · exact le_rfl

theorem fhpbb1w_far_nonneg (h : ℝ) : 0 ≤ fhpbb1w_far h := by
  unfold fhpbb1w_far
  split_ifs
  · exact Real.rpow_nonneg (abs_nonneg h) _
  · exact le_rfl

theorem fhpbb1w_measurable_near : Measurable fhpbb1w_near :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (continuous_abs.measurable.pow_const _) measurable_const

theorem fhpbb1w_measurable_far : Measurable fhpbb1w_far :=
  Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
    (continuous_abs.measurable.pow_const _) measurable_const

/-! ## Elementary real inequalities -/

theorem fhpbb1w_sqrt_le {x y : ℝ} (hy : 0 ≤ y) (hxy : x ≤ y ^ 2) : Real.sqrt x ≤ y :=
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt hxy
    _ = y := Real.sqrt_sq hy

theorem fhpbb1w_sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x :=
  fhpbb1w_sqrt_le (by linarith) (by nlinarith)

/-- `x^{-3/2} ≤ 4 (2x)^{-3/2}` for `x > 0` (since `2^{-3/2} ≥ 2^{-2} = 1/4`). -/
theorem fhpbb1w_rpow_le_four_mul {x : ℝ} (hx : 0 < x) :
    x ^ (-3 / 2 : ℝ) ≤ 4 * (2 * x) ^ (-3 / 2 : ℝ) := by
  rw [Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hx.le]
  have h2 : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (-3 / 2 : ℝ) := by
    calc (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num), Real.rpow_two]; norm_num
      _ ≤ (2 : ℝ) ^ (-3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hxp : 0 ≤ x ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  nlinarith

/-- The weight comparison of the local part: for `|h| ≤ 1` and `α ∈ [0,1]`,
`1 + √|t| ≤ 2 (1 + |t - αh|)`. -/
theorem fhpbb1w_weight_le {t h α : ℝ} (hh : |h| ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    1 + Real.sqrt |t| ≤ 2 * (1 + |t - α * h|) := by
  have h1 : |α * h| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hα0]
    calc α * |h| ≤ 1 * 1 := mul_le_mul hα1 hh (abs_nonneg h) zero_le_one
      _ = 1 := one_mul 1
  have h2 : |t| ≤ |t - α * h| + 1 := by
    have := abs_add_le (t - α * h) (α * h)
    rw [sub_add_cancel] at this
    linarith
  have hu := abs_nonneg (t - α * h)
  have h3 : Real.sqrt |t| ≤ 1 + |t - α * h| := fhpbb1w_sqrt_le (by linarith) (by nlinarith)
  linarith

/-- Mean value theorem for `x ↦ x^{-3/2}` on `[m, ∞)`, `m > 0`. -/
theorem fhpbb1w_rpow_sub_le {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |x ^ (-3 / 2 : ℝ) - y ^ (-3 / 2 : ℝ)| ≤ 3 / 2 * m ^ (-5 / 2 : ℝ) * |x - y| := by
  have hderiv : ∀ z ∈ Ici m, HasDerivWithinAt (fun z : ℝ => z ^ (-3 / 2 : ℝ))
      (-(3 / 2 * z ^ (-5 / 2 : ℝ))) (Ici m) z := by
    intro z hz
    have hz0 : z ≠ 0 := (lt_of_lt_of_le hm hz).ne'
    have hd := Real.hasDerivAt_rpow_const (p := (-3 / 2 : ℝ)) (Or.inl hz0)
    have he : (-3 / 2 : ℝ) * z ^ ((-3 / 2 : ℝ) - 1) = -(3 / 2 * z ^ (-5 / 2 : ℝ)) := by
      rw [show (-3 / 2 : ℝ) - 1 = -5 / 2 by norm_num]; ring
    exact (hd.congr_deriv he).hasDerivWithinAt
  have hbound : ∀ z ∈ Ici m, ‖-(3 / 2 * z ^ (-5 / 2 : ℝ))‖ ≤ 3 / 2 * m ^ (-5 / 2 : ℝ) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hm hz
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hz0.le _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm hz (by norm_num))
      (by norm_num)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Ici m)
    hy hx
  simpa only [Real.norm_eq_abs] using hmvt

/-! ## Integrability of the two kernel parts -/

theorem fhpbb1w_integrable_far : Integrable fhpbb1w_far := by
  have hmaj : Integrable (fun x : ℝ => 4 * (1 + ‖x‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2)
      (by norm_num [Module.finrank_self])).const_mul 4
  refine hmaj.mono' fhpbb1w_measurable_far.aestronglyMeasurable
    (Eventually.of_forall fun h => ?_)
  rw [Real.norm_of_nonneg (fhpbb1w_far_nonneg h), Real.norm_eq_abs]
  unfold fhpbb1w_far
  split_ifs with hh
  · have hp : 0 < |h| := by linarith
    calc |h| ^ (-3 / 2 : ℝ) ≤ 4 * (2 * |h|) ^ (-3 / 2 : ℝ) := fhpbb1w_rpow_le_four_mul hp
      _ ≤ 4 * (1 + |h|) ^ (-(3 / 2 : ℝ)) := by
          rw [show (-(3 / 2 : ℝ)) = -3 / 2 by norm_num]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num))
            (by norm_num)
  · positivity

theorem fhpbb1w_farMass_lt_top : fhpbb1w_farMass < ⊤ :=
  fhpbb1w_integrable_far.lintegral_lt_top

theorem fhpbb1w_near_enorm_le (h : ℝ) :
    ENNReal.ofReal (fhpbb1w_near h) * ‖h‖ₑ ≤
      (Icc (-1 : ℝ) 1).indicator (fun h => ENNReal.ofReal (|h| ^ (-(1 / 2 : ℝ)))) h := by
  by_cases hh : |h| ≤ 1
  · have hmem : h ∈ Icc (-1 : ℝ) 1 := abs_le.mp hh
    rw [Set.indicator_of_mem hmem, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (fhpbb1w_near_nonneg h)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [fhpbb1w_near, ite_eq_left hh]
    rcases eq_or_ne h 0 with rfl | h0
    · simp only [abs_zero, mul_zero]
      exact Real.rpow_nonneg le_rfl _
    · have hp : 0 < |h| := abs_pos.mpr h0
      refine le_of_eq ?_
      rw [show (-(1 / 2 : ℝ)) = -3 / 2 + 1 by norm_num, Real.rpow_add hp, Real.rpow_one]
  · have h0 : fhpbb1w_near h = 0 := by rw [fhpbb1w_near, ite_eq_right hh]
    rw [h0, ENNReal.ofReal_zero, zero_mul]
    exact zero_le

theorem fhpbb1w_nearMass_lt_top : fhpbb1w_nearMass < ⊤ := by
  have hloc : LocallyIntegrable (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) volume := by
    refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1 / 2)
      (by norm_num [Module.finrank_self]) (by norm_num [Module.finrank_self])
      (Eventually.of_forall fun x => ?_) (continuous_abs.measurable.pow_const _).aestronglyMeasurable
    show ‖|x| ^ (-(1 / 2 : ℝ))‖ ≤ 1 * ‖x‖ ^ (-(1 / 2 : ℝ))
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
  have hI : IntegrableOn (fun h : ℝ => |h| ^ (-(1 / 2 : ℝ))) (Icc (-1) 1) :=
    hloc.integrableOn_isCompact isCompact_Icc
  calc fhpbb1w_nearMass = ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖h‖ₑ := rfl
    _ ≤ ∫⁻ h, (Icc (-1 : ℝ) 1).indicator (fun h => ENNReal.ofReal (|h| ^ (-(1 / 2 : ℝ)))) h :=
        lintegral_mono fun h => fhpbb1w_near_enorm_le h
    _ = ∫⁻ h in Icc (-1 : ℝ) 1, ENNReal.ofReal (|h| ^ (-(1 / 2 : ℝ))) :=
        lintegral_indicator measurableSet_Icc _
    _ < ⊤ := hI.setLIntegral_lt_top

/-! ## Step 1: the shift-weight bound (shiftweight) -/

/-- The pointwise form of (shiftweight): for all `s, t`,
`(1 + √|t|) |a(t-s) - a(t)| ≤ (1 + |s|) (6 a(t-s) + 30 a(t))`. On `|t| ≤ 2|s| + 4` the weight is
at most `6 (1 + |s|)`; on the complement the mean value theorem on `[|t|/2, ∞)` gives
`(1 + √|t|) |a(t-s) - a(t)| ≤ 24 |s| a(t)`. -/
theorem fhpbb1w_shift_pointwise (s t : ℝ) :
    (1 + Real.sqrt |t|) * |fhpbb1w_far (t - s) - fhpbb1w_far t| ≤
      (1 + |s|) * (6 * fhpbb1w_far (t - s) + 30 * fhpbb1w_far t) := by
  have hA := fhpbb1w_far_nonneg (t - s)
  have hB := fhpbb1w_far_nonneg t
  have hs0 := abs_nonneg s
  have hsq := fhpbb1w_sqrt_le_one_add (abs_nonneg t)
  have hsA := mul_nonneg hs0 hA
  have hsB := mul_nonneg hs0 hB
  by_cases hp : |t| ≤ 2 * |s| + 4
  · have hw : 1 + Real.sqrt |t| ≤ 6 * (1 + |s|) := by linarith
    have hΔ : |fhpbb1w_far (t - s) - fhpbb1w_far t| ≤ fhpbb1w_far (t - s) + fhpbb1w_far t :=
      abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    calc (1 + Real.sqrt |t|) * |fhpbb1w_far (t - s) - fhpbb1w_far t|
        ≤ (6 * (1 + |s|)) * (fhpbb1w_far (t - s) + fhpbb1w_far t) :=
          mul_le_mul hw hΔ (abs_nonneg _) (by positivity)
      _ ≤ (1 + |s|) * (6 * fhpbb1w_far (t - s) + 30 * fhpbb1w_far t) := by nlinarith
  · replace hp : 2 * |s| + 4 < |t| := not_le.mp hp
    have hp1 : 1 < |t| := by linarith
    have hts : |t| ≤ |t - s| + |s| := by
      have := abs_add_le (t - s) s
      rwa [sub_add_cancel] at this
    have hts1 : 1 < |t - s| := by linarith
    have hm : 0 < |t| / 2 := by linarith
    have hx : |t| / 2 ≤ |t - s| := by linarith
    have hy : |t| / 2 ≤ |t| := by linarith
    have hfarB : fhpbb1w_far t = |t| ^ (-3 / 2 : ℝ) := by rw [fhpbb1w_far, ite_eq_left hp1]
    have hfarA : fhpbb1w_far (t - s) = |t - s| ^ (-3 / 2 : ℝ) := by
      rw [fhpbb1w_far, ite_eq_left hts1]
    have hdiff : |(|t - s| - |t|)| ≤ |s| := by
      have := abs_abs_sub_abs_le_abs_sub (t - s) t
      rwa [show t - s - t = -s by ring, abs_neg] at this
    have hmvt := fhpbb1w_rpow_sub_le hm hx hy
    have hΔ : |fhpbb1w_far (t - s) - fhpbb1w_far t| ≤ 3 / 2 * (|t| / 2) ^ (-5 / 2 : ℝ) * |s| := by
      rw [hfarA, hfarB]
      exact hmvt.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))
    have hw : 1 + Real.sqrt |t| ≤ 4 * (|t| / 2) := by linarith
    have hm32 : (|t| / 2) * (|t| / 2) ^ (-5 / 2 : ℝ) = (|t| / 2) ^ (-3 / 2 : ℝ) := by
      rw [show (-3 / 2 : ℝ) = 1 + -5 / 2 by norm_num, Real.rpow_add hm, Real.rpow_one]
    have h4 : (|t| / 2) ^ (-3 / 2 : ℝ) ≤ 4 * fhpbb1w_far t := by
      rw [hfarB]
      have h4' := fhpbb1w_rpow_le_four_mul hm
      rwa [show 2 * (|t| / 2) = |t| by ring] at h4'
    have hprod : (1 + Real.sqrt |t|) * |fhpbb1w_far (t - s) - fhpbb1w_far t| ≤
        24 * |s| * fhpbb1w_far t := by
      calc (1 + Real.sqrt |t|) * |fhpbb1w_far (t - s) - fhpbb1w_far t|
          ≤ (4 * (|t| / 2)) * (3 / 2 * (|t| / 2) ^ (-5 / 2 : ℝ) * |s|) :=
            mul_le_mul hw hΔ (abs_nonneg _) (by positivity)
        _ = 6 * |s| * ((|t| / 2) * (|t| / 2) ^ (-5 / 2 : ℝ)) := by ring
        _ = 6 * |s| * (|t| / 2) ^ (-3 / 2 : ℝ) := by rw [hm32]
        _ ≤ 6 * |s| * (4 * fhpbb1w_far t) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 24 * |s| * fhpbb1w_far t := by ring
    nlinarith

theorem fhpbb1w_measurable_weight :
    Measurable fun t : ℝ => ENNReal.ofReal (1 + Real.sqrt |t|) :=
  (continuous_const.add (Real.continuous_sqrt.comp continuous_abs)).measurable.ennreal_ofReal

/-- **The shift-weight bound (shiftweight).** For every shift `s`,
`∫⁻ (1 + √|t|) |a(t-s) - a(t)| dt ≤ (1 + |s|) · 36 ‖a‖₁`, with `‖a‖₁ < ∞`
(`fhpbb1w_farMass_lt_top`). -/
theorem fhpbb1w_shiftWeight (s : ℝ) :
    ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
        ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| ≤
      ENNReal.ofReal (1 + |s|) * (36 * fhpbb1w_farMass) := by
  have hm1 : Measurable fun t : ℝ => ENNReal.ofReal (fhpbb1w_far (t - s)) :=
    (fhpbb1w_measurable_far.comp (measurable_id.sub_const s)).ennreal_ofReal
  have hm2 : Measurable fun t : ℝ => ENNReal.ofReal (fhpbb1w_far t) :=
    fhpbb1w_measurable_far.ennreal_ofReal
  have htr : ∫⁻ t, ENNReal.ofReal (fhpbb1w_far (t - s)) = fhpbb1w_farMass :=
    lintegral_sub_right_eq_self (fun h => ENNReal.ofReal (fhpbb1w_far h)) s
  calc ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
        ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t|
      ≤ ∫⁻ t, ENNReal.ofReal (1 + |s|) *
          (6 * ENNReal.ofReal (fhpbb1w_far (t - s)) + 30 * ENNReal.ofReal (fhpbb1w_far t)) := by
        refine lintegral_mono fun t => ?_
        beta_reduce
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + Real.sqrt |t| by positivity)]
        calc ENNReal.ofReal ((1 + Real.sqrt |t|) * |fhpbb1w_far (t - s) - fhpbb1w_far t|)
            ≤ ENNReal.ofReal ((1 + |s|) * (6 * fhpbb1w_far (t - s) + 30 * fhpbb1w_far t)) :=
              ENNReal.ofReal_le_ofReal (fhpbb1w_shift_pointwise s t)
          _ = ENNReal.ofReal (1 + |s|) *
                (6 * ENNReal.ofReal (fhpbb1w_far (t - s)) +
                  30 * ENNReal.ofReal (fhpbb1w_far t)) := by
              rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + |s| by positivity),
                ENNReal.ofReal_add (mul_nonneg (by norm_num) (fhpbb1w_far_nonneg _))
                  (mul_nonneg (by norm_num) (fhpbb1w_far_nonneg _)),
                ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num),
                ENNReal.ofReal_mul (show (0 : ℝ) ≤ 30 by norm_num),
                ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    _ = ENNReal.ofReal (1 + |s|) * (6 * fhpbb1w_farMass + 30 * fhpbb1w_farMass) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hm1.const_mul 6),
          lintegral_const_mul _ hm1, lintegral_const_mul _ hm2, htr]
        rfl
    _ = ENNReal.ofReal (1 + |s|) * (36 * fhpbb1w_farMass) := by ring

/-- (shiftweight) with a real constant: `∫ (1 + √|t|) |a(t-s) - a(t)| dt ≤ C (1 + |s|)`. -/
theorem fhpbb1w_shiftWeight_real :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ,
      ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
          ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| ≤
        ENNReal.ofReal (C * (1 + |s|)) := by
  have hfin : 36 * fhpbb1w_farMass ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) fhpbb1w_farMass_lt_top.ne
  refine ⟨(36 * fhpbb1w_farMass).toReal, ENNReal.toReal_nonneg, fun s => ?_⟩
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin,
    mul_comm (36 * fhpbb1w_farMass) (ENNReal.ofReal (1 + |s|))]
  exact fhpbb1w_shiftWeight s

/-! ## The pointwise splitting of the operator -/

theorem fhpbb1w_enorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |r| := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]

/-- **Pointwise identity.** For integrable `f` with `∫ f = 0` and every `t`,
`‖∫ |h|^{-3/2} (f t - f (t-h)) dh‖ₑ ≤ ∫⁻ n(h) ‖f t - f(t-h)‖ₑ dh + ‖a‖₁ ‖f t‖ₑ
+ ∫⁻ |a(t-s) - a(t)| ‖f s‖ₑ ds`. At a time where the `h`-integrand is not integrable the
Bochner integral is `0`. Otherwise the far part is `∫ a(h) f(t) dh - ∫ a(t-s) f(s) ds`, and
`∫ a(t) f(s) ds = a(t) ∫ f = 0`. -/
theorem fhpbb1w_pointwise (f : ℝ → ℂ) (hfi : Integrable f) (hf0 : ∫ t, f t = 0) (t : ℝ) :
    ‖∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ ≤
      (∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
        fhpbb1w_farMass * ‖f t‖ₑ +
        ∫⁻ s, ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ := by
  by_cases hg : Integrable (fun h : ℝ => ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h)))
  swap
  · rw [integral_undef hg, enorm_zero]
    exact zero_le
  have hN : Integrable (fun h : ℝ => ((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))) := by
    have hS : MeasurableSet {h : ℝ | |h| ≤ 1} :=
      measurableSet_le continuous_abs.measurable measurable_const
    refine (hg.indicator hS).congr (Eventually.of_forall fun h => ?_)
    by_cases hh : |h| ≤ 1 <;> simp [Set.indicator, fhpbb1w_near, hh]
  have hF : Integrable (fun h : ℝ => ((fhpbb1w_far h : ℝ) : ℂ) * (f t - f (t - h))) := by
    refine (hg.sub hN).congr (Eventually.of_forall fun h => ?_)
    simp only [Pi.sub_apply]
    rw [← fhpbb1w_near_add_far h]
    push_cast
    ring
  have hfarI : Integrable (fun h : ℝ => ((fhpbb1w_far h : ℝ) : ℂ)) :=
    fhpbb1w_integrable_far.ofReal
  have hFc : Integrable (fun h : ℝ => ((fhpbb1w_far h : ℝ) : ℂ) * f t) := hfarI.mul_const (f t)
  have hFs : Integrable (fun h : ℝ => ((fhpbb1w_far h : ℝ) : ℂ) * f (t - h)) := by
    refine (hFc.sub hF).congr (Eventually.of_forall fun h => ?_)
    simp only [Pi.sub_apply]
    ring
  have hsub : ∫ h : ℝ, ((fhpbb1w_far h : ℝ) : ℂ) * f (t - h) =
      ∫ s : ℝ, ((fhpbb1w_far (t - s) : ℝ) : ℂ) * f s := by
    have hs := integral_sub_left_eq_self (fun s : ℝ => ((fhpbb1w_far (t - s) : ℝ) : ℂ) * f s)
      (volume : Measure ℝ) t
    simp only [sub_sub_cancel] at hs
    exact hs
  have hFs' : Integrable (fun s : ℝ => ((fhpbb1w_far (t - s) : ℝ) : ℂ) * f s) := by
    have hs := hFs.comp_sub_left t
    simpa only [sub_sub_cancel] using hs
  have hcancel : ∫ s : ℝ, ((fhpbb1w_far (t - s) - fhpbb1w_far t : ℝ) : ℂ) * f s =
      ∫ s : ℝ, ((fhpbb1w_far (t - s) : ℝ) : ℂ) * f s := by
    have h1 : Integrable (fun s : ℝ => ((fhpbb1w_far t : ℝ) : ℂ) * f s) := hfi.const_mul _
    calc ∫ s : ℝ, ((fhpbb1w_far (t - s) - fhpbb1w_far t : ℝ) : ℂ) * f s
        = ∫ s : ℝ, (((fhpbb1w_far (t - s) : ℝ) : ℂ) * f s - ((fhpbb1w_far t : ℝ) : ℂ) * f s) := by
          congr 1
          ext s
          push_cast
          ring
      _ = (∫ s : ℝ, ((fhpbb1w_far (t - s) : ℝ) : ℂ) * f s) -
            ∫ s : ℝ, ((fhpbb1w_far t : ℝ) : ℂ) * f s := integral_sub hFs' h1
      _ = ∫ s : ℝ, ((fhpbb1w_far (t - s) : ℝ) : ℂ) * f s := by
          rw [integral_const_mul, hf0, mul_zero, sub_zero]
  have hid : ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h)) =
      (∫ h : ℝ, ((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))) +
        ((∫ h : ℝ, ((fhpbb1w_far h : ℝ) : ℂ) * f t) -
          ∫ s : ℝ, ((fhpbb1w_far (t - s) - fhpbb1w_far t : ℝ) : ℂ) * f s) := by
    calc ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))
        = ∫ h : ℝ, (((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h)) +
            ((fhpbb1w_far h : ℝ) : ℂ) * (f t - f (t - h))) := by
          congr 1
          ext h
          rw [← fhpbb1w_near_add_far h]
          push_cast
          ring
      _ = (∫ h : ℝ, ((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))) +
            ∫ h : ℝ, ((fhpbb1w_far h : ℝ) : ℂ) * (f t - f (t - h)) := integral_add hN hF
      _ = (∫ h : ℝ, ((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))) +
            ((∫ h : ℝ, ((fhpbb1w_far h : ℝ) : ℂ) * f t) -
              ∫ h : ℝ, ((fhpbb1w_far h : ℝ) : ℂ) * f (t - h)) := by
          rw [← integral_sub hFc hFs]
          congr 2
          ext h
          ring
      _ = _ := by rw [hsub, hcancel]
  rw [hid]
  have hn : ∫⁻ h, ‖((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))‖ₑ =
      ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ := by
    refine lintegral_congr fun h => ?_
    rw [enorm_mul, fhpbb1w_enorm_ofReal, abs_of_nonneg (fhpbb1w_near_nonneg h)]
  have hc : ∫⁻ h, ‖((fhpbb1w_far h : ℝ) : ℂ) * f t‖ₑ = fhpbb1w_farMass * ‖f t‖ₑ := by
    rw [fhpbb1w_farMass, ← lintegral_mul_const' _ _ enorm_ne_top]
    refine lintegral_congr fun h => ?_
    rw [enorm_mul, fhpbb1w_enorm_ofReal, abs_of_nonneg (fhpbb1w_far_nonneg h)]
  have hd : ∫⁻ s, ‖((fhpbb1w_far (t - s) - fhpbb1w_far t : ℝ) : ℂ) * f s‖ₑ =
      ∫⁻ s, ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ := by
    refine lintegral_congr fun s => ?_
    rw [enorm_mul, fhpbb1w_enorm_ofReal]
  calc ‖(∫ h : ℝ, ((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))) +
          ((∫ h : ℝ, ((fhpbb1w_far h : ℝ) : ℂ) * f t) -
            ∫ s : ℝ, ((fhpbb1w_far (t - s) - fhpbb1w_far t : ℝ) : ℂ) * f s)‖ₑ
      ≤ ‖∫ h : ℝ, ((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))‖ₑ +
          (‖∫ h : ℝ, ((fhpbb1w_far h : ℝ) : ℂ) * f t‖ₑ +
            ‖∫ s : ℝ, ((fhpbb1w_far (t - s) - fhpbb1w_far t : ℝ) : ℂ) * f s‖ₑ) :=
        (enorm_add_le _ _).trans (add_le_add le_rfl enorm_sub_le)
    _ ≤ (∫⁻ h, ‖((fhpbb1w_near h : ℝ) : ℂ) * (f t - f (t - h))‖ₑ) +
          ((∫⁻ h, ‖((fhpbb1w_far h : ℝ) : ℂ) * f t‖ₑ) +
            ∫⁻ s, ‖((fhpbb1w_far (t - s) - fhpbb1w_far t : ℝ) : ℂ) * f s‖ₑ) :=
        add_le_add (enorm_integral_le_lintegral_enorm _)
          (add_le_add (enorm_integral_le_lintegral_enorm _) (enorm_integral_le_lintegral_enorm _))
    _ = _ := by rw [hn, hc, hd, add_assoc]

/-! ## Step 2: the operator estimate -/

/-- `‖f t - f (t-h)‖ₑ ≤ ‖h‖ₑ ∫_0^1 ‖f'(t - αh)‖ₑ dα` for `C¹` `f` (fundamental theorem of
calculus along `α ↦ f (t - αh)`). -/
theorem fhpbb1w_enorm_sub_le (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (t h : ℝ) :
    ‖f t - f (t - h)‖ₑ ≤ ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1, ‖deriv f (t - α * h)‖ₑ := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hc : Continuous (deriv f) := hf.continuous_deriv_one
  have hderiv : ∀ α ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun α : ℝ => f (t - α * h))
      ((-h) • deriv f (t - α * h)) α := by
    intro α _
    have h1 : HasDerivAt (fun α : ℝ => t - α * h) (-h) α := (hasDerivAt_mul_const h).const_sub t
    have h2 := (hd (t - α * h)).hasDerivAt.scomp α h1
    exact h2
  have hin : Continuous fun α : ℝ => t - α * h := by fun_prop
  have hcont : Continuous fun α : ℝ => (-h) • deriv f (t - α * h) :=
    (hc.comp hin).const_smul (-h)
  have hint : IntervalIntegrable (fun α : ℝ => (-h) • deriv f (t - α * h)) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [one_mul, zero_mul, sub_zero] at hftc
  rw [enorm_sub_rev, ← hftc, intervalIntegral.integral_of_le zero_le_one]
  calc ‖∫ α in Ioc (0 : ℝ) 1, (-h) • deriv f (t - α * h)‖ₑ
      ≤ ∫⁻ α in Ioc (0 : ℝ) 1, ‖(-h) • deriv f (t - α * h)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ α in Ioc (0 : ℝ) 1, ‖h‖ₑ * ‖deriv f (t - α * h)‖ₑ := by
        refine lintegral_mono fun α => ?_
        beta_reduce
        rw [← enorm_neg h]
        exact enorm_smul_le
    _ = ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1, ‖deriv f (t - α * h)‖ₑ :=
        lintegral_const_mul' _ _ enorm_ne_top

theorem fhpbb1w_measurable_derivWeight (f : ℝ → ℂ) (hc : Continuous (deriv f)) :
    Measurable fun x : ℝ => ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ :=
  ((continuous_const.add continuous_abs).measurable.ennreal_ofReal).mul hc.measurable.enorm

/-- The local part for one shift `|h| ≤ 1`:
`∫⁻ (1 + √|t|) ‖f t - f (t-h)‖ₑ dt ≤ ‖h‖ₑ · 2 ∫⁻ (1 + |x|) ‖f' x‖ₑ dx`. -/
theorem fhpbb1w_local_fixed (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) {h : ℝ} (hh : |h| ≤ 1) :
    ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t - f (t - h)‖ₑ ≤
      ‖h‖ₑ * (2 * ∫⁻ x, ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ) := by
  have hV := fhpbb1w_measurable_derivWeight f hf.continuous_deriv_one
  have hpt : ∀ t : ℝ, ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t - f (t - h)‖ₑ ≤
      ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1,
        2 * (ENNReal.ofReal (1 + |t - α * h|) * ‖deriv f (t - α * h)‖ₑ) := by
    intro t
    calc ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t - f (t - h)‖ₑ
        ≤ ENNReal.ofReal (1 + Real.sqrt |t|) *
            (‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1, ‖deriv f (t - α * h)‖ₑ) := by
          gcongr
          exact fhpbb1w_enorm_sub_le f hf t h
      _ = ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (1 + Real.sqrt |t|) * ‖deriv f (t - α * h)‖ₑ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
      _ ≤ ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1,
            2 * (ENNReal.ofReal (1 + |t - α * h|) * ‖deriv f (t - α * h)‖ₑ) := by
          gcongr ‖h‖ₑ * ?_
          refine setLIntegral_mono' measurableSet_Ioc fun α hα => ?_
          rw [← mul_assoc]
          gcongr
          calc ENNReal.ofReal (1 + Real.sqrt |t|)
              ≤ ENNReal.ofReal (2 * (1 + |t - α * h|)) :=
                ENNReal.ofReal_le_ofReal (fhpbb1w_weight_le hh hα.1.le hα.2)
            _ = 2 * ENNReal.ofReal (1 + |t - α * h|) := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]
  have hmeas : AEMeasurable (Function.uncurry fun (t α : ℝ) =>
      2 * (ENNReal.ofReal (1 + |t - α * h|) * ‖deriv f (t - α * h)‖ₑ))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hm : Measurable fun p : ℝ × ℝ =>
        2 * (ENNReal.ofReal (1 + |p.1 - p.2 * h|) * ‖deriv f (p.1 - p.2 * h)‖ₑ) :=
      (hV.comp (measurable_fst.sub (measurable_snd.mul_const h))).const_mul 2
    exact hm.aemeasurable
  calc ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t - f (t - h)‖ₑ
      ≤ ∫⁻ t, ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1,
          2 * (ENNReal.ofReal (1 + |t - α * h|) * ‖deriv f (t - α * h)‖ₑ) :=
        lintegral_mono hpt
    _ = ‖h‖ₑ * ∫⁻ t, ∫⁻ α in Ioc (0 : ℝ) 1,
          2 * (ENNReal.ofReal (1 + |t - α * h|) * ‖deriv f (t - α * h)‖ₑ) :=
        lintegral_const_mul' _ _ enorm_ne_top
    _ = ‖h‖ₑ * ∫⁻ α in Ioc (0 : ℝ) 1, ∫⁻ t,
          2 * (ENNReal.ofReal (1 + |t - α * h|) * ‖deriv f (t - α * h)‖ₑ) := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ‖h‖ₑ * ∫⁻ _α in Ioc (0 : ℝ) 1, ∫⁻ t,
          2 * (ENNReal.ofReal (1 + |t|) * ‖deriv f t‖ₑ) := by
        congr 1
        refine lintegral_congr fun α => ?_
        exact lintegral_sub_right_eq_self
          (fun x => 2 * (ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ)) (α * h)
    _ = ‖h‖ₑ * (2 * ∫⁻ x, ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one,
          lintegral_const_mul _ hV]

/-- **Local part**:`∫⁻ (1 + √|t|) ∫⁻ n(h) ‖f t - f (t-h)‖ₑ dh dt
≤ (∫⁻ n(h)|h|) · 2 ∫⁻ (1 + |x|) ‖f' x‖ₑ dx`. -/
theorem fhpbb1w_local (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
        ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ ≤
      fhpbb1w_nearMass * (2 * ∫⁻ x, ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ) := by
  have hfc : Continuous f := hf.continuous
  have hw := fhpbb1w_measurable_weight
  have hmeas : AEMeasurable (Function.uncurry fun t h : ℝ =>
      ENNReal.ofReal (1 + Real.sqrt |t|) *
        (ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ)) (volume.prod volume) := by
    have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 + Real.sqrt |p.1|) *
        (ENNReal.ofReal (fhpbb1w_near p.2) * ‖f p.1 - f (p.1 - p.2)‖ₑ) :=
      (hw.comp measurable_fst).mul ((fhpbb1w_measurable_near.comp measurable_snd).ennreal_ofReal.mul
        ((hfc.comp continuous_fst).sub (hfc.comp (continuous_fst.sub continuous_snd))
          ).measurable.enorm)
    exact hm.aemeasurable
  have hK : Measurable fun h : ℝ => ENNReal.ofReal (fhpbb1w_near h) * ‖h‖ₑ :=
    fhpbb1w_measurable_near.ennreal_ofReal.mul measurable_id.enorm
  calc ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
        ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ
      = ∫⁻ t, ∫⁻ h, ENNReal.ofReal (1 + Real.sqrt |t|) *
          (ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) :=
        lintegral_congr fun t => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ h, ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
          (ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) *
          ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t - f (t - h)‖ₑ := by
        refine lintegral_congr fun h => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun t => ?_
        ring
    _ ≤ ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖h‖ₑ *
          (2 * ∫⁻ x, ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ) := by
        refine lintegral_mono fun h => ?_
        beta_reduce
        by_cases hh : |h| ≤ 1
        · rw [mul_assoc]
          gcongr
          exact fhpbb1w_local_fixed f hf hh
        · simp [fhpbb1w_near, hh]
    _ = fhpbb1w_nearMass * (2 * ∫⁻ x, ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ) :=
        lintegral_mul_const _ hK

/-- **Far part**: Tonelli in `(t, s)` and (shiftweight). -/
theorem fhpbb1w_far_tonelli (f : ℝ → ℂ) (hfc : Continuous f) :
    ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
        ∫⁻ s, ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ ≤
      36 * fhpbb1w_farMass * ∫⁻ s, ENNReal.ofReal (1 + |s|) * ‖f s‖ₑ := by
  have hw := fhpbb1w_measurable_weight
  have hfar := fhpbb1w_measurable_far
  have hmeas : AEMeasurable (Function.uncurry fun t s : ℝ =>
      ENNReal.ofReal (1 + Real.sqrt |t|) *
        (ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ))
      (volume.prod volume) := by
    have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 + Real.sqrt |p.1|) *
        (ENNReal.ofReal |fhpbb1w_far (p.1 - p.2) - fhpbb1w_far p.1| * ‖f p.2‖ₑ) :=
      (hw.comp measurable_fst).mul
        ((continuous_abs.measurable.comp ((hfar.comp (measurable_fst.sub measurable_snd)).sub
          (hfar.comp measurable_fst))).ennreal_ofReal.mul
          (hfc.measurable.comp measurable_snd).enorm)
    exact hm.aemeasurable
  have hU : Measurable fun s : ℝ => ENNReal.ofReal (1 + |s|) * ‖f s‖ₑ :=
    ((continuous_const.add continuous_abs).measurable.ennreal_ofReal).mul hfc.measurable.enorm
  calc ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
        ∫⁻ s, ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ
      = ∫⁻ t, ∫⁻ s, ENNReal.ofReal (1 + Real.sqrt |t|) *
          (ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ) :=
        lintegral_congr fun t => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ s, ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
          (ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ) :=
        lintegral_lintegral_swap hmeas
    _ = ∫⁻ s, (∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
          ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t|) * ‖f s‖ₑ := by
        refine lintegral_congr fun s => ?_
        rw [← lintegral_mul_const' _ _ enorm_ne_top]
        refine lintegral_congr fun t => ?_
        ring
    _ ≤ ∫⁻ s, (ENNReal.ofReal (1 + |s|) * (36 * fhpbb1w_farMass)) * ‖f s‖ₑ := by
        exact lintegral_mono fun s => mul_le_mul' (fhpbb1w_shiftWeight s) le_rfl
    _ = 36 * fhpbb1w_farMass * ∫⁻ s, ENNReal.ofReal (1 + |s|) * ‖f s‖ₑ := by
        rw [← lintegral_const_mul _ hU]
        refine lintegral_congr fun s => ?_
        ring

/-- The weight comparison `∫⁻ (1 + √|t|) ‖f t‖ₑ ≤ 2 ∫⁻ (1 + |t|) ‖f t‖ₑ`. -/
theorem fhpbb1w_weight_compare (f : ℝ → ℂ) :
    ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t‖ₑ ≤
      2 * ∫⁻ t, ENNReal.ofReal (1 + |t|) * ‖f t‖ₑ := by
  rw [← lintegral_const_mul' 2 _ (by norm_num)]
  refine lintegral_mono fun t => ?_
  beta_reduce
  rw [← mul_assoc]
  gcongr
  calc ENNReal.ofReal (1 + Real.sqrt |t|) ≤ ENNReal.ofReal (2 * (1 + |t|)) :=
        ENNReal.ofReal_le_ofReal (by
          have := fhpbb1w_sqrt_le_one_add (abs_nonneg t)
          have := abs_nonneg t
          linarith)
    _ = 2 * ENNReal.ofReal (1 + |t|) := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]

/-- **The weighted one-dimensional estimate**, for an arbitrary real normalization
`κ`: there is `C ≥ 0` such that for every integrable `C¹` function `f : ℝ → ℂ` with `∫ f = 0`,
`∫⁻ (1 + √|t|) ‖κ ∫ |h|^{-3/2} (f t - f (t-h)) dh‖ₑ dt ≤ C ∫⁻ (1 + |t|) (‖f t‖ₑ + ‖f' t‖ₑ) dt`.
The constant is `‖κ‖ (2 ∫⁻ n(h)|h| + 38 ‖a‖₁)`. -/
theorem fhpbb1w_oneDimWeighted (κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 1 f → Integrable f → ∫ t, f t = 0 →
      ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
          ‖(κ : ℂ) * ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ ≤
        ENNReal.ofReal C * ∫⁻ t, ENNReal.ofReal (1 + |t|) * (‖f t‖ₑ + ‖deriv f t‖ₑ) := by
  have hM : ‖(κ : ℂ)‖ₑ * (2 * fhpbb1w_nearMass + 38 * fhpbb1w_farMass) ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by norm_num) fhpbb1w_nearMass_lt_top.ne,
        ENNReal.mul_ne_top (by norm_num) fhpbb1w_farMass_lt_top.ne⟩)
  refine ⟨(‖(κ : ℂ)‖ₑ * (2 * fhpbb1w_nearMass + 38 * fhpbb1w_farMass)).toReal,
    ENNReal.toReal_nonneg, fun f hf hfi hf0 => ?_⟩
  rw [ENNReal.ofReal_toReal hM]
  have hfc : Continuous f := hf.continuous
  have hw := fhpbb1w_measurable_weight
  have hA : Measurable fun t : ℝ => ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ := by
    have hm : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (fhpbb1w_near p.2) * ‖f p.1 - f (p.1 - p.2)‖ₑ :=
      (fhpbb1w_measurable_near.comp measurable_snd).ennreal_ofReal.mul
        ((hfc.comp continuous_fst).sub (hfc.comp (continuous_fst.sub continuous_snd))
          ).measurable.enorm
    exact hm.lintegral_prod_right'
  have hF : Measurable fun t : ℝ => ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t‖ₑ :=
    hw.mul hfc.measurable.enorm
  have hAw : Measurable fun t : ℝ => ENNReal.ofReal (1 + Real.sqrt |t|) *
      ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ := hw.mul hA
  have hAF : Measurable fun t : ℝ => ENNReal.ofReal (1 + Real.sqrt |t|) *
      (∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
        fhpbb1w_farMass * (ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t‖ₑ) :=
    hAw.add (hF.const_mul _)
  calc ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
        ‖(κ : ℂ) * ∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ
      ≤ ∫⁻ t, ‖(κ : ℂ)‖ₑ *
          ((ENNReal.ofReal (1 + Real.sqrt |t|) *
              (∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
            fhpbb1w_farMass * (ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t‖ₑ)) +
          ENNReal.ofReal (1 + Real.sqrt |t|) *
            ∫⁻ s, ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ) := by
        refine lintegral_mono fun t => ?_
        beta_reduce
        rw [enorm_mul]
        calc ENNReal.ofReal (1 + Real.sqrt |t|) * (‖(κ : ℂ)‖ₑ *
              ‖∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ)
            = ‖(κ : ℂ)‖ₑ * (ENNReal.ofReal (1 + Real.sqrt |t|) *
              ‖∫ h : ℝ, ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (f t - f (t - h))‖ₑ) := by ring
          _ ≤ ‖(κ : ℂ)‖ₑ * (ENNReal.ofReal (1 + Real.sqrt |t|) *
              ((∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
                fhpbb1w_farMass * ‖f t‖ₑ +
                ∫⁻ s, ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ)) := by
              gcongr
              exact fhpbb1w_pointwise f hfi hf0 t
          _ = _ := by ring
    _ = ‖(κ : ℂ)‖ₑ *
          ((∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
              ∫⁻ h, ENNReal.ofReal (fhpbb1w_near h) * ‖f t - f (t - h)‖ₑ) +
            fhpbb1w_farMass * (∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) * ‖f t‖ₑ) +
            ∫⁻ t, ENNReal.ofReal (1 + Real.sqrt |t|) *
              ∫⁻ s, ENNReal.ofReal |fhpbb1w_far (t - s) - fhpbb1w_far t| * ‖f s‖ₑ) := by
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_add_left hAF,
          lintegral_add_left hAw, lintegral_const_mul _ hF]
    _ ≤ ‖(κ : ℂ)‖ₑ *
          (fhpbb1w_nearMass * (2 * ∫⁻ x, ENNReal.ofReal (1 + |x|) * ‖deriv f x‖ₑ) +
            fhpbb1w_farMass * (2 * ∫⁻ t, ENNReal.ofReal (1 + |t|) * ‖f t‖ₑ) +
            36 * fhpbb1w_farMass * ∫⁻ s, ENNReal.ofReal (1 + |s|) * ‖f s‖ₑ) := by
        gcongr ‖(κ : ℂ)‖ₑ * (?_ + fhpbb1w_farMass * ?_ + ?_)
        · exact fhpbb1w_local f hf
        · exact fhpbb1w_weight_compare f
        · exact fhpbb1w_far_tonelli f hfc
    _ ≤ ‖(κ : ℂ)‖ₑ *
          (fhpbb1w_nearMass *
              (2 * ∫⁻ t, ENNReal.ofReal (1 + |t|) * (‖f t‖ₑ + ‖deriv f t‖ₑ)) +
            fhpbb1w_farMass *
              (2 * ∫⁻ t, ENNReal.ofReal (1 + |t|) * (‖f t‖ₑ + ‖deriv f t‖ₑ)) +
            36 * fhpbb1w_farMass *
              ∫⁻ t, ENNReal.ofReal (1 + |t|) * (‖f t‖ₑ + ‖deriv f t‖ₑ)) := by
        gcongr ‖(κ : ℂ)‖ₑ * (fhpbb1w_nearMass * (2 * ?_) + fhpbb1w_farMass * (2 * ?_) +
          36 * fhpbb1w_farMass * ?_)
        · exact lintegral_mono fun t => mul_le_mul' le_rfl le_add_self
        · exact lintegral_mono fun t => mul_le_mul' le_rfl le_self_add
        · exact lintegral_mono fun t => mul_le_mul' le_rfl le_self_add
    _ = ‖(κ : ℂ)‖ₑ * (2 * fhpbb1w_nearMass + 38 * fhpbb1w_farMass) *
          ∫⁻ t, ENNReal.ofReal (1 + |t|) * (‖f t‖ₑ + ‖deriv f t‖ₑ) := by ring

end ParabolicRectifiability.FractionalKernel
