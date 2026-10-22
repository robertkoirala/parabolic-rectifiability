import ParabolicRectifiability.Analysis.HalfTimeDerivative.LocalConstantTail
import ParabolicRectifiability.Metric.Measure
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Oscillation of the separated half-time tail

The source and cutoff live on ordinary Fourier coordinates. The cylinders and
Lipschitz bound use the actual parabolic metric. Only differences of tails have
a bound independent of the source support. The separated tail is connected to the
local-constant tail theorem of `LocalConstantTail`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped Topology ENNReal

namespace ParabolicRectifiability.HalfTimeDerivative
open FractionalKernel

@[simp] private theorem origin_spatial (m : ℕ) : (point (0 : Spatial m) 0).1 = 0 := rfl
@[simp] private theorem origin_time (m : ℕ) : (point (0 : Spatial m) 0).2.val = 0 := rfl
@[simp] private theorem point_rebuild {m : ℕ} (z : Space m) : point z.1 z.2.val = z := by
  rcases z with ⟨u,⟨t⟩⟩
  rfl

/-- The exact maximum/square-root Lipschitz inequality in ordinary coordinates. -/
def ParabolicLipschitz {m : ℕ} (F : FourierSpace m → ℝ) (L : ℝ) : Prop :=
  ∀ (u v : Spatial m) (t s : ℝ),
    |F (WithLp.toLp 2 (u,t)) - F (WithLp.toLp 2 (v,s))| ≤
      L * max ‖u-v‖ (Real.sqrt |t-s|)

/-- Elementary cutoff hypotheses; a smooth cutoff will supply these properties.
No derivative, BMO estimate or tail conclusion is included as a field. -/
structure TailCutoff {m : ℕ} (χ : FourierSpace m → ℝ) (R Cχ : ℝ) : Prop where
  measurable : Measurable χ
  nonneg : ∀ x, 0 ≤ χ x
  le_one : ∀ x, χ x ≤ 1
  inner : ∀ x ∈ analyticCylinder (point (0 : Spatial m) 0) (2*R), χ x = 1
  outer : ∀ x ∉ analyticCylinder (point (0 : Spatial m) 0) (4*R), χ x = 0
  spatial : ∀ (u v : Spatial m) (s : ℝ),
    |χ (WithLp.toLp 2 (u,s)) - χ (WithLp.toLp 2 (v,s))| ≤ Cχ/R * ‖u-v‖

/-- The genuine finite-volume mean; its denominator is proved positive below. -/
def tailMean {m : ℕ} (F : FourierSpace m → ℝ) (R : ℝ) : ℝ :=
  (volume (analyticCylinder (point (0 : Spatial m) 0) R)).toReal⁻¹ *
    ∫ x in analyticCylinder (point (0 : Spatial m) 0) R, F x

def oscillationTailSet (R : ℝ) : Set ℝ := {s | 4*R^2 ≤ |s|}

/-- The actual signed tail, with the normalization `kappa`. -/
def oscillationTail {m : ℕ} (F χ : FourierSpace m → ℝ) (R : ℝ)
    (u : Spatial m) (t : ℝ) : ℝ :=
  -kappa * ∫ s in oscillationTailSet R,
    (1-χ (WithLp.toLp 2 (u,s))) * (F (WithLp.toLp 2 (u,s))-tailMean F R) *
      |t-s|^(-3/2 : ℝ)

theorem ParabolicLipschitz.continuous {m : ℕ} {F : FourierSpace m → ℝ} {L : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) : Continuous F := by
  let G : Space m → ℝ := fun z => F (WithLp.toLp 2 (z.1,z.2.val))
  have hg : LipschitzWith ⟨L,hL⟩ G := by
    apply LipschitzWith.of_dist_le_mul
    rintro ⟨u,⟨t⟩⟩ ⟨v,⟨s⟩⟩
    change |F (WithLp.toLp 2 (u,t))-F (WithLp.toLp 2 (v,s))| ≤ L*dist (point u t) (point v s)
    rw [dist_point]
    exact hF u v t s
  exact hg.continuous.comp (fourierToParabolic m).continuous

theorem tailBase_volume {m : ℕ} {R : ℝ} (hR : 0 < R) :
    0 < volume (analyticCylinder (point (0 : Spatial m) 0) R) ∧
      volume (analyticCylinder (point (0 : Spatial m) 0) R) < ⊤ := by
  rw [volume_analyticCylinder _ _ hR]
  constructor
  · have ho := omega_pos m
    have hr := ENNReal.ofReal_pos.mpr hR
    positivity
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (omega_lt_top m))
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

theorem parabolicLip_base_bound {m : ℕ} {F : FourierSpace m → ℝ} {L R : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    {x : FourierSpace m} (hx : x ∈ analyticCylinder (point (0 : Spatial m) 0) R) :
    |F x - F (WithLp.toLp 2 ((0 : Spatial m),0))| ≤ L*R := by
  have hu : ‖(WithLp.ofLp x).1‖ < R := by simpa [analyticCylinder, dist_eq_norm] using hx.1
  have ht : |(WithLp.ofLp x).2| < R^2 := by
    have hh := hx.2
    simpa [analyticCylinder, abs_lt] using hh
  exact (hF _ 0 _ 0).trans (mul_le_mul_of_nonneg_left
    (max_le (by simpa using hu.le) (by simpa using (Real.sqrt_le_left hR.le).2 ht.le)) hL)

/-- The average is derived from the actual source; it is not replaced by its central value. -/
theorem abs_tailMean_sub_origin_le {m : ℕ} {F : FourierSpace m → ℝ} {L R : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) :
    |tailMean F R - F (WithLp.toLp 2 ((0 : Spatial m),0))| ≤ L*R := by
  let E := analyticCylinder (point (0 : Spatial m) 0) R
  let a := (volume E).toReal
  have hp : 0 < a := ENNReal.toReal_pos (tailBase_volume hR).1.ne' (tailBase_volume hR).2.ne
  let : IsFiniteMeasure (volume.restrict E) := ⟨by simpa [E] using (tailBase_volume hR).2⟩
  have hi : IntegrableOn F E volume := ((hF.continuous hL).integrable_of_hasCompactSupport hc).integrableOn
  let f0 := F (WithLp.toLp 2 ((0 : Spatial m),0))
  have he : tailMean F R - f0 = a⁻¹ * ∫ x in E, (F x-f0) := by
    rw [integral_sub hi (integrable_const f0), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change a⁻¹*(∫ x in E, F x)-f0 = a⁻¹*((∫ x in E, F x)-a*f0)
    field_simp [hp.ne']
  have hb : |∫ x in E, (F x-f0)| ≤ (L*R)*a := by
    have hn : ‖∫ x in E, (F x-f0)‖ ≤ (L*R)*(volume.restrict E).real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [ae_restrict_mem (measurableSet_analyticCylinder _ _)] with x hx
      simpa only [Real.norm_eq_abs] using parabolicLip_base_bound hF hL hR hx
    simpa [a, Measure.real] using hn
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ a⁻¹ * ((L*R)*a) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)
    _ = L*R := by field_simp

theorem measurableSet_oscillationTailSet (R : ℝ) : MeasurableSet (oscillationTailSet R) :=
  measurableSet_le measurable_const measurable_abs

/-- Separation supplies a uniform lower bound in terms of the original tail variable. -/
theorem tail_distance_lower {R t s : ℝ} (ht : |t| ≤ R^2) (hs : 4*R^2 ≤ |s|) :
    |s|/4 ≤ |t-s| := by
  have h' : |s| ≤ |t-s|+|t| := by
    have hh := abs_sub (t-s) t
    simpa [sub_sub_cancel_left, abs_neg, abs_sub_comm] using hh
  nlinarith [abs_nonneg (t-s)]

private theorem four_rpow_three_halves : (4 : ℝ)^(3/2 : ℝ) = 8 := by
  rw [show (3/2 : ℝ) = 1+1/2 by norm_num, Real.rpow_add (by norm_num)]
  norm_num [← Real.sqrt_eq_rpow]

private theorem four_rpow_five_halves : (4 : ℝ)^(5/2 : ℝ) = 32 := by
  rw [show (5/2 : ℝ) = 2+1/2 by norm_num, Real.rpow_add (by norm_num)]
  norm_num [← Real.sqrt_eq_rpow]

theorem tail_kernel_le {R t s : ℝ} (hR : 0 < R) (ht : |t| ≤ R^2)
    (hs : 4*R^2 ≤ |s|) : |t-s|^(-3/2 : ℝ) ≤ 8*|s|^(-3/2 : ℝ) := by
  have hp : 0 < |s| := (by positivity : 0 < 4*R^2).trans_le hs
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < |s|/4)
    (tail_distance_lower ht hs) (by norm_num : (-3/2 : ℝ) ≤ 0)
  rw [Real.div_rpow (abs_nonneg s) (by norm_num),
    show (-3/2 : ℝ) = -(3/2 : ℝ) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), four_rpow_three_halves] at h
  rw [show -(3/2 : ℝ) = (-3/2 : ℝ) by ring] at h
  simpa [div_eq_mul_inv, mul_comm] using h

/-- The extra power comes from a genuine mean-value estimate away from zero. -/
theorem tail_kernel_difference_le {R t t₀ s : ℝ} (hR : 0 < R)
    (ht : |t| ≤ R^2) (ht₀ : |t₀| ≤ R^2) (hs : 4*R^2 ≤ |s|) :
    abs (|t-s|^(-3/2 : ℝ) - |t₀-s|^(-3/2 : ℝ)) ≤
      48*|t-t₀| *|s|^(-5/2 : ℝ) := by
  have hp : 0 < |s| := (by positivity : 0 < 4*R^2).trans_le hs
  let a := |s|/4
  have ha : 0 < a := by dsimp [a]; positivity
  have hd (x : ℝ) (hx : x ∈ Ici a) :
      HasDerivWithinAt (fun x : ℝ => x^(-3/2 : ℝ))
        ((-3/2 : ℝ)*x^(-5/2 : ℝ)) (Ici a) x := by
    convert (Real.hasDerivAt_rpow_const (Or.inl (ha.trans_le hx).ne')
      (p := (-3/2 : ℝ))).hasDerivWithinAt using 1; norm_num
  have hb (x : ℝ) (hx : x ∈ Ici a) :
      ‖(-3/2 : ℝ)*x^(-5/2 : ℝ)‖ ≤ 48*|s|^(-5/2 : ℝ) := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (ha.le.trans hx) _)]
    have hh := Real.rpow_le_rpow_of_nonpos ha hx (by norm_num : (-5/2 : ℝ) ≤ 0)
    dsimp [a] at hh
    rw [Real.div_rpow (abs_nonneg s) (by norm_num),
      show (-5/2 : ℝ) = -(5/2 : ℝ) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), four_rpow_five_halves] at hh
    rw [show -(5/2 : ℝ) = (-5/2 : ℝ) by ring] at hh
    norm_num at *
    nlinarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici a)
    (tail_distance_lower ht₀ hs) (tail_distance_lower ht hs)
  simp only [Real.norm_eq_abs] at h
  calc
    _ ≤ (48*|s|^(-5/2 : ℝ)) * abs (|t-s|-|t₀-s|) := h
    _ ≤ (48*|s|^(-5/2 : ℝ))*|t-t₀| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (t-s) (t₀-s)
    _ = _ := by ring

/-- A quantitative amplitude estimate from the genuine mean. -/
theorem tail_amplitude_le {m : ℕ} {F : FourierSpace m → ℝ} {L R s : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) {u : Spatial m} (hu : ‖u‖ ≤ R)
    (hs : 4*R^2 ≤ |s|) :
    |F (WithLp.toLp 2 (u,s))-tailMean F R| ≤ 2*L*Real.sqrt |s| := by
  have hsqrt : 2*R ≤ Real.sqrt |s| := by
    apply (Real.le_sqrt (by positivity) (abs_nonneg s)).2
    nlinarith
  have h₁ := hF u 0 s 0
  simp only [sub_zero] at h₁
  have h₂ := abs_tailMean_sub_origin_le hF hL hR hc
  rw [abs_sub_comm] at h₂
  have hmax : max ‖u‖ (Real.sqrt |s|) = Real.sqrt |s| := max_eq_right (hu.trans (by linarith))
  rw [hmax] at h₁
  have ht := abs_add_le (F (WithLp.toLp 2 (u,s))-F (WithLp.toLp 2 ((0 : Spatial m),0)))
    (F (WithLp.toLp 2 ((0 : Spatial m),0))-tailMean F R)
  rw [sub_add_sub_cancel] at ht
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hL]

/-- The bounded annulus has amplitude at most six times L R. -/
theorem tail_amplitude_band_le {m : ℕ} {F : FourierSpace m → ℝ} {L R s : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) {u : Spatial m} (hu : ‖u‖ ≤ R)
    (hs : |s| ≤ 16*R^2) :
    |F (WithLp.toLp 2 (u,s))-tailMean F R| ≤ 6*L*R := by
  have hsqrt : Real.sqrt |s| ≤ 4*R := (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  have h₁ := hF u 0 s 0
  simp only [sub_zero] at h₁
  have h₂ := abs_tailMean_sub_origin_le hF hL hR hc
  rw [abs_sub_comm] at h₂
  have hmax : max ‖u‖ (Real.sqrt |s|) ≤ 4*R := max_le (by linarith) hsqrt
  have h₃ := h₁.trans (mul_le_mul_of_nonneg_left hmax hL)
  have ht := abs_add_le (F (WithLp.toLp 2 (u,s))-F (WithLp.toLp 2 ((0 : Spatial m),0)))
    (F (WithLp.toLp 2 ((0 : Spatial m),0))-tailMean F R)
  rw [sub_add_sub_cancel] at ht
  nlinarith [mul_nonneg hL hR.le]

theorem TailCutoff.one_sub_abs_le {m : ℕ} {χ : FourierSpace m → ℝ} {R Cχ : ℝ}
    (hχ : TailCutoff χ R Cχ) (x : FourierSpace m) : |1-χ x| ≤ 1 := by
  rw [abs_of_nonneg (sub_nonneg.mpr (hχ.le_one x))]
  linarith [hχ.nonneg x]

/-- The spatial cutoff error vanishes on both tails beyond the outer time slab. -/
theorem TailCutoff.outside_time {m : ℕ} {χ : FourierSpace m → ℝ} {R Cχ s : ℝ}
    (hχ : TailCutoff χ R Cχ) (hs : 16*R^2 ≤ |s|) (u : Spatial m) :
    χ (WithLp.toLp 2 (u,s)) = 0 := by
  apply hχ.outer
  intro hx
  have hh : |s| < (4*R)^2 := by
    simpa [analyticCylinder, abs_lt] using hx.2
  nlinarith

/-- The numerator difference has a uniform bound because the cutoff error is localized. -/
theorem tail_numerator_spatial_le {m : ℕ} {F χ : FourierSpace m → ℝ} {L R Cχ : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) (hχ : TailCutoff χ R Cχ) (hC : 0 ≤ Cχ)
    {u v : Spatial m} (_hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) (s : ℝ) :
    |(1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-tailMean F R) -
      (1-χ (WithLp.toLp 2 (v,s)))*(F (WithLp.toLp 2 (v,s))-tailMean F R)| ≤
      (1+6*Cχ)*L*‖u-v‖ := by
  have hdiff : |F (WithLp.toLp 2 (u,s))-F (WithLp.toLp 2 (v,s))| ≤ L*‖u-v‖ := by
    simpa only [sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)] using hF u v s s
  by_cases hs : 16*R^2 ≤ |s|
  · rw [hχ.outside_time hs u, hχ.outside_time hs v]
    simp only [sub_zero, one_mul, sub_sub_sub_cancel_right]
    exact hdiff.trans (by nlinarith [mul_nonneg hL (norm_nonneg (u-v)), mul_nonneg hC (mul_nonneg hL (norm_nonneg (u-v)))])
  have hamp := tail_amplitude_band_le hF hL hR hc hv (le_of_not_ge hs)
  have hcut := hχ.spatial u v s
  have hid : (1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-tailMean F R) -
      (1-χ (WithLp.toLp 2 (v,s)))*(F (WithLp.toLp 2 (v,s))-tailMean F R) =
      (1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-F (WithLp.toLp 2 (v,s))) +
      (χ (WithLp.toLp 2 (v,s))-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (v,s))-tailMean F R) := by ring
  rw [hid]
  calc
    _ ≤ |1-χ (WithLp.toLp 2 (u,s))| * |F (WithLp.toLp 2 (u,s))-F (WithLp.toLp 2 (v,s))| +
      |χ (WithLp.toLp 2 (v,s))-χ (WithLp.toLp 2 (u,s))| * |F (WithLp.toLp 2 (v,s))-tailMean F R| := by
      simpa only [abs_mul] using abs_add_le
        ((1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-F (WithLp.toLp 2 (v,s))))
        ((χ (WithLp.toLp 2 (v,s))-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (v,s))-tailMean F R))
    _ ≤ 1*(L*‖u-v‖) + (Cχ/R*‖u-v‖)*(6*L*R) := by
      gcongr
      · exact hχ.one_sub_abs_le _
      · simpa only [abs_sub_comm] using hcut
    _ = (1+6*Cχ)*L*‖u-v‖ := by field_simp

/-- Both exact dominating integrals have the required parabolic scaling. -/
theorem integral_power_square_radius {R : ℝ} (hR : 0 < R) :
    (∫ s, separatedPower (R^2) (-3/2) s) = 4/R ∧
    (∫ s, separatedPower (R^2) (-2) s) = 2/(R^2) := by
  constructor
  · rw [integral_separatedPower_three_halves (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]
  · rw [integral_separatedPower (by positivity) (by norm_num : (-2 : ℝ) < -1)]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- Integrating a nonnegative separated-power majorant retains both real tails. -/
theorem abs_setIntegral_le_power {f : ℝ → ℝ} {E : Set ℝ} (hE : MeasurableSet E)
    {δ a C : ℝ} (hδ : 0 < δ) (ha : a < -1) (hC : 0 ≤ C)
    (hb : ∀ s ∈ E, |f s| ≤ C*separatedPower δ a s) :
    |∫ s in E, f s| ≤ C*(∫ s, separatedPower δ a s) := by
  have hi := (integrable_separatedPower hδ ha).const_mul C
  calc
    _ ≤ ∫ s in E, C*separatedPower δ a s := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hi.integrableOn
      filter_upwards [ae_restrict_mem hE] with s hs
      simpa only [Real.norm_eq_abs] using hb s hs
    _ ≤ ∫ s, C*separatedPower δ a s :=
      setIntegral_le_integral hi (Eventually.of_forall fun s => mul_nonneg hC (separatedPower_nonneg _ _ _))
    _ = _ := integral_const_mul _ _

/-- Compact support supplies a source-dependent bound only for convergence. -/
theorem integrable_oscillationTail {m : ℕ} {F χ : FourierSpace m → ℝ} {L R Cχ : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) (hχ : TailCutoff χ R Cχ)
    (u : Spatial m) {t : ℝ} (ht : |t| ≤ R^2) :
    IntegrableOn (fun s => (1-χ (WithLp.toLp 2 (u,s))) *
      (F (WithLp.toLp 2 (u,s))-tailMean F R) * |t-s|^(-3/2 : ℝ))
      (oscillationTailSet R) volume := by
  obtain ⟨B,hB⟩ := (hF.continuous hL).bounded_above_of_compact_support hc
  have hB0 : 0 ≤ B := (norm_nonneg (F (WithLp.toLp 2 (u,0)))).trans (hB _)
  have hm : Measurable (fun s : ℝ => WithLp.toLp 2 (u,s)) :=
    (fourierCoordinatesMeasurableEquiv m).symm.measurable.comp (measurable_const.prodMk measurable_id)
  have hi := (integrable_separatedPower (by positivity : 0 < R^2)
    (by norm_num : (-3/2 : ℝ) < -1)).const_mul (8*(B+|tailMean F R|))
  apply hi.integrableOn.mono'
    ((((measurable_const.sub (hχ.measurable.comp hm)).mul
      (((hF.continuous hL).measurable.comp hm).sub measurable_const)).mul
      (((measurable_const.sub measurable_id).abs).pow_const _)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_oscillationTailSet R)] with s hs
  have hs' : 4*R^2 ≤ |s| := hs
  have hpow := tail_kernel_le hR ht hs'
  have hsize : |F (WithLp.toLp 2 (u,s))-tailMean F R| ≤ B+|tailMean F R| :=
    (abs_sub _ _).trans (add_le_add (by simpa only [Real.norm_eq_abs] using hB (WithLp.toLp 2 (u,s))) le_rfl)
  rw [Real.norm_eq_abs]
  change |(1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-tailMean F R)*|t-s|^(-3/2 : ℝ)| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    separatedPower, ite_eq_left (by nlinarith [sq_nonneg R] : R^2 ≤ |s|)]
  calc
    _ ≤ 1*(B+|tailMean F R|)*(8*|s|^(-3/2 : ℝ)) := by
      gcongr
      exact hχ.one_sub_abs_le _
    _ = _ := by ring

/-- The time oscillation uses an integrable -2 majorant, not a bound on the tail itself. -/
theorem oscillationTail_time_le {m : ℕ} {F χ : FourierSpace m → ℝ} {L R Cχ : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) (hχ : TailCutoff χ R Cχ)
    {u : Spatial m} (hu : ‖u‖ ≤ R) {t t₀ : ℝ}
    (ht : |t| ≤ R^2) (ht₀ : |t₀| ≤ R^2) :
    |oscillationTail F χ R u t - oscillationTail F χ R u t₀| ≤ 384*kappa*L := by
  have hi := integrable_oscillationTail hF hL hR hc hχ u ht
  have hi₀ := integrable_oscillationTail hF hL hR hc hχ u ht₀
  rw [oscillationTail, oscillationTail, ← mul_sub, ← integral_sub hi hi₀,
    abs_mul, abs_neg, abs_of_pos kappa_pos]
  have hb : |∫ s in oscillationTailSet R,
      (1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-tailMean F R)*|t-s|^(-3/2 : ℝ) -
      (1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-tailMean F R)*|t₀-s|^(-3/2 : ℝ)| ≤
      (192*L*R^2)*(∫ s, separatedPower (R^2) (-2) s) := by
    apply abs_setIntegral_le_power (measurableSet_oscillationTailSet R)
      (by positivity) (by norm_num) (by positivity)
    intro s hs
    have hs' : 4*R^2 ≤ |s| := hs
    have hp : 0 < |s| := (by positivity : 0 < 4*R^2).trans_le hs'
    have hamp := tail_amplitude_le hF hL hR hc hu hs'
    have hk := tail_kernel_difference_le hR ht ht₀ hs'
    have htd : |t-t₀| ≤ 2*R^2 := (abs_sub _ _).trans (by linarith)
    have hpow : Real.sqrt |s| * |s|^(-5/2 : ℝ) = |s|^(-2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
      norm_num
    rw [← mul_sub, abs_mul, abs_mul, separatedPower,
      ite_eq_left (by nlinarith [sq_nonneg R] : R^2 ≤ |s|)]
    calc
      _ ≤ 1*(2*L*Real.sqrt |s|)*(48*|t-t₀| *|s|^(-5/2 : ℝ)) := by
        gcongr
        exact hχ.one_sub_abs_le _
      _ = (96*L*|t-t₀|)*(Real.sqrt |s| *|s|^(-5/2 : ℝ)) := by ring
      _ = (96*L*|t-t₀|)*|s|^(-2 : ℝ) := by rw [hpow]
      _ ≤ (192*L*R^2)*|s|^(-2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left htd hL]
  calc
    _ ≤ kappa*((192*L*R^2)*(∫ s, separatedPower (R^2) (-2) s)) :=
      mul_le_mul_of_nonneg_left hb kappa_pos.le
    _ = 384*kappa*L := by rw [(integral_power_square_radius hR).2]; field_simp; ring

/-- The cutoff's spatial difference only contributes on a bounded time annulus. -/
theorem oscillationTail_spatial_le {m : ℕ} {F χ : FourierSpace m → ℝ} {L R Cχ : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) (hχ : TailCutoff χ R Cχ) (hC : 0 ≤ Cχ)
    {u v : Spatial m} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) {t : ℝ} (ht : |t| ≤ R^2) :
    |oscillationTail F χ R u t - oscillationTail F χ R v t| ≤
      64*kappa*(1+6*Cχ)*L := by
  have hi := integrable_oscillationTail hF hL hR hc hχ u ht
  have hi₀ := integrable_oscillationTail hF hL hR hc hχ v ht
  rw [oscillationTail, oscillationTail, ← mul_sub, ← integral_sub hi hi₀,
    abs_mul, abs_neg, abs_of_pos kappa_pos]
  have hb : |∫ s in oscillationTailSet R,
      (1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-tailMean F R)*|t-s|^(-3/2 : ℝ) -
      (1-χ (WithLp.toLp 2 (v,s)))*(F (WithLp.toLp 2 (v,s))-tailMean F R)*|t-s|^(-3/2 : ℝ)| ≤
      (16*(1+6*Cχ)*L*R)*(∫ s, separatedPower (R^2) (-3/2) s) := by
    apply abs_setIntegral_le_power (measurableSet_oscillationTailSet R)
      (by positivity) (by norm_num) (by positivity)
    intro s hs
    have hs' : 4*R^2 ≤ |s| := hs
    have hn := tail_numerator_spatial_le hF hL hR hc hχ hC hu hv s
    have huv : ‖u-v‖ ≤ 2*R := (norm_sub_le _ _).trans (by linarith)
    have hk := tail_kernel_le hR ht hs'
    rw [← sub_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      separatedPower, ite_eq_left (by nlinarith [sq_nonneg R] : R^2 ≤ |s|)]
    calc
      _ ≤ ((1+6*Cχ)*L*‖u-v‖)*(8*|s|^(-3/2 : ℝ)) := mul_le_mul hn hk
        (Real.rpow_nonneg (abs_nonneg _) _) (by positivity)
      _ ≤ ((1+6*Cχ)*L*(2*R))*(8*|s|^(-3/2 : ℝ)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ kappa*((16*(1+6*Cχ)*L*R)*(∫ s, separatedPower (R^2) (-3/2) s)) :=
      mul_le_mul_of_nonneg_left hb kappa_pos.le
    _ = 64*kappa*(1+6*Cχ)*L := by rw [(integral_power_square_radius hR).1]; field_simp; ring

/-- One fixed finite constant, independent of the source, radius and support. -/
def tailOscillationConstant (Cχ : ℝ) : ℝ := 512*kappa*(1+Cχ)

theorem tailOscillationConstant_pos {Cχ : ℝ} (hC : 0 ≤ Cχ) :
    0 < tailOscillationConstant Cχ := by
  have hk := kappa_pos
  unfold tailOscillationConstant
  positivity

/-- Scalar separated-tail oscillation in every spatial rank, including zero. -/
theorem oscillationTail_le {m : ℕ} {F χ : FourierSpace m → ℝ} {L R Cχ : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) (hχ : TailCutoff χ R Cχ) (hC : 0 ≤ Cχ)
    {u v : Spatial m} (hu : ‖u‖ < R) (hv : ‖v‖ < R) {t t₀ : ℝ}
    (ht : |t| < R^2) (ht₀ : |t₀| < R^2) :
    |oscillationTail F χ R u t - oscillationTail F χ R v t₀| ≤ tailOscillationConstant Cχ*L := by
  have h₁ := oscillationTail_time_le hF hL hR hc hχ hu.le ht.le ht₀.le
  have h₂ := oscillationTail_spatial_le hF hL hR hc hχ hC hu.le hv.le ht₀.le
  have h₃ := abs_add_le (oscillationTail F χ R u t - oscillationTail F χ R u t₀)
    (oscillationTail F χ R u t₀ - oscillationTail F χ R v t₀)
  rw [sub_add_sub_cancel] at h₃
  unfold tailOscillationConstant
  nlinarith [mul_nonneg kappa_pos.le hL, mul_nonneg (mul_nonneg kappa_pos.le hC) hL]

/-- The actual source whose locally constant derivative is the separated tail. -/
def tailRemainder {m : ℕ} (F χ : FourierSpace m → ℝ) (R : ℝ) (x : FourierSpace m) : ℝ :=
  F x - χ x*(F x-tailMean F R)

theorem TailCutoff.compact_support {m : ℕ} {χ : FourierSpace m → ℝ} {R Cχ : ℝ}
    (hχ : TailCutoff χ R Cχ) (hR : 0 < R) : HasCompactSupport χ := by
  have hg : HasCompactSupport (fun z : Space m => χ ((fourierToParabolic m).symm z)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (point (0 : Spatial m) 0) (4*R))
    intro z hz
    by_contra hn
    apply hz
    apply hχ.outer
    rw [analyticCylinder_eq_preimage_ball _ _ (by positivity)]
    intro hx
    apply hn
    apply Metric.ball_subset_closedBall
    simpa using hx
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
    hg.comp_homeomorph (fourierToParabolic m)

/-- The cutoff remainder is an actual global L2 function, although its local constant need not be. -/
theorem memLp_tailRemainder {m : ℕ} {F χ : FourierSpace m → ℝ} {L R Cχ : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) (hχ : TailCutoff χ R Cχ) :
    MemLp (tailRemainder F χ R) 2 volume := by
  have hcp : HasCompactSupport (fun x => χ x*(F x-tailMean F R)) :=
    (hχ.compact_support hR).mul_right
  have hh : HasCompactSupport (tailRemainder F χ R) := hc.sub hcp
  obtain ⟨B,hB⟩ := (hF.continuous hL).bounded_above_of_compact_support hc
  have hB0 : 0 ≤ B := (norm_nonneg (F (WithLp.toLp 2 ((0 : Spatial m),0)))).trans (hB _)
  apply hh.memLp_of_bound
    (((hF.continuous hL).measurable.sub (hχ.measurable.mul
      ((hF.continuous hL).measurable.sub measurable_const))).aestronglyMeasurable)
    (2*B+|tailMean F R|)
  apply Eventually.of_forall
  intro x
  change ‖F x-χ x*(F x-tailMean F R)‖ ≤ _
  calc
    _ ≤ ‖F x‖ + ‖χ x*(F x-tailMean F R)‖ := norm_sub_le _ _
    _ ≤ B+1*(B+|tailMean F R|) := by
      rw [norm_mul]
      gcongr
      · exact hB x
      · rw [Real.norm_eq_abs, abs_of_nonneg (hχ.nonneg x)]; exact hχ.le_one x
      · exact (norm_sub_le _ _).trans (add_le_add (hB x) (by rw [Real.norm_eq_abs]))
    _ = _ := by ring

theorem localConstantTail_tailRemainder {m : ℕ} (F χ : FourierSpace m → ℝ) (R : ℝ)
    (u : Spatial m) (t : ℝ) :
    localConstantTail (tailRemainder F χ R) (tailMean F R) (Ioo (-(4*R^2)) (4*R^2)) u t =
      oscillationTail F χ R u t := by
  have he : (Ioo (-(4*R^2)) (4*R^2))ᶜ = oscillationTailSet R := by
    ext s
    change (¬ (-(4*R^2) < s ∧ s < 4*R^2)) ↔ 4*R^2 ≤ |s|
    rw [← abs_lt]
    exact not_lt
  unfold localConstantTail oscillationTail
  rw [he]
  calc
    _ = kappa * ∫ s in oscillationTailSet R,
        -((1-χ (WithLp.toLp 2 (u,s)))*(F (WithLp.toLp 2 (u,s))-tailMean F R)*|t-s|^(-3/2 : ℝ)) := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by dsimp [tailRemainder]; ring
    _ = _ := by rw [integral_neg]; ring

/-- A complete interval/cylinder bridge to the local-constant tail theorem. -/
theorem repHalf_oscillationTail {m : ℕ} {F χ : FourierSpace m → ℝ} {L R Cχ : ℝ}
    (hF : ParabolicLipschitz F L) (hL : 0 ≤ L) (hR : 0 < R)
    (hc : HasCompactSupport F) (hχ : TailCutoff χ R Cχ) :
    RepHalf (memLp_tailRemainder hF hL hR hc hχ)
      (fun x => oscillationTail F χ R (WithLp.ofLp x).1 (WithLp.ofLp x).2)
      (analyticCylinder (point (0 : Spatial m) 0) R) := by
  let H := tailRemainder F χ R
  let c := tailMean F R
  let I := Ioo (-(4*R^2)) (4*R^2)
  let J := Ioo (-(R^2)) (R^2)
  let V := Metric.ball (0 : Spatial m) R
  have hH : MemLp H 2 volume := memLp_tailRemainder hF hL hR hc hχ
  have hsep : ∀ t ∈ J, ∀ s ∉ I, R^2 ≤ |t-s| := by
    intro t ht s hs
    have ht' : |t| < R^2 := abs_lt.mpr ht
    have hs' : 4*R^2 ≤ |s| := le_of_not_gt (fun h => hs (abs_lt.mp h))
    have hb := tail_distance_lower ht'.le hs'
    nlinarith
  have hloc : ∀ᵐ x ∂volume.restrict ((fourierCoordinatesMeasurableEquiv m) ⁻¹' (V ×ˢ I)), H x = c := by
    filter_upwards [ae_restrict_mem ((fourierCoordinatesMeasurableEquiv m).measurable
      (isOpen_ball.measurableSet.prod measurableSet_Ioo))] with x hx
    have hh : χ x = 1 := by
      apply hχ.inner
      constructor
      · apply Metric.mem_ball.mpr
        have hu : dist (WithLp.ofLp x).1 0 < R := hx.1
        change dist (WithLp.ofLp x).1 0 < 2*R
        linarith
      · simpa [I, show (2*R)^2 = 4*R^2 by ring] using hx.2
    dsimp [H, c, tailRemainder]
    rw [hh]
    ring
  have hrep := repHalf_measurableLocalConstantTail hH isOpen_ball measurableSet_Ioo isOpen_Ioo
    Metric.isBounded_ball.isCompact_closure (Metric.isBounded_Ioo (-(R^2)) (R^2)).isCompact_closure
    (by positivity : 0 < R^2) hsep hloc
  have he : measurableLocalConstantTailFourier hH c I =ᵐ[volume]
      (fun x => oscillationTail F χ R (WithLp.ofLp x).1 (WithLp.ofLp x).2) := by
    apply (ae_fourierCoordinates_symm_iff _).mp
    rw [volume_coordinates_eq_prod]
    have hf := measurableLocalConstantTail_eq_ae_fibers hH c I
    filter_upwards [quasiMeasurePreserving_fst.ae hf] with p hp
    change measurableLocalConstantTail hH c I p.1 p.2 = _
    rw [hp p.2]
    exact localConstantTail_tailRemainder F χ R p.1 p.2
  have hr := (repHalf_congr hH hH (Eventually.of_forall fun _ => rfl) (ae_restrict_of_ae he)).mp hrep
  simpa [analyticCylinder, H, I, J, V] using hr

end ParabolicRectifiability.HalfTimeDerivative
