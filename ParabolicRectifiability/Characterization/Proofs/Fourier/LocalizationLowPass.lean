import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationAdapters
import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationGagliardo

/-! # Critical Sobolev localization: the low-pass part

Part of the proof of `ba1_critical_sobolev_localization_proof`. With the fixed
cutoff `η = b1loc_cutoff`, `G = F ∘ Ψ` and `x₀ = Ψ⁻¹ p₀`, the low-pass part is

`A(x) = (η *_t (G - F(p₀)))(x) = ∫ η(r) (G(x - r e_t) - F(p₀)) dr`   (`b1loc_lowPass`).

For `x ∈ B(x₀,7)` and `0 < s ≤ 1`:
* `|G(x - r e_t) - F(p₀)| ≤ 8 L (1 + |r|)` (parabolic Lipschitz; a time shift by `r` moves
  `Ψ x` by `√|r|`);
* `(1 + |r|)³ (|η(r)| + |η'(r)|) ≤ C_η` (Schwartz decay), hence by the mean value theorem
  `(1 + |r|)³ |η(r + s) - η(r)| ≤ 8 C_η s`;
* `|A(x)| ≤ 8 C_η I₂ L` and, after the substitution `r ↦ r + s`,
  `A(x + s e_t) - A(x) = ∫ (η(r + s) - η(r)) (G(x - r e_t) - F(p₀)) dr`, so
  `|A(x + s e_t) - A(x)| ≤ 64 C_η I₂ L s`, with `I₂ = ∫ (1 + |r|)^{-2} dr`.

Consequently `LGag(A) + ∫_{B(x₀,7)} |A|² ≤ 2 (64 C_η I₂)² V L²` and, by the cutoff product rule,
`b1loc_timeGagliardo (χ_{x₀} A) ≤ C L²` with `χ_{x₀} A ∈ L²` (`b1loc_lowPass_estimate`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform SchwartzMap

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-! ## Decay of the fixed cutoff -/

/-- `(1 + |r|)³ |η(r)| ≤ C` and `(1 + |r|)³ |η'(r)| ≤ C`. -/
theorem b1loc_cutoff_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
    (1 + |r|) ^ 3 * |b1loc_cutoff r| ≤ C ∧ (1 + |r|) ^ 3 * |deriv (⇑b1loc_cutoff) r| ≤ C := by
  have h0 : ∀ r : ℝ, (1 + |r|) ^ 3 * |b1loc_cutoff r| ≤ 2 ^ 3 *
      ((Finset.Iic ((3, 1) : ℕ × ℕ)).sup
        (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) b1loc_cutoff := by
    intro r
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((3, 1) : ℕ × ℕ))
      (k := 3) (n := 0) le_rfl (Nat.zero_le _) b1loc_cutoff r
    rw [norm_iteratedFDeriv_zero] at h
    simp only [Real.norm_eq_abs] at h
    exact h
  have h1 : ∀ r : ℝ, (1 + |r|) ^ 3 * |deriv (⇑b1loc_cutoff) r| ≤ 2 ^ 3 *
      ((Finset.Iic ((3, 1) : ℕ × ℕ)).sup
        (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)) b1loc_cutoff := by
    intro r
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((3, 1) : ℕ × ℕ))
      (k := 3) (n := 1) le_rfl le_rfl b1loc_cutoff r
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] at h
    simp only [Real.norm_eq_abs] at h
    exact h
  refine ⟨_, le_trans (by positivity) (h0 0), fun r => ⟨h0 r, h1 r⟩⟩

/-- Mean value theorem for the cutoff: `(1 + |r|)³ |η(r + s) - η(r)| ≤ 8 C s` for `0 ≤ s ≤ 1`. -/
theorem b1loc_cutoff_sub_le {C : ℝ}
    (hC : ∀ r : ℝ, (1 + |r|) ^ 3 * |deriv (⇑b1loc_cutoff) r| ≤ C) (r : ℝ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 + |r|) ^ 3 * |b1loc_cutoff (r + s) - b1loc_cutoff r| ≤ 8 * C * s := by
  have hpos : 0 < (1 + |r|) ^ 3 := by positivity
  have hb : ∀ y ∈ Icc r (r + s), ‖deriv (⇑b1loc_cutoff) y‖ ≤ 8 * C / (1 + |r|) ^ 3 := by
    intro y hy
    rw [le_div_iff₀ hpos, Real.norm_eq_abs]
    have hry : 1 + |r| ≤ 2 * (1 + |y|) := by
      have e1 := abs_sub_abs_le_abs_sub r y
      have e2 : |r - y| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2]
      linarith [abs_nonneg y]
    have h3 : (1 + |r|) ^ 3 ≤ 8 * (1 + |y|) ^ 3 := by
      calc (1 + |r|) ^ 3 ≤ (2 * (1 + |y|)) ^ 3 := pow_le_pow_left₀ (by positivity) hry 3
        _ = 8 * (1 + |y|) ^ 3 := by ring
    calc |deriv (⇑b1loc_cutoff) y| * (1 + |r|) ^ 3
        ≤ |deriv (⇑b1loc_cutoff) y| * (8 * (1 + |y|) ^ 3) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = 8 * ((1 + |y|) ^ 3 * |deriv (⇑b1loc_cutoff) y|) := by ring
      _ ≤ 8 * C := by linarith [hC y]
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := ⇑b1loc_cutoff)
    (fun y _ => b1loc_cutoff.differentiableAt) hb (convex_Icc r (r + s))
    (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hs0] at hmvt
  calc (1 + |r|) ^ 3 * |b1loc_cutoff (r + s) - b1loc_cutoff r|
      ≤ (1 + |r|) ^ 3 * (8 * C / (1 + |r|) ^ 3 * s) := mul_le_mul_of_nonneg_left hmvt hpos.le
    _ = 8 * C * s := by
        have hne : (1 + |r|) ^ 3 ≠ 0 := hpos.ne'
        field_simp

/-! ## The integrable profile `(1 + |r|)^{-2}` -/

/-- `I₂ = ∫ (1 + |r|)^{-2} dr`. -/
def b1loc_I2 : ℝ := ∫ r : ℝ, (1 + ‖r‖) ^ (-(2 : ℝ))

theorem b1loc_integrable_decay2 : Integrable (fun r : ℝ => (1 + ‖r‖) ^ (-(2 : ℝ))) :=
  integrable_one_add_norm (by norm_num)

theorem b1loc_decay2_eq (r : ℝ) : (1 + ‖r‖) ^ (-(2 : ℝ)) = ((1 + |r|) ^ 2)⁻¹ := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two, Real.norm_eq_abs]

theorem b1loc_I2_nonneg : 0 ≤ b1loc_I2 :=
  integral_nonneg fun r => Real.rpow_nonneg (by positivity) _

/-! ## The Lipschitz bound along time translates -/

/-- A time shift by `r` moves `Ψ x` by exactly `√|r|`. -/
theorem b1loc_dist_sub_timeVector (x : FourierSpace m) (r : ℝ) :
    dist (fourierToParabolic m (x - r • timeVector m)) (fourierToParabolic m x) =
      Real.sqrt |r| := by
  simp only [fourierToParabolic_apply, coordinates_sub_timeVector]
  rw [dist_point, sub_self, norm_zero, sub_sub_cancel_left, abs_neg]
  exact max_eq_right (Real.sqrt_nonneg _)

/-- `|G(x - r e_t) - F(p₀)| ≤ 8 L (1 + |r|)` for `‖x - x₀‖ ≤ 7`. -/
theorem b1loc_abs_sub_shift_le {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) {x : FourierSpace m} (hx : ‖x - (fourierToParabolic m).symm p₀‖ ≤ 7)
    (r : ℝ) :
    |F (fourierToParabolic m (x - r • timeVector m)) - F p₀| ≤ 8 * L * (1 + |r|) := by
  have hd1 := b1loc_dist_sub_timeVector x r
  have hd2 := b1loc_dist_fourierToParabolic_le (by norm_num : (1 : ℝ) ≤ 7) hx
  rw [Homeomorph.apply_symm_apply] at hd2
  have hsq : Real.sqrt |r| ≤ 1 + |r| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg r]
  have hdist : dist (fourierToParabolic m (x - r • timeVector m)) p₀ ≤ 8 * (1 + |r|) := by
    calc dist (fourierToParabolic m (x - r • timeVector m)) p₀
        ≤ dist (fourierToParabolic m (x - r • timeVector m)) (fourierToParabolic m x) +
          dist (fourierToParabolic m x) p₀ := dist_triangle _ _ _
      _ ≤ (1 + |r|) + 7 := by
          rw [hd1]
          exact add_le_add hsq hd2
      _ ≤ 8 * (1 + |r|) := by linarith [abs_nonneg r]
  have h := hL.dist_le_mul (fourierToParabolic m (x - r • timeVector m)) p₀
  rw [Real.dist_eq] at h
  calc |F (fourierToParabolic m (x - r • timeVector m)) - F p₀|
      ≤ L * dist (fourierToParabolic m (x - r • timeVector m)) p₀ := h
    _ ≤ L * (8 * (1 + |r|)) := mul_le_mul_of_nonneg_left hdist L.2
    _ = 8 * L * (1 + |r|) := by ring

/-! ## The low-pass part -/

/-- The low-pass part `A = η *_t (G - F(p₀))`, `G = F ∘ Ψ`, `η = b1loc_cutoff`. -/
def b1loc_lowPass (m : ℕ) (F : Space m → ℝ) (p₀ : Space m) : FourierSpace m → ℝ :=
  fhp_timeConvolution (⇑b1loc_cutoff) (fun y => F (fourierToParabolic m y) - F p₀)

theorem b1loc_lowPass_apply (m : ℕ) (F : Space m → ℝ) (p₀ : Space m) (x : FourierSpace m) :
    b1loc_lowPass m F p₀ x =
      ∫ r : ℝ, b1loc_cutoff r * (F (fourierToParabolic m (x - r • timeVector m)) - F p₀) :=
  rfl

theorem b1loc_integrable_lowPass {F : Space m → ℝ} (p₀ : Space m)
    (hint : ∀ x : FourierSpace m, Integrable (fun s : ℝ =>
      b1loc_cutoff s * F (fourierToParabolic m (x - s • timeVector m))))
    (x : FourierSpace m) :
    Integrable (fun s : ℝ =>
      b1loc_cutoff s * (F (fourierToParabolic m (x - s • timeVector m)) - F p₀)) := by
  have h := (hint x).sub ((b1loc_cutoff.integrable (μ := volume)).mul_const (F p₀))
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [Pi.sub_apply]
  ring

/-- `|A(x)| ≤ 8 C I₂ L` on `‖x - x₀‖ ≤ 7`. -/
theorem b1loc_abs_lowPass_le {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m) {C : ℝ} (hC : ∀ r : ℝ, (1 + |r|) ^ 3 * |b1loc_cutoff r| ≤ C)
    {x : FourierSpace m} (hx : ‖x - (fourierToParabolic m).symm p₀‖ ≤ 7) :
    |b1loc_lowPass m F p₀ x| ≤ 8 * C * b1loc_I2 * L := by
  rw [b1loc_lowPass_apply, ← Real.norm_eq_abs]
  have hg : Integrable (fun r : ℝ => 8 * C * L * (1 + ‖r‖) ^ (-(2 : ℝ))) :=
    b1loc_integrable_decay2.const_mul _
  refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun r => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, b1loc_decay2_eq, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity)]
    have h1 := b1loc_abs_sub_shift_le hL p₀ hx r
    have h2 := hC r
    have hL0 : (0 : ℝ) ≤ 8 * L := by positivity
    calc |b1loc_cutoff r| * |F (fourierToParabolic m (x - r • timeVector m)) - F p₀| *
          (1 + |r|) ^ 2
        ≤ |b1loc_cutoff r| * (8 * L * (1 + |r|)) * (1 + |r|) ^ 2 := by gcongr
      _ = 8 * L * ((1 + |r|) ^ 3 * |b1loc_cutoff r|) := by ring
      _ ≤ 8 * L * C := mul_le_mul_of_nonneg_left h2 hL0
      _ = 8 * C * L := by ring
  · rw [integral_const_mul, b1loc_I2]
    ring

/-- The substitution `r ↦ r + s`: `A(x + s e_t) = ∫ η(r + s) (G(x - r e_t) - F(p₀)) dr`. -/
theorem b1loc_lowPass_shift_eq (F : Space m → ℝ) (p₀ : Space m) (x : FourierSpace m)
    (s : ℝ) :
    b1loc_lowPass m F p₀ (x + s • timeVector m) =
      ∫ r : ℝ, b1loc_cutoff (r + s) *
        (F (fourierToParabolic m (x - r • timeVector m)) - F p₀) := by
  have he : ∀ r : ℝ, x + s • timeVector m - (r + s) • timeVector m = x - r • timeVector m := by
    intro r
    rw [add_smul]
    abel
  have h : (∫ r : ℝ, b1loc_cutoff (r + s) *
        (F (fourierToParabolic m (x + s • timeVector m - (r + s) • timeVector m)) - F p₀)) =
      ∫ r : ℝ, b1loc_cutoff r *
        (F (fourierToParabolic m (x + s • timeVector m - r • timeVector m)) - F p₀) :=
    integral_add_right_eq_self (fun r : ℝ => b1loc_cutoff r *
      (F (fourierToParabolic m (x + s • timeVector m - r • timeVector m)) - F p₀)) s
  simp only [he] at h
  rw [b1loc_lowPass_apply]
  exact h.symm

/-- `|A(x + s e_t) - A(x)| ≤ 64 C I₂ L s` on `‖x - x₀‖ ≤ 7`, `0 ≤ s ≤ 1`. -/
theorem b1loc_lowPass_diff_le {F : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (p₀ : Space m)
    (hint : ∀ x : FourierSpace m, Integrable (fun s : ℝ =>
      b1loc_cutoff s * F (fourierToParabolic m (x - s • timeVector m))))
    {C : ℝ} (hC : ∀ r : ℝ, (1 + |r|) ^ 3 * |deriv (⇑b1loc_cutoff) r| ≤ C)
    {x : FourierSpace m} (hx : ‖x - (fourierToParabolic m).symm p₀‖ ≤ 7) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |b1loc_lowPass m F p₀ (x + s • timeVector m) - b1loc_lowPass m F p₀ x| ≤
      64 * C * b1loc_I2 * L * s := by
  have he : ∀ r : ℝ, x + s • timeVector m - (r + s) • timeVector m = x - r • timeVector m := by
    intro r
    rw [add_smul]
    abel
  have hA1 : Integrable (fun r : ℝ => b1loc_cutoff (r + s) *
      (F (fourierToParabolic m (x - r • timeVector m)) - F p₀)) := by
    have h := (b1loc_integrable_lowPass p₀ hint (x + s • timeVector m)).comp_add_right s
    refine h.congr (Eventually.of_forall fun r => ?_)
    simp only [he]
  have hA0 := b1loc_integrable_lowPass p₀ hint x
  rw [b1loc_lowPass_shift_eq, b1loc_lowPass_apply, ← integral_sub hA1 hA0, ← Real.norm_eq_abs]
  have hg : Integrable (fun r : ℝ => 64 * C * L * s * (1 + ‖r‖) ^ (-(2 : ℝ))) :=
    b1loc_integrable_decay2.const_mul _
  refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun r => ?_)).trans
    (le_of_eq ?_)
  · rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, b1loc_decay2_eq,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have h1 := b1loc_abs_sub_shift_le hL p₀ hx r
    have h2 := b1loc_cutoff_sub_le hC r hs0 hs1
    have hL0 : (0 : ℝ) ≤ 8 * L := by positivity
    calc |b1loc_cutoff (r + s) - b1loc_cutoff r| *
          |F (fourierToParabolic m (x - r • timeVector m)) - F p₀| * (1 + |r|) ^ 2
        ≤ |b1loc_cutoff (r + s) - b1loc_cutoff r| * (8 * L * (1 + |r|)) * (1 + |r|) ^ 2 := by
          gcongr
      _ = 8 * L * ((1 + |r|) ^ 3 * |b1loc_cutoff (r + s) - b1loc_cutoff r|) := by ring
      _ ≤ 8 * L * (8 * C * s) := mul_le_mul_of_nonneg_left h2 hL0
      _ = 64 * C * L * s := by ring
  · rw [integral_const_mul, b1loc_I2]
    ring

theorem b1loc_aestronglyMeasurable_lowPass {F : Space m → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (p₀ : Space m) :
    AEStronglyMeasurable (b1loc_lowPass m F p₀) volume := by
  have hc : Continuous (fun p : FourierSpace m × ℝ =>
      b1loc_cutoff p.2 * (F (fourierToParabolic m (p.1 - p.2 • timeVector m)) - F p₀)) :=
    (b1loc_cutoff.continuous.comp continuous_snd).mul
      ((hL.continuous.comp ((fourierToParabolic m).continuous.comp
        (continuous_fst.sub (continuous_snd.smul continuous_const)))).sub continuous_const)
  exact (hc.aestronglyMeasurable
    (μ := (volume : Measure (FourierSpace m)).prod (volume : Measure ℝ))).integral_prod_right'

/-! ## Local energy from pointwise bounds -/

theorem b1loc_setLIntegral_ball_sq_le (x₀ : FourierSpace m) {h : FourierSpace m → ℝ} {c : ℝ}
    (hc : ∀ x ∈ Metric.ball x₀ 7, |h x| ≤ c) :
    ∫⁻ x in Metric.ball x₀ 7, ‖h x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := by
  calc ∫⁻ x in Metric.ball x₀ 7, ‖h x‖ₑ ^ 2
      ≤ ∫⁻ _x in Metric.ball x₀ 7, ENNReal.ofReal (c ^ 2) := by
        refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hc x hx) 2)
    _ = ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := by
        rw [setLIntegral_const, b1loc_volume_ball_seven, ← ENNReal.ofReal_mul (sq_nonneg c)]

/-- `s^{-2} · s² q = q`. -/
theorem b1loc_inv_sq_mul_ofReal (s : ℝ) (hs : 0 < s) (q : ℝ) :
    (ENNReal.ofReal s)⁻¹ ^ 2 * ENNReal.ofReal (s ^ 2 * q) = ENNReal.ofReal q := by
  have hs2 : (ENNReal.ofReal s)⁻¹ ^ 2 * ENNReal.ofReal (s ^ 2) = 1 := by
    rw [ENNReal.ofReal_pow hs.le, ← mul_pow, ENNReal.inv_mul_cancel
      (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top, one_pow]
  rw [ENNReal.ofReal_mul (sq_nonneg s), ← mul_assoc, hs2, one_mul]

/-- Pointwise bounds `|h| ≤ c` and `|h(x + s e_t) - h(x)| ≤ c s` on `B(x₀,7)`, `0 < s ≤ 1`, give
`LGag(h) + ∫_{B(x₀,7)} |h|² ≤ 2 c² V`. -/
theorem b1loc_local_energy_le_of_bounds (x₀ : FourierSpace m) {h : FourierSpace m → ℝ}
    {c : ℝ} (h0 : ∀ x ∈ Metric.ball x₀ 7, |h x| ≤ c)
    (h1 : ∀ x ∈ Metric.ball x₀ 7, ∀ s : ℝ, 0 < s → s ≤ 1 →
      |h (x + s • timeVector m) - h x| ≤ c * s) :
    b1loc_localGagliardo x₀ h + ∫⁻ x in Metric.ball x₀ 7, ‖h x‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * c ^ 2 * b1loc_ballVolume m) := by
  have hV := b1loc_ballVolume_nonneg m
  have hLG : b1loc_localGagliardo x₀ h ≤ ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := by
    unfold b1loc_localGagliardo
    calc ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
          ∫⁻ x in Metric.ball x₀ 7, ‖h (x + s • timeVector m) - h x‖ₑ ^ 2
        ≤ ∫⁻ _s in Ioc (0 : ℝ) 1, ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          have hb := b1loc_setLIntegral_ball_sq_le x₀
            (h := fun x => h (x + s • timeVector m) - h x) (c := c * s)
            fun x hx => h1 x hx s hs.1 hs.2
          calc (ENNReal.ofReal s)⁻¹ ^ 2 *
                ∫⁻ x in Metric.ball x₀ 7, ‖h (x + s • timeVector m) - h x‖ₑ ^ 2
              ≤ (ENNReal.ofReal s)⁻¹ ^ 2 *
                  ENNReal.ofReal ((c * s) ^ 2 * b1loc_ballVolume m) :=
                mul_le_mul_of_nonneg_left hb zero_le
            _ = (ENNReal.ofReal s)⁻¹ ^ 2 *
                  ENNReal.ofReal (s ^ 2 * (c ^ 2 * b1loc_ballVolume m)) := by
                rw [show (c * s) ^ 2 * b1loc_ballVolume m =
                  s ^ 2 * (c ^ 2 * b1loc_ballVolume m) by ring]
            _ = ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) :=
                b1loc_inv_sq_mul_ofReal s hs.1 _
      _ = ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  have h2 := b1loc_setLIntegral_ball_sq_le x₀ h0
  calc b1loc_localGagliardo x₀ h + ∫⁻ x in Metric.ball x₀ 7, ‖h x‖ₑ ^ 2
      ≤ ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) +
          ENNReal.ofReal (c ^ 2 * b1loc_ballVolume m) := add_le_add hLG h2
    _ = ENNReal.ofReal (2 * c ^ 2 * b1loc_ballVolume m) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

theorem b1loc_two_six_le (a b : ℝ≥0∞) :
    ENNReal.ofReal 2 * a + ENNReal.ofReal 6 * b ≤ ENNReal.ofReal 6 * (a + b) := by
  have h26 : ENNReal.ofReal 2 ≤ ENNReal.ofReal 6 := ENNReal.ofReal_le_ofReal (by norm_num)
  calc ENNReal.ofReal 2 * a + ENNReal.ofReal 6 * b
      ≤ ENNReal.ofReal 6 * a + ENNReal.ofReal 6 * b := by gcongr
    _ = ENNReal.ofReal 6 * (a + b) := (mul_add _ _ _).symm

/-- A function bounded by `c` on `B(x₀,7)`, multiplied by the cutoff, is in `L²`. -/
theorem b1loc_memLp_cut_mul_of_bound (x₀ : FourierSpace m) {h : FourierSpace m → ℝ}
    (hm : AEStronglyMeasurable h volume) {c : ℝ} (hc : ∀ x ∈ Metric.ball x₀ 7, |h x| ≤ c) :
    MemLp (fun x => b1loc_cut x₀ x * h x) 2 volume := by
  have hI : MemLp ((Metric.ball x₀ 7).indicator (fun _ => c)) 2 volume :=
    memLp_indicator_const 2 measurableSet_ball.nullMeasurableSet c
      (Or.inr (MeasureTheory.measure_ball_lt_top).ne)
  refine hI.of_le ((b1loc_continuous_cut x₀).aestronglyMeasurable.mul hm)
    (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Metric.ball x₀ 7
  · rw [indicator_of_mem hx, norm_mul]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (b1loc_cut_nonneg _ _)]
    calc b1loc_cut x₀ x * |h x| ≤ 1 * c :=
          mul_le_mul (b1loc_cut_le_one _ _) (hc x hx) (abs_nonneg _) zero_le_one
      _ ≤ |c| := by
          rw [one_mul]
          exact le_abs_self _
  · have h7 : 7 ≤ ‖x - x₀‖ := by
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hx
      exact hx
    rw [b1loc_cut_eq_zero (by linarith), zero_mul, norm_zero]
    exact norm_nonneg _

/-! ## The low-pass estimate -/

/-- **Low-pass estimate.** There is `C` (depending only on `m` and the fixed cutoff) such that
for every parabolic `L`-Lipschitz `F` and centre `p₀`, if the low-pass integrals converge
(clause 1 of (c2)), then `χ_{x₀} A ∈ L²` and `b1loc_timeGagliardo (χ_{x₀} A) ≤ C L²`. -/
theorem b1loc_lowPass_estimate (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Space m → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ p₀ : Space m,
      (∀ x : FourierSpace m, Integrable (fun s : ℝ =>
        b1loc_cutoff s * F (fourierToParabolic m (x - s • timeVector m)))) →
      MemLp (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
        b1loc_lowPass m F p₀ x) 2 volume ∧
      b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
        b1loc_lowPass m F p₀ x) ≤ ENNReal.ofReal (C * (L : ℝ) ^ 2) := by
  obtain ⟨Cη, hCη0, hCη⟩ := b1loc_cutoff_decay
  have hI2 := b1loc_I2_nonneg
  have hV := b1loc_ballVolume_nonneg m
  refine ⟨12 * (64 * Cη * b1loc_I2) ^ 2 * b1loc_ballVolume m,
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hV, fun F L hL p₀ hint => ?_⟩
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hb0 : ∀ x ∈ Metric.ball ((fourierToParabolic m).symm p₀) 7,
      |b1loc_lowPass m F p₀ x| ≤ 64 * Cη * b1loc_I2 * L := by
    intro x hx
    refine (b1loc_abs_lowPass_le hL p₀ (fun r => (hCη r).1)
      (mem_ball_iff_norm.1 hx).le).trans ?_
    have : 0 ≤ Cη * b1loc_I2 * L := mul_nonneg (mul_nonneg hCη0 hI2) hL0
    linarith
  have hb1 : ∀ x ∈ Metric.ball ((fourierToParabolic m).symm p₀) 7, ∀ s : ℝ, 0 < s → s ≤ 1 →
      |b1loc_lowPass m F p₀ (x + s • timeVector m) - b1loc_lowPass m F p₀ x| ≤
        64 * Cη * b1loc_I2 * L * s := fun x hx s hs0 hs1 =>
    b1loc_lowPass_diff_le hL p₀ hint (fun r => (hCη r).2) (mem_ball_iff_norm.1 hx).le
      hs0.le hs1
  have hE := b1loc_local_energy_le_of_bounds _ hb0 hb1
  refine ⟨b1loc_memLp_cut_mul_of_bound _ (b1loc_aestronglyMeasurable_lowPass hL p₀) hb0, ?_⟩
  calc b1loc_timeGagliardo (fun x => b1loc_cut ((fourierToParabolic m).symm p₀) x *
        b1loc_lowPass m F p₀ x)
      ≤ ENNReal.ofReal 2 * b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
            (b1loc_lowPass m F p₀) +
          ENNReal.ofReal 6 * ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            ‖b1loc_lowPass m F p₀ x‖ₑ ^ 2 :=
        b1loc_timeGagliardo_cut_mul_le _ (b1loc_aestronglyMeasurable_lowPass hL p₀)
    _ ≤ ENNReal.ofReal 6 * (b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
            (b1loc_lowPass m F p₀) +
          ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            ‖b1loc_lowPass m F p₀ x‖ₑ ^ 2) := b1loc_two_six_le _ _
    _ ≤ ENNReal.ofReal 6 *
          ENNReal.ofReal (2 * (64 * Cη * b1loc_I2 * L) ^ 2 * b1loc_ballVolume m) :=
        mul_le_mul_of_nonneg_left hE zero_le
    _ = ENNReal.ofReal (12 * (64 * Cη * b1loc_I2) ^ 2 * b1loc_ballVolume m * (L : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end ParabolicRectifiability.Characterization
