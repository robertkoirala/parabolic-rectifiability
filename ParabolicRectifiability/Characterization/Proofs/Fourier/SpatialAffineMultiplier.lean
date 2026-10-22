import ParabolicRectifiability.Characterization.Proofs.Fourier.SpatialAffineTranslates

/-! # The spatial residual multiplier and the scale integral

The affine competitor used for `ba1_spatial_affine_square_proof` at the centre `u` and scale `s` is
`v ↦ G(u) + ∑_j ((v - u)_j / s) (G(u + s e_j) - G(u))`, the first-order Taylor polynomial of `G`
at `u` with the finite-difference gradient at step `s`. For an increment `h` the residual
`G(u + h) - G(u) - ∑_j (h_j / s) (G(u + s e_j) - G(u))` is the combination of translate
differences with coefficients `b1sas_coef s h` and translations `b1sas_vec s h`. Its Fourier
multiplier, the **residual's** multiplier against the spatial Taylor polynomial, is `M_{s,h}(ξ) = (e(⟨h,ξ⟩) - 1) - ∑_j (h_j/s) (e(s ξ_j) - 1)`.

For `‖h‖ < s`: `|M_{s,h}(ξ)| ≤ K_k min(1, (s|ξ|)²)` with `K_k = 24π² + 2k + 2`. The first-order
Taylor terms cancel exactly (`2πi⟨h,ξ⟩ = ∑_j (h_j/s) 2πi sξ_j`), the second-order remainders are
`≤ 12π²(s|ξ|)²` each in total, and every term is bounded. The scale integral is
`∫_0^∞ s^{-2} min(1, s² a)² ds/s ≤ a` (split at `s = a^{-1/2}`; the same argument as
`b1fas_lintegral_scale_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

variable {k : ℕ}

/-! ### The finite-difference families -/

/-- The `j`-th unit vector `e_j` of `ℝ^k`. -/
def b1sas_unit (j : Fin k) : Spatial k :=
  EuclideanSpace.single j (1 : ℝ)

/-- Coefficients of the residual at scale `s` and increment `h`: `1` on the translation `h`
and `-h_j / s` on the translation `s e_j`. -/
def b1sas_coef (s : ℝ) (h : Spatial k) : Option (Fin k) → ℝ
  | none => 1
  | some j => -(h j / s)

/-- Translations of the residual at scale `s` and increment `h`. -/
def b1sas_vec (s : ℝ) (h : Spatial k) : Option (Fin k) → Spatial k
  | none => h
  | some j => s • b1sas_unit j

theorem b1sas_inner_unit (j : Fin k) (ξ : Spatial k) :
    inner ℝ (b1sas_unit j) ξ = ξ j := by
  simp [b1sas_unit, EuclideanSpace.inner_single_left]

/-! ### Elementary bounds for the character -/

theorem b1sas_norm_exp_sub_le (y : ℝ) :
    ‖Complex.exp (↑y * Complex.I) - 1 - ↑y * Complex.I‖ ≤ 3 * y ^ 2 := by
  have hn : ‖(↑y * Complex.I : ℂ)‖ = |y| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  by_cases hy : |y| ≤ 1
  · have h := Complex.norm_exp_sub_one_sub_id_le (x := ↑y * Complex.I) (by rw [hn]; exact hy)
    rw [hn, sq_abs] at h
    nlinarith [sq_nonneg y]
  · rw [not_le] at hy
    have h1 : ‖Complex.exp (↑y * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I y
    have h2 : ‖Complex.exp (↑y * Complex.I) - 1 - ↑y * Complex.I‖ ≤ 1 + 1 + |y| := by
      calc ‖Complex.exp (↑y * Complex.I) - 1 - ↑y * Complex.I‖
          ≤ ‖Complex.exp (↑y * Complex.I) - 1‖ + ‖(↑y * Complex.I : ℂ)‖ := norm_sub_le _ _
        _ ≤ (‖Complex.exp (↑y * Complex.I)‖ + ‖(1 : ℂ)‖) + ‖(↑y * Complex.I : ℂ)‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = 1 + 1 + |y| := by rw [h1, norm_one, hn]
    have h3 : |y| ≤ y ^ 2 := by
      rw [← sq_abs]
      nlinarith
    nlinarith

theorem b1sas_norm_char_sub_le (x : ℝ) :
    ‖(𝐞 x : ℂ) - 1 - ((2 * π * x : ℝ) : ℂ) * Complex.I‖ ≤ 12 * π ^ 2 * x ^ 2 := by
  rw [Real.fourierChar_apply]
  calc ‖Complex.exp (↑(2 * π * x) * Complex.I) - 1 - ((2 * π * x : ℝ) : ℂ) * Complex.I‖
      ≤ 3 * (2 * π * x) ^ 2 := b1sas_norm_exp_sub_le (2 * π * x)
    _ = 12 * π ^ 2 * x ^ 2 := by ring

theorem b1sas_norm_char_sub_one_le (x : ℝ) : ‖(𝐞 x : ℂ) - 1‖ ≤ 2 :=
  (norm_sub_le _ _).trans (by rw [Circle.norm_coe, norm_one]; norm_num)

/-! ### The residual multiplier -/

theorem b1sas_sum_identity {n : ℕ} (a x : ℂ) (d b y : Fin n → ℂ) :
    a - ∑ j, d j * b j = (a - x) - ∑ j, d j * (b j - y j) + (x - ∑ j, d j * y j) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem b1sas_mult_eq (s : ℝ) (h ξ : Spatial k) :
    b1sas_mult Finset.univ (b1sas_coef s h) (b1sas_vec s h) ξ =
      ((𝐞 (inner ℝ h ξ) : ℂ) - 1) -
        ∑ j : Fin k, ((h j / s : ℝ) : ℂ) * ((𝐞 (s * ξ j) : ℂ) - 1) := by
  simp only [b1sas_mult, Fintype.sum_option, b1sas_coef, b1sas_vec, real_inner_smul_left,
    b1sas_inner_unit, Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul,
    Finset.sum_neg_distrib]
  ring

/-- The quadratic bound of the residual multiplier: for `‖h‖ < s`,
`|M_{s,h}(ξ)| ≤ 24π² (s|ξ|)²`. -/
theorem b1sas_norm_mult_le_quad {s : ℝ} (hs : 0 < s) {h : Spatial k} (hh : ‖h‖ < s)
    (ξ : Spatial k) :
    ‖b1sas_mult Finset.univ (b1sas_coef s h) (b1sas_vec s h) ξ‖ ≤
      24 * π ^ 2 * (s ^ 2 * ‖ξ‖ ^ 2) := by
  have hs0 : s ≠ 0 := hs.ne'
  set θ : ℝ := inner ℝ h ξ with hθdef
  have hθ : θ = ∑ j, h j * ξ j := by
    rw [hθdef, PiLp.inner_apply]
    simp only [Real.inner_apply]
  have hθabs : |θ| ≤ s * ‖ξ‖ :=
    (abs_real_inner_le_norm h ξ).trans (mul_le_mul_of_nonneg_right hh.le (norm_nonneg _))
  have hθsq : θ ^ 2 ≤ s ^ 2 * ‖ξ‖ ^ 2 := by
    rw [← sq_abs θ, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg θ) hθabs 2
  have hd : ∀ j, |h j / s| ≤ 1 := by
    intro j
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    have := PiLp.norm_apply_le h j
    rw [Real.norm_eq_abs] at this
    linarith
  have hterm' : ∀ j : Fin k, ((h j / s : ℝ) : ℂ) * (((2 * π * (s * ξ j) : ℝ) : ℂ) * Complex.I) =
      ((2 * π * (h j * ξ j) : ℝ) : ℂ) * Complex.I := by
    intro j
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [div_mul_eq_mul_div, div_eq_iff hs0]
    ring
  have hT3 : ((2 * π * θ : ℝ) : ℂ) * Complex.I -
      ∑ j : Fin k, ((h j / s : ℝ) : ℂ) * (((2 * π * (s * ξ j) : ℝ) : ℂ) * Complex.I) = 0 := by
    simp only [hterm']
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hθ, Finset.mul_sum, sub_self]
  have hT1 : ‖(𝐞 θ : ℂ) - 1 - ((2 * π * θ : ℝ) : ℂ) * Complex.I‖ ≤ 12 * π ^ 2 * θ ^ 2 :=
    b1sas_norm_char_sub_le θ
  have hT2 : ‖∑ j : Fin k, ((h j / s : ℝ) : ℂ) * (((𝐞 (s * ξ j) : ℂ) - 1) -
      ((2 * π * (s * ξ j) : ℝ) : ℂ) * Complex.I)‖ ≤ 12 * π ^ 2 * (s ^ 2 * ‖ξ‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j : Fin k, ‖((h j / s : ℝ) : ℂ) * (((𝐞 (s * ξ j) : ℂ) - 1) -
        ((2 * π * (s * ξ j) : ℝ) : ℂ) * Complex.I)‖ ≤ 12 * π ^ 2 * (s ^ 2 * ξ j ^ 2) := by
      intro j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |h j / s| * ‖((𝐞 (s * ξ j) : ℂ) - 1) - ((2 * π * (s * ξ j) : ℝ) : ℂ) * Complex.I‖
          ≤ 1 * (12 * π ^ 2 * (s * ξ j) ^ 2) :=
            mul_le_mul (hd j) (b1sas_norm_char_sub_le (s * ξ j)) (norm_nonneg _) zero_le_one
        _ = 12 * π ^ 2 * (s ^ 2 * ξ j ^ 2) := by ring
    refine (Finset.sum_le_sum fun j _ => hterm j).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  rw [b1sas_mult_eq, ← hθdef, b1sas_sum_identity _ (((2 * π * θ : ℝ) : ℂ) * Complex.I) _ _
    (fun j => ((2 * π * (s * ξ j) : ℝ) : ℂ) * Complex.I), hT3, add_zero]
  refine (norm_sub_le _ _).trans ?_
  have := mul_le_mul_of_nonneg_left hθsq (by positivity : (0 : ℝ) ≤ 12 * π ^ 2)
  linarith

/-- The bounded estimate of the residual multiplier: for `‖h‖ < s`, `|M_{s,h}(ξ)| ≤ 2k + 2`. -/
theorem b1sas_norm_mult_le_const {s : ℝ} (hs : 0 < s) {h : Spatial k} (hh : ‖h‖ < s)
    (ξ : Spatial k) :
    ‖b1sas_mult Finset.univ (b1sas_coef s h) (b1sas_vec s h) ξ‖ ≤ 2 * k + 2 := by
  have hd : ∀ j, |h j / s| ≤ 1 := by
    intro j
    rw [abs_div, abs_of_pos hs, div_le_one hs]
    have := PiLp.norm_apply_le h j
    rw [Real.norm_eq_abs] at this
    linarith
  rw [b1sas_mult_eq]
  refine (norm_sub_le _ _).trans ?_
  have hsum : ‖∑ j : Fin k, ((h j / s : ℝ) : ℂ) * ((𝐞 (s * ξ j) : ℂ) - 1)‖ ≤ 2 * k := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin k, ‖((h j / s : ℝ) : ℂ) * ((𝐞 (s * ξ j) : ℂ) - 1)‖
        ≤ ∑ _j : Fin k, (2 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |h j / s| * ‖(𝐞 (s * ξ j) : ℂ) - 1‖
              ≤ 1 * 2 := mul_le_mul (hd j) (b1sas_norm_char_sub_one_le _) (norm_nonneg _)
                zero_le_one
            _ = 2 := one_mul 2
      _ = 2 * k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have h1 := b1sas_norm_char_sub_one_le (inner ℝ h ξ)
  linarith

/-- The multiplier constant `K_k = 24π² + 2k + 2`. -/
def b1sas_K (k : ℕ) : ℝ := 24 * π ^ 2 + 2 * k + 2

theorem b1sas_K_nonneg (k : ℕ) : 0 ≤ b1sas_K k := by
  unfold b1sas_K
  positivity

/-- **The residual multiplier bound**: for every increment
`‖h‖ < s`, the multiplier of the residual of `G` against its spatial first-order Taylor
polynomial at scale `s` satisfies `|M_{s,h}(ξ)| ≤ K_k min(1, (s|ξ|)²)`. -/
theorem b1sas_norm_mult_le_min {s : ℝ} (hs : 0 < s) {h : Spatial k} (hh : ‖h‖ < s)
    (ξ : Spatial k) :
    ‖b1sas_mult Finset.univ (b1sas_coef s h) (b1sas_vec s h) ξ‖ ≤
      b1sas_K k * min 1 (s ^ 2 * ‖ξ‖ ^ 2) := by
  have hpi : 3 < π := Real.pi_gt_three
  have hX0 : 0 ≤ s ^ 2 * ‖ξ‖ ^ 2 := by positivity
  by_cases hc : s ^ 2 * ‖ξ‖ ^ 2 ≤ 1
  · rw [min_eq_right hc]
    have hq := b1sas_norm_mult_le_quad hs hh ξ
    have hK : 24 * π ^ 2 * (s ^ 2 * ‖ξ‖ ^ 2) ≤ b1sas_K k * (s ^ 2 * ‖ξ‖ ^ 2) := by
      unfold b1sas_K
      have : 0 ≤ (2 * (k : ℝ) + 2) * (s ^ 2 * ‖ξ‖ ^ 2) := by positivity
      nlinarith
    linarith
  · rw [not_le] at hc
    rw [min_eq_left hc.le, mul_one]
    have hb := b1sas_norm_mult_le_const hs hh ξ
    unfold b1sas_K
    have : 0 ≤ 24 * π ^ 2 := by positivity
    linarith

theorem b1sas_enorm_mult_sq_le {s : ℝ} (hs : 0 < s) {h : Spatial k} (hh : ‖h‖ < s)
    (ξ : Spatial k) :
    ‖b1sas_mult Finset.univ (b1sas_coef s h) (b1sas_vec s h) ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal (b1sas_K k ^ 2 * min 1 (s ^ 2 * ‖ξ‖ ^ 2) ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← mul_pow]
  exact ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (norm_nonneg _) (b1sas_norm_mult_le_min hs hh ξ) 2)

/-! ### The scale integral -/

/-- `∫_0^∞ s^{-2} min(1, s² a)² ds/s ≤ a` (the form used here). -/
theorem b1sas_lintegral_scale_le {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ r, (ENNReal.ofReal r)⁻¹ ^ 2 * ENNReal.ofReal (min 1 (r ^ 2 * a) ^ 2) ∂scaleMeasure ≤
      ENNReal.ofReal a := by
  rw [scaleMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    measurable_scaleDensity (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]
  have hpt : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (1 / r) * ((ENNReal.ofReal r)⁻¹ ^ 2 *
      ENNReal.ofReal (min 1 (r ^ 2 * a) ^ 2)) =
        ENNReal.ofReal (r⁻¹ ^ 3 * min 1 (r ^ 2 * a) ^ 2) := by
    intro r hr
    have hr' : 0 < r := hr
    rw [← ENNReal.ofReal_inv_of_pos hr', ← ENNReal.ofReal_pow (inv_nonneg.2 hr'.le),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r⁻¹ ^ 2),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / r)]
    congr 1
    rw [one_div]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    simp
  set r₀ : ℝ := (√a)⁻¹ with hr₀def
  have hr₀ : 0 < r₀ := inv_pos.2 (Real.sqrt_pos.2 hpos)
  have hr₀sq : r₀ ^ 2 = a⁻¹ := by
    rw [hr₀def, inv_pow, Real.sq_sqrt ha]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 r₀ ∪ Ioi r₀ := (Ioc_union_Ioi_eq_Ioi hr₀.le).symm
  rw [hsplit]
  refine (lintegral_union_le _ _ _).trans ?_
  have h1 : ∫⁻ r in Ioc 0 r₀, ENNReal.ofReal (r⁻¹ ^ 3 * min 1 (r ^ 2 * a) ^ 2) ≤
      ENNReal.ofReal (a / 2) := by
    calc ∫⁻ r in Ioc 0 r₀, ENNReal.ofReal (r⁻¹ ^ 3 * min 1 (r ^ 2 * a) ^ 2)
        ≤ ∫⁻ r in Ioc 0 r₀, ENNReal.ofReal (a ^ 2 * r) := by
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ENNReal.ofReal_le_ofReal ?_
          have hr0 : 0 < r := hr.1
          have hmin0 : 0 ≤ min 1 (r ^ 2 * a) := le_min zero_le_one (by positivity)
          have hmin : min 1 (r ^ 2 * a) ^ 2 ≤ (r ^ 2 * a) ^ 2 :=
            pow_le_pow_left₀ hmin0 (min_le_right _ _) 2
          calc r⁻¹ ^ 3 * min 1 (r ^ 2 * a) ^ 2 ≤ r⁻¹ ^ 3 * (r ^ 2 * a) ^ 2 :=
                mul_le_mul_of_nonneg_left hmin (by positivity)
            _ = a ^ 2 * r := by
                field_simp
      _ = ENNReal.ofReal (∫ r in Ioc 0 r₀, a ^ 2 * r) := by
          refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
          · exact (continuous_const.mul continuous_id).integrableOn_Ioc
          · exact (ae_restrict_iff' measurableSet_Ioc).2
              (Eventually.of_forall fun r hr => by
                have : 0 < r := hr.1
                positivity)
      _ = ENNReal.ofReal (a / 2) := by
          congr 1
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hr₀.le, integral_id, hr₀sq]
          field_simp
          ring
  have h2 : ∫⁻ r in Ioi r₀, ENNReal.ofReal (r⁻¹ ^ 3 * min 1 (r ^ 2 * a) ^ 2) ≤
      ENNReal.ofReal (a / 2) := by
    calc ∫⁻ r in Ioi r₀, ENNReal.ofReal (r⁻¹ ^ 3 * min 1 (r ^ 2 * a) ^ 2)
        ≤ ∫⁻ r in Ioi r₀, ENNReal.ofReal (r ^ (-3 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun r hr => ENNReal.ofReal_le_ofReal ?_
          have hr0 : 0 < r := hr₀.trans hr
          have hmin0 : 0 ≤ min 1 (r ^ 2 * a) := le_min zero_le_one (by positivity)
          have hmin : min 1 (r ^ 2 * a) ^ 2 ≤ 1 := by
            have := min_le_left 1 (r ^ 2 * a)
            nlinarith
          have hrp : r ^ (-3 : ℝ) = r⁻¹ ^ 3 := by
            rw [Real.rpow_neg hr0.le, inv_pow]
            norm_cast
          rw [hrp]
          calc r⁻¹ ^ 3 * min 1 (r ^ 2 * a) ^ 2 ≤ r⁻¹ ^ 3 * 1 :=
                mul_le_mul_of_nonneg_left hmin (by positivity)
            _ = r⁻¹ ^ 3 := mul_one _
      _ = ENNReal.ofReal (∫ r in Ioi r₀, r ^ (-3 : ℝ)) := by
          refine (ofReal_integral_eq_lintegral_ofReal
            (integrableOn_Ioi_rpow_of_lt (by norm_num) hr₀) ?_).symm
          exact (ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun r hr => Real.rpow_nonneg (hr₀.trans hr).le _)
      _ = ENNReal.ofReal (a / 2) := by
          congr 1
          rw [integral_Ioi_rpow_of_lt (by norm_num) hr₀]
          have h22 : r₀ ^ (-3 + 1 : ℝ) = a := by
            rw [show (-3 + 1 : ℝ) = -2 by norm_num, Real.rpow_neg hr₀.le]
            norm_cast
            rw [hr₀sq, inv_inv]
          rw [h22]
          ring
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ a / 2) (by positivity : (0 : ℝ) ≤ a / 2)]
  ring_nf

end ParabolicRectifiability.Characterization
