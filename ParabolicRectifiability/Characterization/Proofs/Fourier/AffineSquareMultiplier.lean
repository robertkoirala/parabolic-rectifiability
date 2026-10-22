import ParabolicRectifiability.Characterization.Proofs.Fourier.AffineSquareTranslates

/-! # The finite-difference multiplier and the scale integral

The affine competitor used for `ba1_fourier_affine_square_proof` at the centre `p` and scale `r` is
`a + B·u` with `a + B·u_p = H(p)` and the finite-difference gradient
`B_j = (H(p + r e_j) - H(p)) / r`. For an increment `w = (h, s)` the residual
`H(p + w) - H(p) - ∑_j (h_j / r) (H(p + r e_j) - H(p))` is the combination of translate
differences with coefficients `b1fas_coef r w` and translations `b1fas_vec r w`; its Fourier
multiplier is `M = (e(⟨w,ζ⟩) - 1) - ∑_j (h_j/r) (e(r ξ_j) - 1)`.

For `‖h‖ < r`, `|s| < r²` and `ζ = (ξ, τ)`, with `a = |ξ|² + |τ|`:
`|M| ≤ K_m min(1, r² a)`, `K_m = 38π² + 2m + 2`. Indeed the first-order Taylor terms cancel
up to `2πi sτ` (`|sτ| ≤ r²|τ|`), the second-order remainders are `O(r²|ξ|² + r⁴τ²)`, and
`r⁴τ² ≤ r²|τ|` when `r²|τ| ≤ 1`; for `r² a > 1` every term is bounded. The scale integral is
`∫_0^∞ r^{-2} min(1, r² a)² dr/r = a` (split at `r = a^{-1/2}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.FourierAffine

variable {m : ℕ}

/-! ### The finite-difference families -/

/-- The `j`-th spatial unit vector `(e_j, 0)` of `FourierSpace m`. -/
def b1fas_unit (j : Fin m) : FourierSpace m :=
  WithLp.toLp 2 (EuclideanSpace.single j (1 : ℝ), (0 : ℝ))

/-- Coefficients of the residual at scale `r` and increment `w`: `1` on the translation `w`
and `-w_j / r` on the translation `r e_j`. -/
def b1fas_coef (r : ℝ) (w : FourierSpace m) : Option (Fin m) → ℝ
  | none => 1
  | some j => -((WithLp.ofLp w).1 j / r)

/-- Translations of the residual at scale `r` and increment `w`. -/
def b1fas_vec (r : ℝ) (w : FourierSpace m) : Option (Fin m) → FourierSpace m
  | none => w
  | some j => r • b1fas_unit j

theorem b1fas_inner_unit (j : Fin m) (ζ : FourierSpace m) :
    inner ℝ (b1fas_unit j) ζ = (WithLp.ofLp ζ).1 j := by
  simp [b1fas_unit, WithLp.prod_inner_apply, EuclideanSpace.inner_single_left]

theorem b1fas_mem_coordBall_zero {r : ℝ} {w : FourierSpace m} :
    w ∈ coordBall 0 r ↔ ‖(WithLp.ofLp w).1‖ < r ∧ |(WithLp.ofLp w).2| < r ^ 2 := by
  simp [coordBall]

/-! ### Elementary bounds for the character -/

theorem b1fas_norm_exp_sub_le (y : ℝ) :
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

theorem b1fas_norm_char_sub_le (x : ℝ) :
    ‖(𝐞 x : ℂ) - 1 - ((2 * π * x : ℝ) : ℂ) * Complex.I‖ ≤ 12 * π ^ 2 * x ^ 2 := by
  rw [Real.fourierChar_apply]
  calc ‖Complex.exp (↑(2 * π * x) * Complex.I) - 1 - ((2 * π * x : ℝ) : ℂ) * Complex.I‖
      ≤ 3 * (2 * π * x) ^ 2 := b1fas_norm_exp_sub_le (2 * π * x)
    _ = 12 * π ^ 2 * x ^ 2 := by ring

theorem b1fas_norm_char_sub_one_le (x : ℝ) : ‖(𝐞 x : ℂ) - 1‖ ≤ 2 :=
  (norm_sub_le _ _).trans (by rw [Circle.norm_coe, norm_one]; norm_num)

/-! ### The multiplier -/

theorem b1fas_sum_identity {n : ℕ} (a x : ℂ) (d b y : Fin n → ℂ) :
    a - ∑ j, d j * b j = (a - x) - ∑ j, d j * (b j - y j) + (x - ∑ j, d j * y j) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem b1fas_mult_eq (r : ℝ) (w ζ : FourierSpace m) :
    b1fas_mult Finset.univ (b1fas_coef r w) (b1fas_vec r w) ζ =
      ((𝐞 (inner ℝ w ζ) : ℂ) - 1) -
        ∑ j : Fin m, (((WithLp.ofLp w).1 j / r : ℝ) : ℂ) *
          ((𝐞 (r * (WithLp.ofLp ζ).1 j) : ℂ) - 1) := by
  simp only [b1fas_mult, Fintype.sum_option, b1fas_coef, b1fas_vec, real_inner_smul_left,
    b1fas_inner_unit, Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_mul,
    Finset.sum_neg_distrib]
  ring

/-- The quadratic bound in abstract coordinates: `θ = ⟨h,ξ⟩ + sτ`, `‖h‖ < r`, `|s| < r²`. -/
theorem b1fas_norm_mult_core {r : ℝ} (hr : 0 < r) (h ξ : Spatial m) (s τ θ : ℝ)
    (hθ : θ = (∑ j, h j * ξ j) + s * τ) (hh : ‖h‖ < r) (hs : |s| < r ^ 2) :
    ‖((𝐞 θ : ℂ) - 1) - ∑ j : Fin m, ((h j / r : ℝ) : ℂ) * ((𝐞 (r * ξ j) : ℂ) - 1)‖ ≤
      12 * π ^ 2 * (r * ‖ξ‖ + r ^ 2 * |τ|) ^ 2 + 12 * π ^ 2 * (r ^ 2 * ‖ξ‖ ^ 2) +
        2 * π * (r ^ 2 * |τ|) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hip : ∑ j, h j * ξ j = inner ℝ h ξ := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  have hθabs : |θ| ≤ r * ‖ξ‖ + r ^ 2 * |τ| := by
    rw [hθ, hip]
    have h2 : |inner ℝ h ξ| ≤ ‖h‖ * ‖ξ‖ := abs_real_inner_le_norm h ξ
    have h3 : |s * τ| ≤ r ^ 2 * |τ| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hs.le (abs_nonneg _)
    have h4 : ‖h‖ * ‖ξ‖ ≤ r * ‖ξ‖ := mul_le_mul_of_nonneg_right hh.le (norm_nonneg _)
    calc |inner ℝ h ξ + s * τ| ≤ |inner ℝ h ξ| + |s * τ| := abs_add_le _ _
      _ ≤ r * ‖ξ‖ + r ^ 2 * |τ| := by linarith
  have hθsq : θ ^ 2 ≤ (r * ‖ξ‖ + r ^ 2 * |τ|) ^ 2 := by
    rw [← sq_abs θ]
    exact pow_le_pow_left₀ (abs_nonneg θ) hθabs 2
  have hd : ∀ j, |h j / r| ≤ 1 := by
    intro j
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    have := PiLp.norm_apply_le h j
    rw [Real.norm_eq_abs] at this
    linarith
  have hterm' : ∀ j : Fin m, ((h j / r : ℝ) : ℂ) * (((2 * π * (r * ξ j) : ℝ) : ℂ) * Complex.I) =
      ((2 * π * (h j * ξ j) : ℝ) : ℂ) * Complex.I := by
    intro j
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [div_mul_eq_mul_div, div_eq_iff hr0]
    ring
  have hsum : ∑ j : Fin m, ((h j / r : ℝ) : ℂ) * (((2 * π * (r * ξ j) : ℝ) : ℂ) * Complex.I) =
      ((2 * π * ∑ j, h j * ξ j : ℝ) : ℂ) * Complex.I := by
    simp only [hterm']
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, Finset.mul_sum]
  have hT3 : ((2 * π * θ : ℝ) : ℂ) * Complex.I -
      ∑ j : Fin m, ((h j / r : ℝ) : ℂ) * (((2 * π * (r * ξ j) : ℝ) : ℂ) * Complex.I) =
      ((2 * π * (s * τ) : ℝ) : ℂ) * Complex.I := by
    rw [hsum, hθ]
    push_cast
    ring
  have hT1 : ‖(𝐞 θ : ℂ) - 1 - ((2 * π * θ : ℝ) : ℂ) * Complex.I‖ ≤ 12 * π ^ 2 * θ ^ 2 :=
    b1fas_norm_char_sub_le θ
  have hT2 : ‖∑ j : Fin m, ((h j / r : ℝ) : ℂ) * (((𝐞 (r * ξ j) : ℂ) - 1) -
      ((2 * π * (r * ξ j) : ℝ) : ℂ) * Complex.I)‖ ≤ 12 * π ^ 2 * (r ^ 2 * ‖ξ‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j : Fin m, ‖((h j / r : ℝ) : ℂ) * (((𝐞 (r * ξ j) : ℂ) - 1) -
        ((2 * π * (r * ξ j) : ℝ) : ℂ) * Complex.I)‖ ≤ 12 * π ^ 2 * (r ^ 2 * ξ j ^ 2) := by
      intro j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |h j / r| * ‖((𝐞 (r * ξ j) : ℂ) - 1) - ((2 * π * (r * ξ j) : ℝ) : ℂ) * Complex.I‖
          ≤ 1 * (12 * π ^ 2 * (r * ξ j) ^ 2) :=
            mul_le_mul (hd j) (b1fas_norm_char_sub_le (r * ξ j)) (norm_nonneg _) zero_le_one
        _ = 12 * π ^ 2 * (r ^ 2 * ξ j ^ 2) := by ring
    refine (Finset.sum_le_sum fun j _ => hterm j).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hT3n : ‖((2 * π * (s * τ) : ℝ) : ℂ) * Complex.I‖ ≤ 2 * π * (r ^ 2 * |τ|) := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul (2 * π) (s * τ), abs_mul s τ, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs.le (abs_nonneg _))
      (by positivity)
  rw [b1fas_sum_identity _ (((2 * π * θ : ℝ) : ℂ) * Complex.I) _ _
    (fun j => ((2 * π * (r * ξ j) : ℝ) : ℂ) * Complex.I), hT3]
  have htri : ∀ X S T : ℂ, ‖X - S + T‖ ≤ ‖X‖ + ‖S‖ + ‖T‖ := fun X S T =>
    (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  refine (htri _ _ _).trans ?_
  refine (add_le_add (add_le_add hT1 hT2) hT3n).trans ?_
  have := mul_le_mul_of_nonneg_left hθsq (by positivity : (0 : ℝ) ≤ 12 * π ^ 2)
  linarith

/-- The quadratic bound of the multiplier on the testing ball. -/
theorem b1fas_norm_mult_le_quad {r : ℝ} (hr : 0 < r) {w : FourierSpace m}
    (hw : w ∈ coordBall 0 r) (ζ : FourierSpace m) :
    ‖b1fas_mult Finset.univ (b1fas_coef r w) (b1fas_vec r w) ζ‖ ≤
      12 * π ^ 2 * (r * ‖(WithLp.ofLp ζ).1‖ + r ^ 2 * |(WithLp.ofLp ζ).2|) ^ 2 +
        12 * π ^ 2 * (r ^ 2 * ‖(WithLp.ofLp ζ).1‖ ^ 2) +
          2 * π * (r ^ 2 * |(WithLp.ofLp ζ).2|) := by
  obtain ⟨hh, hs⟩ := b1fas_mem_coordBall_zero.1 hw
  rw [b1fas_mult_eq]
  refine b1fas_norm_mult_core hr (WithLp.ofLp w).1 (WithLp.ofLp ζ).1 (WithLp.ofLp w).2
    (WithLp.ofLp ζ).2 (inner ℝ w ζ) ?_ hh hs
  rw [WithLp.prod_inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]

/-- The bounded estimate of the multiplier on the testing ball. -/
theorem b1fas_norm_mult_le_const {r : ℝ} (hr : 0 < r) {w : FourierSpace m}
    (hw : w ∈ coordBall 0 r) (ζ : FourierSpace m) :
    ‖b1fas_mult Finset.univ (b1fas_coef r w) (b1fas_vec r w) ζ‖ ≤ 2 * m + 2 := by
  obtain ⟨hh, -⟩ := b1fas_mem_coordBall_zero.1 hw
  have hd : ∀ j, |(WithLp.ofLp w).1 j / r| ≤ 1 := by
    intro j
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    have := PiLp.norm_apply_le (WithLp.ofLp w).1 j
    rw [Real.norm_eq_abs] at this
    linarith
  rw [b1fas_mult_eq]
  refine (norm_sub_le _ _).trans ?_
  have hsum : ‖∑ j : Fin m, (((WithLp.ofLp w).1 j / r : ℝ) : ℂ) *
      ((𝐞 (r * (WithLp.ofLp ζ).1 j) : ℂ) - 1)‖ ≤ 2 * m := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin m, ‖(((WithLp.ofLp w).1 j / r : ℝ) : ℂ) *
          ((𝐞 (r * (WithLp.ofLp ζ).1 j) : ℂ) - 1)‖
        ≤ ∑ _j : Fin m, (2 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |(WithLp.ofLp w).1 j / r| * ‖(𝐞 (r * (WithLp.ofLp ζ).1 j) : ℂ) - 1‖
              ≤ 1 * 2 := mul_le_mul (hd j) (b1fas_norm_char_sub_one_le _) (norm_nonneg _)
                zero_le_one
            _ = 2 := one_mul 2
      _ = 2 * m := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have h1 := b1fas_norm_char_sub_one_le (inner ℝ w ζ)
  linarith

/-- The multiplier constant `K_m = 38π² + 2m + 2`. -/
def b1fas_K (m : ℕ) : ℝ := 38 * π ^ 2 + 2 * m + 2

theorem b1fas_K_nonneg (m : ℕ) : 0 ≤ b1fas_K m := by
  unfold b1fas_K
  positivity

/-- `|M| ≤ K_m min(1, r² (|ξ|² + |τ|))` on the testing ball. -/
theorem b1fas_norm_mult_le_min {r : ℝ} (hr : 0 < r) {w : FourierSpace m}
    (hw : w ∈ coordBall 0 r) (ζ : FourierSpace m) :
    ‖b1fas_mult Finset.univ (b1fas_coef r w) (b1fas_vec r w) ζ‖ ≤
      b1fas_K m * min 1 (r ^ 2 * (‖(WithLp.ofLp ζ).1‖ ^ 2 + |(WithLp.ofLp ζ).2|)) := by
  set X : ℝ := r * ‖(WithLp.ofLp ζ).1‖ with hX
  set Y : ℝ := r ^ 2 * |(WithLp.ofLp ζ).2| with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hra : r ^ 2 * (‖(WithLp.ofLp ζ).1‖ ^ 2 + |(WithLp.ofLp ζ).2|) = X ^ 2 + Y := by
    rw [hX, hY]
    ring
  rw [hra]
  have hpi : 3 < π := Real.pi_gt_three
  by_cases hc : X ^ 2 + Y ≤ 1
  · rw [min_eq_right hc]
    have hq := b1fas_norm_mult_le_quad hr hw ζ
    have hq' : 12 * π ^ 2 * (r ^ 2 * ‖(WithLp.ofLp ζ).1‖ ^ 2) = 12 * π ^ 2 * X ^ 2 := by
      rw [hX]
      ring
    rw [hq', ← hX, ← hY] at hq
    have hY1 : Y ≤ 1 := by nlinarith
    have hYY : Y ^ 2 ≤ Y := by nlinarith
    have hXY : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by nlinarith [sq_nonneg (X - Y)]
    have hfin : 12 * π ^ 2 * (X + Y) ^ 2 + 12 * π ^ 2 * X ^ 2 + 2 * π * Y ≤
        38 * π ^ 2 * (X ^ 2 + Y) := by
      have e1 : 12 * π ^ 2 * (X + Y) ^ 2 ≤ 12 * π ^ 2 * (2 * X ^ 2 + 2 * Y) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have e2 : 2 * π * Y ≤ 14 * π ^ 2 * Y := by
        have : 2 * π ≤ 14 * π ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hY0
      have e3 : 0 ≤ π ^ 2 * X ^ 2 := by positivity
      nlinarith
    have hK : 38 * π ^ 2 * (X ^ 2 + Y) ≤ b1fas_K m * (X ^ 2 + Y) := by
      unfold b1fas_K
      have : 0 ≤ (2 * (m : ℝ) + 2) * (X ^ 2 + Y) := by positivity
      nlinarith
    linarith
  · rw [not_le] at hc
    rw [min_eq_left hc.le, mul_one]
    have hb := b1fas_norm_mult_le_const hr hw ζ
    unfold b1fas_K
    have : 0 ≤ 38 * π ^ 2 := by positivity
    linarith

theorem b1fas_enorm_mult_sq_le {r : ℝ} (hr : 0 < r) {w : FourierSpace m}
    (hw : w ∈ coordBall 0 r) (ζ : FourierSpace m) :
    ‖b1fas_mult Finset.univ (b1fas_coef r w) (b1fas_vec r w) ζ‖ₑ ^ 2 ≤
      ENNReal.ofReal (b1fas_K m ^ 2 *
        min 1 (r ^ 2 * (‖(WithLp.ofLp ζ).1‖ ^ 2 + |(WithLp.ofLp ζ).2|)) ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← mul_pow]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (b1fas_norm_mult_le_min hr hw ζ) 2)

/-! ### The scale integral -/

/-- `∫_0^∞ r^{-2} min(1, r² a)² dr/r ≤ a`. -/
theorem b1fas_lintegral_scale_le {a : ℝ} (ha : 0 ≤ a) :
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
