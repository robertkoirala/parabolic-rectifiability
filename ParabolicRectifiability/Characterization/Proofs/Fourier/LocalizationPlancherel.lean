import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Critical Sobolev localization: the temporal Sobolev / Plancherel bridge

Part of the proof of `ba1_critical_sobolev_localization_proof`. The energy of
`CriticalSobolevLocalizationStatement` is the Fourier-side
`parabolicFourierEnergy hH = ∫ (|ξ|² + |τ|) |Ĥ|²` of the L² Fourier transform
`Ĥ = 𝓕 (realLp hH)` (mathlib's phase `e^{-2πi⟨x,ζ⟩}`). This file converts both parts of this
energy into physical-space difference quotients, which are then estimated in physical space:

* **translation Plancherel** (`b1loc_lintegral_translate_sub_sq`): for real `H ∈ L²` and every
  `h`, `∫ |H(x + h) - H(x)|² dx = ∫ |e(⟨h,ζ⟩) - 1|² |Ĥ(ζ)|² dζ`, `e(θ) = e^{2πiθ}`;
* **temporal Gagliardo bridge**: with the temporal
  Gagliardo energy `b1loc_timeGagliardo H = ∫_0^∞ s^{-2} ∫ |H(x + s e_t) - H(x)|² dx ds`,
  `8 ∫ |τ| |Ĥ|² ≤ b1loc_timeGagliardo H ≤ (4π² + 4) ∫ |τ| |Ĥ|²`
  (`b1loc_timeFourier_le_timeGagliardo`, `b1loc_timeGagliardo_le_timeFourier`); the two
  inequalities come from `8|τ| ≤ ∫_0^∞ s^{-2} |e(sτ) - 1|² ds ≤ (4π² + 4)|τ|`;
* **spatial difference quotients** (`b1loc_lintegral_inner_sq_fourier_le`): if
  `∫ |H(x + s v) - H(x)|² ≤ s² A` for `0 < s ≤ 1`, then `16 ∫ ⟨v,ζ⟩² |Ĥ|² ≤ A`
  (Jordan's inequality on `|⟨v,ζ⟩| ≤ n + 1`, then monotone convergence in `n`).

Only inequalities are needed, so the exact constant `∫ sin²u/u² du = π` is not
used. The identification of the translated difference uses the testing method of
`FourierAffine.lintegral_enorm_smoothing_sq`: both sides
are tested against real compact smooth functions, the bilinear L² pairing moves the Fourier
transform to the test, and a translation of a test multiplies its inverse transform by a phase.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ContDiff SchwartzMap

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.HalfTimeDerivative

/- The continuity instance `FourierAffine.continuousSMul_fourierSpace`, made local to this
file. -/
attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-! ## Phase factors `e(θ) - 1` -/

theorem b1loc_fourierChar_coe (θ : ℝ) :
    ((𝐞 θ : Circle) : ℂ) = Complex.exp (↑(2 * Real.pi * θ) * Complex.I) :=
  Real.fourierChar_apply θ

theorem b1loc_continuous_fourierChar_coe : Continuous fun θ : ℝ => ((𝐞 θ : Circle) : ℂ) := by
  have h : (fun θ : ℝ => ((𝐞 θ : Circle) : ℂ)) =
      fun θ => Complex.exp (↑(2 * Real.pi * θ) * Complex.I) := funext b1loc_fourierChar_coe
  rw [h]
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)

/-- `|e(θ) - 1| = 2 |sin (π θ)|`. -/
theorem b1loc_norm_fourierChar_sub_one (θ : ℝ) :
    ‖((𝐞 θ : Circle) : ℂ) - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  rw [b1loc_fourierChar_coe, mul_comm (↑(2 * Real.pi * θ) : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two,
    show 2 * Real.pi * θ / 2 = Real.pi * θ by ring]

theorem b1loc_norm_fourierChar_sub_one_le_two (θ : ℝ) : ‖((𝐞 θ : Circle) : ℂ) - 1‖ ≤ 2 := by
  calc ‖((𝐞 θ : Circle) : ℂ) - 1‖ ≤ ‖((𝐞 θ : Circle) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num

/-- `|e(θ) - 1| ≤ 2π |θ|`. -/
theorem b1loc_norm_fourierChar_sub_one_le (θ : ℝ) :
    ‖((𝐞 θ : Circle) : ℂ) - 1‖ ≤ 2 * Real.pi * |θ| := by
  rw [b1loc_fourierChar_coe, mul_comm (↑(2 * Real.pi * θ) : ℂ) Complex.I]
  calc ‖Complex.exp (Complex.I * ↑(2 * Real.pi * θ)) - 1‖ ≤ ‖2 * Real.pi * θ‖ :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |θ| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]

/-- Jordan's inequality: `4 |θ| ≤ |e(θ) - 1|` for `|θ| ≤ 1/2`. -/
theorem b1loc_four_mul_abs_le_norm_fourierChar_sub_one {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    4 * |θ| ≤ ‖((𝐞 θ : Circle) : ℂ) - 1‖ := by
  rw [b1loc_norm_fourierChar_sub_one]
  have hpi := Real.pi_pos
  have h0 : 0 ≤ Real.pi * |θ| := mul_nonneg hpi.le (abs_nonneg θ)
  have h1 : Real.pi * |θ| ≤ Real.pi / 2 := by nlinarith
  have hs := Real.mul_le_sin h0 h1
  have hsin : Real.sin (Real.pi * |θ|) ≤ |Real.sin (Real.pi * θ)| := by
    rcases le_or_gt 0 θ with hθ0 | hθ0
    · rw [abs_of_nonneg hθ0]
      exact le_abs_self _
    · rw [abs_of_neg hθ0, mul_neg, Real.sin_neg]
      exact neg_le_abs _
  have hpi2 : 2 / Real.pi * (Real.pi * |θ|) = 2 * |θ| := by
    rw [← mul_assoc, div_mul_cancel₀ 2 hpi.ne']
  linarith

/-- `s^{-2} |z|²` in real form. -/
theorem b1loc_inv_sq_mul_enorm_sq {s : ℝ} (hs : 0 < s) (z : ℂ) :
    (ENNReal.ofReal s)⁻¹ ^ 2 * ‖z‖ₑ ^ 2 = ENNReal.ofReal ((s⁻¹ * ‖z‖) ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_inv_of_pos hs,
    ← ENNReal.ofReal_pow (inv_nonneg.2 hs.le), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), mul_pow]

/-- `∫_a^∞ s^{-2} ds = a^{-1}`. -/
theorem b1loc_lintegral_Ioi_inv_sq {a : ℝ} (ha : 0 < a) :
    ∫⁻ s in Ioi a, (ENNReal.ofReal s)⁻¹ ^ 2 = ENNReal.ofReal a⁻¹ := by
  have he : (-2 : ℝ) < -1 := by norm_num
  have hi := integrableOn_Ioi_rpow_of_lt he ha
  calc ∫⁻ s in Ioi a, (ENNReal.ofReal s)⁻¹ ^ 2
      = ∫⁻ s in Ioi a, ENNReal.ofReal (s ^ (-2 : ℝ)) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro s hs
        have hs0 : 0 < s := ha.trans hs
        show (ENNReal.ofReal s)⁻¹ ^ 2 = ENNReal.ofReal (s ^ (-2 : ℝ))
        rw [Real.rpow_neg hs0.le, Real.rpow_two, ← inv_pow,
          ENNReal.ofReal_pow (inv_nonneg.2 hs0.le), ENNReal.ofReal_inv_of_pos hs0]
    _ = ENNReal.ofReal (∫ s in Ioi a, s ^ (-2 : ℝ)) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact Real.rpow_nonneg (ha.trans hs).le _
    _ = ENNReal.ofReal a⁻¹ := by
        rw [integral_Ioi_rpow_of_lt he ha, show (-2 : ℝ) + 1 = -1 by norm_num,
          Real.rpow_neg_one]
        congr 1
        ring

/-! ## The one-dimensional temporal weight -/

/-- `8 |τ| ≤ ∫_0^∞ s^{-2} |e(sτ) - 1|² ds`: integrate Jordan's inequality over
`0 < s ≤ (2|τ|)⁻¹`. -/
theorem b1loc_timeWeight_lower (τ : ℝ) :
    ENNReal.ofReal (8 * |τ|) ≤
      ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ₑ ^ 2 := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · simp
  have hτ0 : 0 < |τ| := abs_pos.mpr hτ
  have ha0 : 0 < (2 * |τ|)⁻¹ := by positivity
  have hinv : (2 * |τ|)⁻¹ * (2 * |τ|) = 1 := inv_mul_cancel₀ (by positivity)
  calc ENNReal.ofReal (8 * |τ|)
      = ∫⁻ _ in Ioc (0 : ℝ) (2 * |τ|)⁻¹, ENNReal.ofReal (16 * τ ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [sub_zero, ← sq_abs τ]
        linear_combination (-(8 * |τ|)) * hinv
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) (2 * |τ|)⁻¹,
          (ENNReal.ofReal s)⁻¹ ^ 2 * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ₑ ^ 2 := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro s hs
        have hs0 : 0 < s := hs.1
        have hθ : |s * τ| ≤ 1 / 2 := by
          rw [abs_mul, abs_of_pos hs0]
          calc s * |τ| ≤ (2 * |τ|)⁻¹ * |τ| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg τ)
            _ = 1 / 2 := by linear_combination (1 / 2 : ℝ) * hinv
        have hlow := b1loc_four_mul_abs_le_norm_fourierChar_sub_one hθ
        rw [abs_mul, abs_of_pos hs0] at hlow
        rw [b1loc_inv_sq_mul_enorm_sq hs0]
        apply ENNReal.ofReal_le_ofReal
        have h4 : 4 * |τ| ≤ s⁻¹ * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ := by
          rw [le_inv_mul_iff₀ hs0]
          calc s * (4 * |τ|) = 4 * (s * |τ|) := by ring
            _ ≤ _ := hlow
        calc 16 * τ ^ 2 = (4 * |τ|) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
          _ ≤ (s⁻¹ * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h4 2
    _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self

/-- `∫_0^∞ s^{-2} |e(sτ) - 1|² ds ≤ (4π² + 4) |τ|`: `|e(sτ) - 1| ≤ 2π s|τ|` for `s ≤ |τ|⁻¹`,
and `≤ 2` beyond. -/
theorem b1loc_timeWeight_upper (τ : ℝ) :
    ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ₑ ^ 2 ≤
      ENNReal.ofReal ((4 * Real.pi ^ 2 + 4) * |τ|) := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · simp
  have hτ0 : 0 < |τ| := abs_pos.mpr hτ
  have ha0 : 0 < |τ|⁻¹ := inv_pos.mpr hτ0
  have hinv : |τ|⁻¹ * |τ| = 1 := inv_mul_cancel₀ hτ0.ne'
  have hsub : Ioi (0 : ℝ) ⊆ Ioc 0 |τ|⁻¹ ∪ Ioi |τ|⁻¹ := by
    intro s hs
    by_cases hsa : s ≤ |τ|⁻¹
    · exact Or.inl ⟨hs, hsa⟩
    · exact Or.inr (lt_of_not_ge hsa)
  have h1 : ∫⁻ s in Ioc (0 : ℝ) |τ|⁻¹,
      (ENNReal.ofReal s)⁻¹ ^ 2 * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * Real.pi ^ 2 * |τ|) := by
    calc _ ≤ ∫⁻ _ in Ioc (0 : ℝ) |τ|⁻¹, ENNReal.ofReal (4 * Real.pi ^ 2 * τ ^ 2) := by
          apply setLIntegral_mono' measurableSet_Ioc
          intro s hs
          have hs0 : 0 < s := hs.1
          rw [b1loc_inv_sq_mul_enorm_sq hs0]
          apply ENNReal.ofReal_le_ofReal
          have hup := b1loc_norm_fourierChar_sub_one_le (s * τ)
          rw [abs_mul, abs_of_pos hs0] at hup
          have h4 : s⁻¹ * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ ≤ 2 * Real.pi * |τ| := by
            rw [inv_mul_le_iff₀ hs0]
            calc ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ ≤ 2 * Real.pi * (s * |τ|) := hup
              _ = s * (2 * Real.pi * |τ|) := by ring
          calc (s⁻¹ * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖) ^ 2 ≤ (2 * Real.pi * |τ|) ^ 2 :=
                pow_le_pow_left₀ (by positivity) h4 2
            _ = 4 * Real.pi ^ 2 * τ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
      _ = ENNReal.ofReal (4 * Real.pi ^ 2 * |τ|) := by
          rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [sub_zero, ← sq_abs τ]
          linear_combination (4 * Real.pi ^ 2 * |τ|) * hinv
  have h2 : ∫⁻ s in Ioi |τ|⁻¹,
      (ENNReal.ofReal s)⁻¹ ^ 2 * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * |τ|) := by
    calc _ ≤ ∫⁻ s in Ioi |τ|⁻¹, ENNReal.ofReal 4 * (ENNReal.ofReal s)⁻¹ ^ 2 := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro s hs
          rw [mul_comm (ENNReal.ofReal 4)]
          gcongr
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          have h2 := b1loc_norm_fourierChar_sub_one_le_two (s * τ)
          nlinarith [norm_nonneg (((𝐞 (s * τ) : Circle) : ℂ) - 1)]
      _ = ENNReal.ofReal (4 * |τ|) := by
          rw [lintegral_const_mul _ (by fun_prop), b1loc_lintegral_Ioi_inv_sq ha0, inv_inv,
            ← ENNReal.ofReal_mul (by norm_num)]
  calc _ ≤ ∫⁻ s in Ioc 0 |τ|⁻¹ ∪ Ioi |τ|⁻¹,
        (ENNReal.ofReal s)⁻¹ ^ 2 * ‖((𝐞 (s * τ) : Circle) : ℂ) - 1‖ₑ ^ 2 :=
        lintegral_mono_set hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (4 * Real.pi ^ 2 * |τ|) + ENNReal.ofReal (4 * |τ|) := add_le_add h1 h2
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ## Bilinear Parseval against Schwartz tests and translation Plancherel -/

/-- Bilinear Parseval against a Schwartz test, for the inverse transform. -/
theorem b1loc_integral_fourierInv_mul (f : Lp ℂ 2 (volume : Measure (FourierSpace m)))
    (T : 𝓢(FourierSpace m, ℂ)) :
    ∫ x, (𝓕⁻ f : Lp ℂ 2 (volume : Measure (FourierSpace m))) x * T x =
      ∫ ζ, f ζ * (𝓕⁻ T) ζ := by
  have h1 : ∫ x, (𝓕⁻ f : Lp ℂ 2 (volume : Measure (FourierSpace m))) x * T x =
      l2Pairing m (𝓕⁻ f) (T.toLp 2 volume) := by
    rw [l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [T.coeFn_toLp 2 volume] with x hx
    rw [hx]
  rw [h1, l2Pairing_fourierInv_left, SchwartzMap.toLp_fourierInv_eq, l2Pairing_apply]
  apply integral_congr_ae
  filter_upwards [(𝓕⁻ T).coeFn_toLp 2 volume] with ζ hζ
  rw [hζ]

/-- Bilinear Parseval against a Schwartz test. -/
theorem b1loc_integral_mul_schwartz (f : Lp ℂ 2 (volume : Measure (FourierSpace m)))
    (T : 𝓢(FourierSpace m, ℂ)) :
    ∫ x, f x * T x =
      ∫ ζ, (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T) ζ := by
  have hFF : 𝓕⁻ (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) = f :=
    (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm_apply_apply f
  have h := b1loc_integral_fourierInv_mul (𝓕 f : Lp ℂ 2 (volume : Measure (FourierSpace m))) T
  rwa [hFF] at h

/-- A translation of the function multiplies its inverse transform by a phase. -/
theorem b1loc_fourierInv_comp_add_neg (φ : FourierSpace m → ℂ) (h w : FourierSpace m) :
    𝓕⁻ (fun x => φ (x + -h)) w = ((𝐞 (inner ℝ h w) : Circle) : ℂ) * 𝓕⁻ φ w := by
  have hshift := integral_add_right_eq_self (μ := (volume : Measure (FourierSpace m)))
    (fun x => ((𝐞 (inner ℝ x w) : Circle) : ℂ) * φ (x + -h)) h
  simp only [add_neg_cancel_right] at hshift
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← hshift, ← integral_const_mul]
  congr 1
  funext x
  rw [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-- **Translation Plancherel.** For real `H ∈ L²(ℝ^m × ℝ)` and every `h`,
`∫ |H(x + h) - H(x)|² dx = ∫ |e(⟨h,ζ⟩) - 1|² |Ĥ(ζ)|² dζ` (extended nonnegative integrals). -/
theorem b1loc_lintegral_translate_sub_sq {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (h : FourierSpace m) :
    ∫⁻ x, ‖H (x + h) - H x‖ₑ ^ 2 =
      ∫⁻ ζ, ‖((𝐞 (inner ℝ h ζ) : Circle) : ℂ) - 1‖ₑ ^ 2 *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  have hMc : Continuous fun ζ : FourierSpace m => ((𝐞 (inner ℝ h ζ) : Circle) : ℂ) - 1 :=
    (b1loc_continuous_fourierChar_coe.comp (continuous_const.inner continuous_id)).sub
      continuous_const
  have hGm : MemLp (fun ζ => (((𝐞 (inner ℝ h ζ) : Circle) : ℂ) - 1) *
      (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ) 2 volume :=
    (Lp.memLp (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m)))).of_le_mul (c := 2)
      (hMc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun ζ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (b1loc_norm_fourierChar_sub_one_le_two _)
          (norm_nonneg _))
  have hT : MemLp (fun x => H (x + h)) 2 volume :=
    hH.comp_measurePreserving (measurePreserving_add_right volume h)
  have hD : MemLp (fun x => H (x + h) - H x) 2 volume := hT.sub hH
  -- Pairing of a real L² function with a Schwartz test.
  have hP : ∀ (G : FourierSpace m → ℝ) (hG : MemLp G 2 volume) (T : 𝓢(FourierSpace m, ℂ)),
      ∫ x, (G x : ℂ) * T x =
        ∫ ζ, (𝓕 (realLp hG) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T) ζ := by
    intro G hG T
    rw [← b1loc_integral_mul_schwartz]
    apply integral_congr_ae
    filter_upwards [coeFn_realLp hG] with x hx
    rw [hx]
  have hint : ∀ (G : FourierSpace m → ℝ), MemLp G 2 volume → ∀ T : 𝓢(FourierSpace m, ℂ),
      Integrable (fun x => (G x : ℂ) * T x) volume := fun G hG T =>
    (hG.ofReal (K := ℂ)).integrable_mul (T.memLp 2 volume)
  have hintF : ∀ T : 𝓢(FourierSpace m, ℂ), Integrable (fun ζ =>
      (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T) ζ) volume :=
    fun T => (Lp.memLp _).integrable_mul ((𝓕⁻ T).memLp 2 volume)
  -- Identification of the inverse transform of the multiplied transform.
  have hid : ∀ᵐ x ∂volume,
      (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x =
        ((H (x + h) - H x : ℝ) : ℂ) := by
    apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
      ((hD.ofReal (K := ℂ)).locallyIntegrable (by norm_num))
    intro g hg hgc
    simp only [Complex.real_smul]
    have hg' : ContDiff ℝ ∞ (fun x => g (x + -h)) := hg.comp (contDiff_id.add contDiff_const)
    have hgc' : HasCompactSupport (fun x => g (x + -h)) :=
      hgc.comp_homeomorph (Homeomorph.addRight (-h))
    set T₀ := realCompactTest g hg hgc with hT₀
    set T₁ := realCompactTest (fun x => g (x + -h)) hg' hgc' with hT₁
    have hFT : ∀ ζ, (𝓕⁻ T₁) ζ = ((𝐞 (inner ℝ h ζ) : Circle) : ℂ) * (𝓕⁻ T₀) ζ := by
      intro ζ
      have e1 : (⇑T₁ : FourierSpace m → ℂ) = fun x => T₀ (x + -h) := by
        funext x
        simp only [hT₁, hT₀, realCompactTest_apply]
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, e1,
        b1loc_fourierInv_comp_add_neg]
    have hL : ∫ x, (g x : ℂ) * (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x =
        ∫ ζ, (((𝐞 (inner ℝ h ζ) : Circle) : ℂ) - 1) *
          (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T₀) ζ := by
      calc _ = ∫ x, (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x * T₀ x := by
            congr 1
            funext x
            rw [hT₀, realCompactTest_apply, mul_comm]
        _ = ∫ ζ, (hGm.toLp _ : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T₀) ζ :=
            b1loc_integral_fourierInv_mul _ T₀
        _ = _ := by
            apply integral_congr_ae
            filter_upwards [hGm.coeFn_toLp] with ζ hζ
            rw [hζ]
    have hR : ∫ x, (g x : ℂ) * ((H (x + h) - H x : ℝ) : ℂ) =
        ∫ ζ, (((𝐞 (inner ℝ h ζ) : Circle) : ℂ) - 1) *
          (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T₀) ζ := by
      have hsplit : ∫ x, (g x : ℂ) * ((H (x + h) - H x : ℝ) : ℂ) =
          (∫ x, (H (x + h) : ℂ) * T₀ x) - ∫ x, (H x : ℂ) * T₀ x := by
        calc _ = ∫ x, ((H (x + h) : ℂ) * T₀ x - (H x : ℂ) * T₀ x) := by
              congr 1
              funext x
              rw [hT₀, realCompactTest_apply]
              push_cast
              ring
          _ = _ := integral_sub (hint _ hT T₀) (hint _ hH T₀)
      have hshift : ∫ x, (H (x + h) : ℂ) * T₀ x = ∫ x, (H x : ℂ) * T₁ x := by
        have hs := integral_add_right_eq_self (μ := (volume : Measure (FourierSpace m)))
          (fun y => (H y : ℂ) * T₁ y) h
        rw [← hs]
        congr 1
        funext x
        simp only [hT₁, hT₀, realCompactTest_apply, add_neg_cancel_right]
      rw [hsplit, hshift, hP H hH T₁, hP H hH T₀, ← integral_sub (hintF T₁) (hintF T₀)]
      congr 1
      funext ζ
      rw [hFT]
      ring
    exact hL.trans hR.symm
  -- Plancherel.
  have hn : ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ =
      ‖hGm.toLp _‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact congrArg _ ((Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.nnnorm_map _)
  calc ∫⁻ x, ‖H (x + h) - H x‖ₑ ^ 2
      = ∫⁻ x, ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [hid] with x hx
        rw [hx, FourierAffine.enorm_complex_ofReal]
    _ = ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ ^ 2 := by
        rw [FourierAffine.lintegral_enorm_sq_eq (Lp.aestronglyMeasurable _), Lp.enorm_def]
    _ = ‖hGm.toLp _‖ₑ ^ 2 := by rw [hn]
    _ = ∫⁻ ζ, ‖(((𝐞 (inner ℝ h ζ) : Circle) : ℂ) - 1) *
          (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
        rw [Lp.enorm_def, eLpNorm_congr_ae hGm.coeFn_toLp,
          ← FourierAffine.lintegral_enorm_sq_eq hGm.aestronglyMeasurable]
    _ = _ := by simp only [enorm_mul, mul_pow]

/-! ## The temporal Gagliardo energy -/

/-- The temporal Gagliardo energy `∫_0^∞ s^{-2} ∫ |H(x + s e_t) - H(x)|² dx ds ∈ [0,∞]`
(the half `s > 0` of the symmetric energy), `e_t = timeVector m`. -/
def b1loc_timeGagliardo (H : FourierSpace m → ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 *
    ∫⁻ x, ‖H (x + s • timeVector m) - H x‖ₑ ^ 2

theorem b1loc_inner_smul_timeVector (s : ℝ) (ζ : FourierSpace m) :
    inner ℝ (s • timeVector m) ζ = s * (WithLp.ofLp ζ).2 := by
  rw [real_inner_smul_left, real_inner_comm, inner_timeVector, timeCoordinate_apply]

theorem b1loc_continuous_phase_time : Continuous fun p : ℝ × FourierSpace m =>
    ((𝐞 (p.1 * (WithLp.ofLp p.2).2) : Circle) : ℂ) - 1 :=
  (b1loc_continuous_fourierChar_coe.comp (continuous_fst.mul
    ((continuous_snd.comp (WithLp.prod_continuous_ofLp _ _ _)).comp continuous_snd))).sub
      continuous_const

theorem b1loc_measurable_timeIntegrand {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    Measurable (Function.uncurry fun (s : ℝ) (ζ : FourierSpace m) =>
      (ENNReal.ofReal s)⁻¹ ^ 2 * (‖((𝐞 (s * (WithLp.ofLp ζ).2) : Circle) : ℂ) - 1‖ₑ ^ 2 *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2)) := by
  have h1 : Measurable fun p : ℝ × FourierSpace m => (ENNReal.ofReal p.1)⁻¹ ^ 2 :=
    ((ENNReal.measurable_ofReal.comp measurable_fst).inv).pow_const 2
  have h3 : Measurable fun p : ℝ × FourierSpace m =>
      ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) p.2‖ₑ ^ 2 :=
    ((Lp.stronglyMeasurable _).measurable.enorm.pow_const 2).comp measurable_snd
  exact h1.mul ((b1loc_continuous_phase_time.measurable.enorm.pow_const 2).mul h3)

/-- The temporal Gagliardo energy on the Fourier side (translation Plancherel and Tonelli). -/
theorem b1loc_timeGagliardo_eq {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    b1loc_timeGagliardo H =
      ∫⁻ ζ, (∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 *
          ‖((𝐞 (s * (WithLp.ofLp ζ).2) : Circle) : ℂ) - 1‖ₑ ^ 2) *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  have hsec : ∀ s : ℝ, Measurable fun ζ : FourierSpace m =>
      ‖((𝐞 (s * (WithLp.ofLp ζ).2) : Circle) : ℂ) - 1‖ₑ ^ 2 *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := fun s =>
    ((b1loc_continuous_phase_time.comp (continuous_const.prodMk continuous_id)).measurable.enorm.pow_const
      2).mul ((Lp.stronglyMeasurable _).measurable.enorm.pow_const 2)
  have hsec' : ∀ ζ : FourierSpace m, Measurable fun s : ℝ =>
      (ENNReal.ofReal s)⁻¹ ^ 2 * ‖((𝐞 (s * (WithLp.ofLp ζ).2) : Circle) : ℂ) - 1‖ₑ ^ 2 :=
    fun ζ => (ENNReal.measurable_ofReal.inv.pow_const 2).mul
      ((b1loc_continuous_phase_time.comp (continuous_id.prodMk continuous_const)).measurable.enorm.pow_const 2)
  unfold b1loc_timeGagliardo
  calc ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 *
        ∫⁻ x, ‖H (x + s • timeVector m) - H x‖ₑ ^ 2
      = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ ζ, (ENNReal.ofReal s)⁻¹ ^ 2 *
          (‖((𝐞 (s * (WithLp.ofLp ζ).2) : Circle) : ℂ) - 1‖ₑ ^ 2 *
            ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) := by
        apply lintegral_congr
        intro s
        rw [b1loc_lintegral_translate_sub_sq hH]
        simp_rw [b1loc_inner_smul_timeVector]
        rw [lintegral_const_mul _ (hsec s)]
    _ = ∫⁻ ζ, ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal s)⁻¹ ^ 2 *
          (‖((𝐞 (s * (WithLp.ofLp ζ).2) : Circle) : ℂ) - 1‖ₑ ^ 2 *
            ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) :=
        lintegral_lintegral_swap (b1loc_measurable_timeIntegrand hH).aemeasurable
    _ = _ := by
        apply lintegral_congr
        intro ζ
        simp_rw [← mul_assoc]
        rw [lintegral_mul_const _ (hsec' ζ)]

/-- **Temporal bridge, lower form.** `8 ∫ |τ| |Ĥ|² ≤ ∫_0^∞ s^{-2} ‖H(· + s e_t) - H‖₂² ds`. -/
theorem b1loc_timeFourier_le_timeGagliardo {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    ENNReal.ofReal 8 * ∫⁻ ζ, ENNReal.ofReal |(WithLp.ofLp ζ).2| *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 ≤
      b1loc_timeGagliardo H := by
  rw [b1loc_timeGagliardo_eq hH, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ζ => ?_
  dsimp only
  calc ENNReal.ofReal 8 * (ENNReal.ofReal |(WithLp.ofLp ζ).2| *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2)
      = ENNReal.ofReal (8 * |(WithLp.ofLp ζ).2|) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ _ := by
        gcongr
        exact b1loc_timeWeight_lower _

/-- **Temporal bridge, upper form.** `∫_0^∞ s^{-2} ‖H(· + s e_t) - H‖₂² ds ≤ (4π² + 4) ∫ |τ| |Ĥ|²`. -/
theorem b1loc_timeGagliardo_le_timeFourier {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    b1loc_timeGagliardo H ≤
      ENNReal.ofReal (4 * Real.pi ^ 2 + 4) * ∫⁻ ζ, ENNReal.ofReal |(WithLp.ofLp ζ).2| *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  rw [b1loc_timeGagliardo_eq hH, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ζ => ?_
  dsimp only
  calc _ ≤ ENNReal.ofReal ((4 * Real.pi ^ 2 + 4) * |(WithLp.ofLp ζ).2|) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
        gcongr
        exact b1loc_timeWeight_upper _
    _ = ENNReal.ofReal (4 * Real.pi ^ 2 + 4) * (ENNReal.ofReal |(WithLp.ofLp ζ).2| *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-! ## Spatial difference quotients -/

/-- **Difference quotients control a directional Fourier energy.** If
`∫ |H(x + s v) - H(x)|² ≤ s² A` for `0 < s ≤ 1`, then `16 ∫ ⟨v,ζ⟩² |Ĥ|² ≤ A`. -/
theorem b1loc_lintegral_inner_sq_fourier_le {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (v : FourierSpace m) (A : ℝ≥0∞)
    (hA : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∫⁻ x, ‖H (x + s • v) - H x‖ₑ ^ 2 ≤ ENNReal.ofReal (s ^ 2) * A) :
    ENNReal.ofReal 16 * ∫⁻ ζ, ENNReal.ofReal (inner ℝ v ζ ^ 2) *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 ≤ A := by
  have hcv : Continuous fun ζ : FourierSpace m => inner ℝ v ζ :=
    continuous_const.inner continuous_id
  have hFm : Measurable fun ζ : FourierSpace m => ENNReal.ofReal (inner ℝ v ζ ^ 2) *
      ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 :=
    (hcv.pow 2).measurable.ennreal_ofReal.mul
      ((Lp.stronglyMeasurable _).measurable.enorm.pow_const 2)
  have hEm : ∀ n : ℕ, MeasurableSet {ζ : FourierSpace m | |inner ℝ v ζ| ≤ (n : ℝ) + 1} :=
    fun n => (isClosed_le (continuous_abs.comp hcv) continuous_const).measurableSet
  have hstep : ∀ n : ℕ, ENNReal.ofReal 16 *
      ∫⁻ ζ, {ζ : FourierSpace m | |inner ℝ v ζ| ≤ (n : ℝ) + 1}.indicator (fun ζ =>
        ENNReal.ofReal (inner ℝ v ζ ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) ζ ≤ A := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hs0 : 0 < (2 * ((n : ℝ) + 1))⁻¹ := by positivity
    have hs1 : (2 * ((n : ℝ) + 1))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    set s : ℝ := (2 * ((n : ℝ) + 1))⁻¹ with hs
    have hinv : s * (2 * ((n : ℝ) + 1)) = 1 := inv_mul_cancel₀ (by positivity)
    have hpt : ∀ ζ : FourierSpace m, ENNReal.ofReal (16 * s ^ 2) *
        {ζ : FourierSpace m | |inner ℝ v ζ| ≤ (n : ℝ) + 1}.indicator (fun ζ =>
          ENNReal.ofReal (inner ℝ v ζ ^ 2) *
            ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) ζ ≤
        ‖((𝐞 (inner ℝ (s • v) ζ) : Circle) : ℂ) - 1‖ₑ ^ 2 *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
      intro ζ
      by_cases hζ : ζ ∈ {ζ : FourierSpace m | |inner ℝ v ζ| ≤ (n : ℝ) + 1}
      · rw [indicator_of_mem hζ, real_inner_smul_left, ← mul_assoc]
        gcongr
        have hζ' : |inner ℝ v ζ| ≤ (n : ℝ) + 1 := hζ
        have hθ : |s * inner ℝ v ζ| ≤ 1 / 2 := by
          rw [abs_mul, abs_of_pos hs0]
          calc s * |inner ℝ v ζ| ≤ s * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left hζ' hs0.le
            _ = 1 / 2 := by linear_combination (1 / 2 : ℝ) * hinv
        have hlow := b1loc_four_mul_abs_le_norm_fourierChar_sub_one hθ
        rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        calc 16 * s ^ 2 * inner ℝ v ζ ^ 2 = (4 * |s * inner ℝ v ζ|) ^ 2 := by
              rw [mul_pow, sq_abs, mul_pow]
              ring
          _ ≤ _ := pow_le_pow_left₀ (by positivity) hlow 2
      · rw [indicator_of_notMem hζ, mul_zero]
        exact zero_le
    have hint := lintegral_mono (μ := (volume : Measure (FourierSpace m))) hpt
    rw [lintegral_const_mul _ (hFm.indicator (hEm n)),
      ← b1loc_lintegral_translate_sub_sq hH] at hint
    have hle := hint.trans (hA s hs0 hs1)
    have hs2 : ENNReal.ofReal (16 * s ^ 2) = ENNReal.ofReal (s ^ 2) * ENNReal.ofReal 16 := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
    rw [hs2, mul_assoc] at hle
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne'
      ENNReal.ofReal_ne_top).1 hle
  have hmono : Monotone fun n : ℕ =>
      {ζ : FourierSpace m | |inner ℝ v ζ| ≤ (n : ℝ) + 1}.indicator (fun ζ =>
        ENNReal.ofReal (inner ℝ v ζ ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) := by
    intro a b hab
    apply indicator_le_indicator_of_subset _ (fun _ => zero_le)
    intro ζ hζ
    have hζ' : |inner ℝ v ζ| ≤ (a : ℝ) + 1 := hζ
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    show |inner ℝ v ζ| ≤ (b : ℝ) + 1
    linarith
  have hsup : ∀ ζ : FourierSpace m,
      ⨆ n : ℕ, {ζ : FourierSpace m | |inner ℝ v ζ| ≤ (n : ℝ) + 1}.indicator (fun ζ =>
        ENNReal.ofReal (inner ℝ v ζ ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) ζ =
      ENNReal.ofReal (inner ℝ v ζ ^ 2) *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
    intro ζ
    apply le_antisymm (iSup_le fun n => indicator_le_self _ _ ζ)
    refine le_iSup_of_le ⌈|inner ℝ v ζ|⌉₊ ?_
    rw [indicator_of_mem]
    show |inner ℝ v ζ| ≤ (⌈|inner ℝ v ζ|⌉₊ : ℝ) + 1
    linarith [Nat.le_ceil |inner ℝ v ζ|]
  have hlim : ∫⁻ ζ, ENNReal.ofReal (inner ℝ v ζ ^ 2) *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 =
      ⨆ n : ℕ, ∫⁻ ζ, {ζ : FourierSpace m | |inner ℝ v ζ| ≤ (n : ℝ) + 1}.indicator (fun ζ =>
        ENNReal.ofReal (inner ℝ v ζ ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) ζ := by
    rw [← lintegral_iSup (fun n => hFm.indicator (hEm n)) hmono]
    exact lintegral_congr fun ζ => (hsup ζ).symm
  rw [hlim, ENNReal.mul_iSup]
  exact iSup_le hstep

end ParabolicRectifiability.Characterization
