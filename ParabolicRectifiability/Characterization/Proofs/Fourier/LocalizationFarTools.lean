import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationSplit

/-! # Critical Sobolev localization: tools for the far part

For the far estimate in the proof of `ba1_critical_sobolev_localization_proof`. Notation:
`K = I - η * I` (fixed cutoff), `w∞ = 1_{Ωᶜ} (g - c)` (`b1loc_farPart`), `V∞ = K *_t w∞`,
`x₀ = Ψ⁻¹ p₀`, `B₇ = B(x₀,7)`.

* **support** (`b1loc_farPart_shift_eq_zero`): for `x ∈ B₇` and `|r| ≤ 93`, `x - r e_t ∈ Ω`, so
  `w∞(x - r e_t) = 0`;
* **kernel tails** (`b1loc_kernel_far_bounds`): for `|r| ≥ 93`, `0 ≤ s ≤ 1`:
  `|K(r)|, |K(r + s)| ≤ D |r|^{-N}` and `|K(r + s) - K(r)| ≤ D |r|^{-N} s` (tails of
  `b1loc_kernel_adapter`, mean value theorem on `[r, r + s] ⊆ {|t| ≥ 92}`);
* **majorant** `W(x) = ∫ ω(r) |w∞(x - r e_t)| dr`, `ω(r) = D |r|^{-(m+8)} 1_{|r| ≥ 93}`
  (`b1loc_farMajorant`): `|V∞(x)| ≤ W(x)` and, for a.e. `x ∈ B₇` and `0 < s ≤ 1`,
  `|V∞(x + s e_t) - V∞(x)| ≤ s W(x)` (substitution `r ↦ r + s`); hence
  `LGag(V∞) + ∫_{B₇} |V∞|² ≤ 2 ∫_{B₇} W²` (`b1loc_far_energy_le_W`);
* **`L²` bound of the majorant** (`b1loc_far_W_L2`): Cauchy–Schwarz in `r` with
  `ω = |r|^{-1} 1 · D |r|^{-(m+7)} 1`, Tonelli, translation invariance and the concentric BMO
  growth on `P(p₀, 10 + |r|) ⊇ Ψ(B₇ - r e_t)` give
  `∫_{B₇} W² ≤ A · (D² C_BMO V_m 2^{m+4} B²) · A`, `A = ∫_{|r| ≥ 93} |r|^{-2} dr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-! ## Geometry of time translates of `B(x₀,7)` -/

/-- For `‖x - x₀‖ < 7`, `7 ≤ R` and `7 + |r| ≤ R²`, `Ψ(x - r e_t) ∈ P(p₀,R)`. -/
theorem b1loc_shift_mem_ball (p₀ : Space m) {x : FourierSpace m}
    (hx : ‖x - (fourierToParabolic m).symm p₀‖ < 7) {r R : ℝ} (hR : 7 ≤ R)
    (hrR : 7 + |r| ≤ R ^ 2) :
    fourierToParabolic m (x - r • timeVector m) ∈ Metric.ball p₀ R := by
  have hp : fourierToParabolic m ((fourierToParabolic m).symm p₀) = p₀ :=
    Homeomorph.apply_symm_apply _ _
  rw [Metric.mem_ball, ← hp, b1loc_dist_fourierToParabolic]
  have hz : x - r • timeVector m - (fourierToParabolic m).symm p₀ =
      (x - (fourierToParabolic m).symm p₀) - r • timeVector m := by abel
  rw [hz]
  simp only [coordinates_sub_timeVector]
  have h1 := b1loc_norm_fst_le (x - (fourierToParabolic m).symm p₀)
  have h2 := b1loc_abs_snd_le (x - (fourierToParabolic m).symm p₀)
  refine max_lt (by linarith) ?_
  rw [Real.sqrt_lt' (by linarith)]
  have h3 := abs_add_le (WithLp.ofLp (x - (fourierToParabolic m).symm p₀)).2 (-r)
  rw [← sub_eq_add_neg, abs_neg] at h3
  linarith

/-- The far part vanishes at `x - r e_t` for `‖x - x₀‖ < 7` and `|r| ≤ 93`. -/
theorem b1loc_farPart_shift_eq_zero (f : Space m → ℝ) (p₀ : Space m) {x : FourierSpace m}
    (hx : ‖x - (fourierToParabolic m).symm p₀‖ < 7) {r : ℝ} (hr : |r| ≤ 93) :
    b1loc_farPart m f p₀ (x - r • timeVector m) = 0 := by
  have h100 : (10 : ℝ) ^ 2 = 100 := by norm_num
  have hmem : fourierToParabolic m (x - r • timeVector m) ∈ Metric.ball p₀ 10 :=
    b1loc_shift_mem_ball p₀ hx (by norm_num) (by rw [h100]; linarith)
  have hmem' : x - r • timeVector m ∈ b1loc_nearSet m p₀ := hmem
  exact indicator_of_notMem
    (fun h : x - r • timeVector m ∈ (b1loc_nearSet m p₀)ᶜ => h hmem') _

/-! ## Kernel bounds on the far region -/

/-- For `|r| ≥ 93` and `0 ≤ s ≤ 1`: `|K(r)|, |K(r + s)| ≤ D |r|^{-N}` and
`|K(r + s) - K(r)| ≤ D |r|^{-N} s`. -/
theorem b1loc_kernel_far_bounds (hK : HighPassKernelStatement) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℝ, 93 ≤ |r| → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |fhp_highPassKernel b1loc_cutoff r| ≤ D * (|r| ^ N)⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s)| ≤ D * (|r| ^ N)⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s) - fhp_highPassKernel b1loc_cutoff r| ≤
        D * (|r| ^ N)⁻¹ * s := by
  obtain ⟨-, hC1, -, htail, -⟩ := b1loc_kernel_adapter hK b1loc_cutoff b1loc_cutoff_admissible
  obtain ⟨C, hC⟩ := htail N
  have hz : ∀ t : ℝ, |t| ^ (-(N : ℤ)) = (|t| ^ N)⁻¹ := fun t => by
    rw [zpow_neg, zpow_natCast]
  have hK0 : ∀ t : ℝ, 1 ≤ |t| →
      |fhp_highPassKernel b1loc_cutoff t| ≤ C * (|t| ^ N)⁻¹ := by
    intro t ht
    have h := hC t ht
    rw [hz] at h
    linarith [abs_nonneg (deriv (fhp_highPassKernel b1loc_cutoff) t)]
  have hK1 : ∀ t : ℝ, 1 ≤ |t| →
      |deriv (fhp_highPassKernel b1loc_cutoff) t| ≤ C * (|t| ^ N)⁻¹ := by
    intro t ht
    have h := hC t ht
    rw [hz] at h
    linarith [abs_nonneg (fhp_highPassKernel b1loc_cutoff t)]
  have hC0 : 0 ≤ C := by
    have h := hK0 1 (by norm_num)
    rw [abs_one, one_pow, inv_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  refine ⟨2 ^ N * C, mul_nonneg (by positivity) hC0, fun r hr s hs0 hs1 => ?_⟩
  have hhalf : ∀ y : ℝ, |r| - 1 ≤ |y| → (|y| ^ N)⁻¹ ≤ 2 ^ N * (|r| ^ N)⁻¹ := by
    intro y hy
    have hpos : 0 < |r| / 2 := by linarith
    have hy2 : |r| / 2 ≤ |y| := by linarith
    calc (|y| ^ N)⁻¹ ≤ ((|r| / 2) ^ N)⁻¹ :=
          inv_anti₀ (pow_pos hpos N) (pow_le_pow_left₀ hpos.le hy2 N)
      _ = 2 ^ N * (|r| ^ N)⁻¹ := by
          rw [div_pow, inv_div, div_eq_mul_inv]
  have hseg : ∀ y ∈ Icc r (r + s), |r| - 1 ≤ |y| := by
    intro y hy
    have h := abs_sub_abs_le_abs_sub r y
    have e : |r - y| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    linarith
  have hrs : |r| - 1 ≤ |r + s| :=
    hseg (r + s) (right_mem_Icc.2 (by linarith))
  have hCr : 0 ≤ C * (|r| ^ N)⁻¹ := mul_nonneg hC0 (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · calc |fhp_highPassKernel b1loc_cutoff r| ≤ C * (|r| ^ N)⁻¹ := hK0 r (by linarith)
      _ ≤ 2 ^ N * C * (|r| ^ N)⁻¹ := by nlinarith
  · calc |fhp_highPassKernel b1loc_cutoff (r + s)| ≤ C * (|r + s| ^ N)⁻¹ :=
          hK0 _ (by linarith)
      _ ≤ C * (2 ^ N * (|r| ^ N)⁻¹) := mul_le_mul_of_nonneg_left (hhalf _ hrs) hC0
      _ = 2 ^ N * C * (|r| ^ N)⁻¹ := by ring
  · have hb : ∀ y ∈ Icc r (r + s),
        ‖deriv (fhp_highPassKernel b1loc_cutoff) y‖ ≤ 2 ^ N * C * (|r| ^ N)⁻¹ := by
      intro y hy
      have hy' := hseg y hy
      rw [Real.norm_eq_abs]
      calc |deriv (fhp_highPassKernel b1loc_cutoff) y| ≤ C * (|y| ^ N)⁻¹ :=
            hK1 y (by linarith)
        _ ≤ C * (2 ^ N * (|r| ^ N)⁻¹) := mul_le_mul_of_nonneg_left (hhalf y hy') hC0
        _ = 2 ^ N * C * (|r| ^ N)⁻¹ := by ring
    have hd : ∀ y ∈ Icc r (r + s),
        DifferentiableAt ℝ (fhp_highPassKernel b1loc_cutoff) y := by
      intro y hy
      have hy' := hseg y hy
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, abs_zero] at hy'
        linarith
      exact (hC1.differentiableOn one_ne_zero).differentiableAt
        (isOpen_compl_singleton.mem_nhds hy0)
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc r (r + s))
      (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hs0] at hmvt
    exact hmvt

/-! ## Weights -/

/-- `b(r) = |r|^{-1} 1_{|r| ≥ 93}`. -/
def b1loc_farB (r : ℝ) : ℝ := if 93 ≤ |r| then |r|⁻¹ else 0

/-- `c(r) = D |r|^{-(m+7)} 1_{|r| ≥ 93}`. -/
def b1loc_farC (D : ℝ) (m : ℕ) (r : ℝ) : ℝ := if 93 ≤ |r| then D * (|r| ^ (m + 7))⁻¹ else 0

/-- `a(r) = |r|^{-2} 1_{|r| ≥ 93}`. -/
def b1loc_farA (r : ℝ) : ℝ := if 93 ≤ |r| then (|r| ^ 2)⁻¹ else 0

/-- `ω(r) = D |r|^{-(m+8)} 1_{|r| ≥ 93}`. -/
def b1loc_farW (D : ℝ) (m : ℕ) (r : ℝ) : ℝ := if 93 ≤ |r| then D * (|r| ^ (m + 8))⁻¹ else 0

theorem b1loc_measurableSet_far : MeasurableSet {r : ℝ | 93 ≤ |r|} :=
  measurableSet_le measurable_const continuous_abs.measurable

theorem b1loc_measurable_farB : Measurable b1loc_farB := by
  show Measurable (fun r : ℝ => if 93 ≤ |r| then |r|⁻¹ else 0)
  exact Measurable.ite b1loc_measurableSet_far continuous_abs.measurable.inv measurable_const

theorem b1loc_measurable_farC (D : ℝ) (m : ℕ) : Measurable (b1loc_farC D m) := by
  show Measurable (fun r : ℝ => if 93 ≤ |r| then D * (|r| ^ (m + 7))⁻¹ else 0)
  exact Measurable.ite b1loc_measurableSet_far
    (measurable_const.mul (continuous_abs.measurable.pow_const _).inv) measurable_const

theorem b1loc_farB_nonneg (r : ℝ) : 0 ≤ b1loc_farB r := by
  unfold b1loc_farB
  split_ifs
  · exact inv_nonneg.2 (abs_nonneg r)
  · exact le_rfl

theorem b1loc_farC_nonneg {D : ℝ} (hD : 0 ≤ D) (m : ℕ) (r : ℝ) : 0 ≤ b1loc_farC D m r := by
  unfold b1loc_farC
  split_ifs
  · exact mul_nonneg hD (inv_nonneg.2 (pow_nonneg (abs_nonneg r) _))
  · exact le_rfl

theorem b1loc_farA_nonneg (r : ℝ) : 0 ≤ b1loc_farA r := by
  unfold b1loc_farA
  split_ifs
  · exact inv_nonneg.2 (pow_nonneg (abs_nonneg r) _)
  · exact le_rfl

theorem b1loc_farW_eq (D : ℝ) (m : ℕ) (r : ℝ) :
    b1loc_farW D m r = b1loc_farB r * b1loc_farC D m r := by
  unfold b1loc_farW b1loc_farB b1loc_farC
  split_ifs
  · rw [show m + 8 = (m + 7) + 1 by ring, pow_succ, mul_inv]
    ring
  · ring

theorem b1loc_farB_sq (r : ℝ) : b1loc_farB r ^ 2 = b1loc_farA r := by
  unfold b1loc_farB b1loc_farA
  split_ifs
  · rw [inv_pow]
  · ring

theorem b1loc_farA_le (r : ℝ) : b1loc_farA r ≤ 4 * (1 + ‖r‖) ^ (-(2 : ℝ)) := by
  rw [b1loc_decay2_eq]
  unfold b1loc_farA
  split_ifs with h
  · have h1 : 1 + |r| ≤ 2 * |r| := by linarith
    have hpos : 0 < 1 + |r| := by positivity
    have e : (|r| ^ 2)⁻¹ = 4 * ((2 * |r|) ^ 2)⁻¹ := by
      rw [mul_pow, mul_inv, ← mul_assoc]
      norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le h1 2)) (by norm_num)
  · positivity

theorem b1loc_lintegral_farA_lt_top : ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r) < ⊤ := by
  calc ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)
      ≤ ∫⁻ r : ℝ, ENNReal.ofReal (4 * (1 + ‖r‖) ^ (-(2 : ℝ))) :=
        lintegral_mono fun r => ENNReal.ofReal_le_ofReal (b1loc_farA_le r)
    _ < ⊤ := (b1loc_integrable_decay2.const_mul 4).lintegral_lt_top

/-! ## Pointwise bounds of the far part -/

/-- The majorant `W(x) = ∫ ω(r) |w∞(x - r e_t)| dr`. -/
def b1loc_farMajorant (D : ℝ) (m : ℕ) (f : Space m → ℝ) (p₀ : Space m) (x : FourierSpace m) :
    ℝ≥0∞ :=
  ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farW D m r) *
    ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ

theorem b1loc_far_pointwise {D : ℝ}
    (hD : ∀ r : ℝ, 93 ≤ |r| → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |fhp_highPassKernel b1loc_cutoff r| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s)| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s) - fhp_highPassKernel b1loc_cutoff r| ≤
        D * (|r| ^ (m + 8))⁻¹ * s)
    (f : Space m → ℝ) (p₀ : Space m) {x : FourierSpace m}
    (hx : ‖x - (fourierToParabolic m).symm p₀‖ < 7) (r : ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖fhp_highPassKernel b1loc_cutoff r * b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ≤
        ENNReal.ofReal (b1loc_farW D m r) *
          ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ∧
      ‖fhp_highPassKernel b1loc_cutoff (r + s) *
          b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ≤
        ENNReal.ofReal (b1loc_farW D m r) *
          ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ∧
      ‖(fhp_highPassKernel b1loc_cutoff (r + s) - fhp_highPassKernel b1loc_cutoff r) *
          b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ≤
        ENNReal.ofReal s * (ENNReal.ofReal (b1loc_farW D m r) *
          ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) := by
  by_cases hr : 93 ≤ |r|
  · obtain ⟨h1, h2, h3⟩ := hD r hr s hs0 hs1
    have hω : b1loc_farW D m r = D * (|r| ^ (m + 8))⁻¹ := ite_eq_left hr
    rw [hω]
    simp only [enorm_mul]
    have key : ∀ t : ℝ, |t| ≤ D * (|r| ^ (m + 8))⁻¹ →
        ‖t‖ₑ ≤ ENNReal.ofReal (D * (|r| ^ (m + 8))⁻¹) := fun t ht => by
      rw [← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal ht
    refine ⟨mul_le_mul_of_nonneg_right (key _ h1) zero_le,
      mul_le_mul_of_nonneg_right (key _ h2) zero_le, ?_⟩
    rw [← mul_assoc, ← ENNReal.ofReal_mul hs0]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (h3.trans_eq (by ring))
  · have h0 : b1loc_farPart m f p₀ (x - r • timeVector m) = 0 :=
      b1loc_farPart_shift_eq_zero f p₀ hx (by linarith [not_le.1 hr])
    simp [h0]

theorem b1loc_far_V_le {D : ℝ}
    (hD : ∀ r : ℝ, 93 ≤ |r| → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |fhp_highPassKernel b1loc_cutoff r| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s)| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s) - fhp_highPassKernel b1loc_cutoff r| ≤
        D * (|r| ^ (m + 8))⁻¹ * s)
    (f : Space m → ℝ) (p₀ : Space m) {x : FourierSpace m}
    (hx : ‖x - (fourierToParabolic m).symm p₀‖ < 7) :
    ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x‖ₑ ≤
      b1loc_farMajorant D m f p₀ x :=
  (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_mono fun r => (b1loc_far_pointwise hD f p₀ hx r le_rfl zero_le_one).1)

theorem b1loc_far_V_diff_le {D : ℝ}
    (hD : ∀ r : ℝ, 93 ≤ |r| → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |fhp_highPassKernel b1loc_cutoff r| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s)| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s) - fhp_highPassKernel b1loc_cutoff r| ≤
        D * (|r| ^ (m + 8))⁻¹ * s)
    (hKm : AEStronglyMeasurable (fhp_highPassKernel b1loc_cutoff) volume)
    (f : Space m → ℝ) (p₀ : Space m) {x : FourierSpace m}
    (hx : ‖x - (fourierToParabolic m).symm p₀‖ < 7)
    (hsec : AEStronglyMeasurable
      (fun r : ℝ => b1loc_farPart m f p₀ (x - r • timeVector m)) volume)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)
        (x + s • timeVector m) -
      fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x‖ₑ ≤
      ENNReal.ofReal s * b1loc_farMajorant D m f p₀ x := by
  by_cases hWt : b1loc_farMajorant D m f p₀ x = ⊤
  · rw [hWt, ENNReal.mul_top (ENNReal.ofReal_pos.2 hs0).ne']
    exact le_top
  have hWlt : b1loc_farMajorant D m f p₀ x < ⊤ := lt_top_iff_ne_top.2 hWt
  have hpw := fun r => b1loc_far_pointwise hD f p₀ hx r hs0.le hs1
  have hi0 : Integrable (fun r : ℝ => fhp_highPassKernel b1loc_cutoff r *
      b1loc_farPart m f p₀ (x - r • timeVector m)) :=
    ⟨hKm.mul hsec, (lintegral_mono fun r => (hpw r).1).trans_lt hWlt⟩
  have hi1 : Integrable (fun r : ℝ => fhp_highPassKernel b1loc_cutoff (r + s) *
      b1loc_farPart m f p₀ (x - r • timeVector m)) :=
    ⟨(hKm.comp_measurePreserving (measurePreserving_add_right volume s)).mul hsec,
      (lintegral_mono fun r => (hpw r).2.1).trans_lt hWlt⟩
  have he : ∀ r : ℝ, x + s • timeVector m - (r + s) • timeVector m = x - r • timeVector m := by
    intro r
    rw [add_smul]
    abel
  have hshift : fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)
        (x + s • timeVector m) =
      ∫ r : ℝ, fhp_highPassKernel b1loc_cutoff (r + s) *
        b1loc_farPart m f p₀ (x - r • timeVector m) := by
    have h : (∫ r : ℝ, fhp_highPassKernel b1loc_cutoff (r + s) *
          b1loc_farPart m f p₀ (x + s • timeVector m - (r + s) • timeVector m)) =
        ∫ r : ℝ, fhp_highPassKernel b1loc_cutoff r *
          b1loc_farPart m f p₀ (x + s • timeVector m - r • timeVector m) :=
      integral_add_right_eq_self (fun r : ℝ => fhp_highPassKernel b1loc_cutoff r *
        b1loc_farPart m f p₀ (x + s • timeVector m - r • timeVector m)) s
    simp only [he] at h
    exact h.symm
  have hV0 : fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x =
      ∫ r : ℝ, fhp_highPassKernel b1loc_cutoff r *
        b1loc_farPart m f p₀ (x - r • timeVector m) := rfl
  rw [hshift, hV0, ← integral_sub hi1 hi0]
  calc ‖∫ r : ℝ, (fhp_highPassKernel b1loc_cutoff (r + s) *
          b1loc_farPart m f p₀ (x - r • timeVector m) -
        fhp_highPassKernel b1loc_cutoff r * b1loc_farPart m f p₀ (x - r • timeVector m))‖ₑ
      ≤ ∫⁻ r : ℝ, ‖fhp_highPassKernel b1loc_cutoff (r + s) *
          b1loc_farPart m f p₀ (x - r • timeVector m) -
        fhp_highPassKernel b1loc_cutoff r * b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r : ℝ, ENNReal.ofReal s * (ENNReal.ofReal (b1loc_farW D m r) *
          ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) :=
        lintegral_mono fun r => by
          rw [← sub_mul]
          exact (hpw r).2.2
    _ = ENNReal.ofReal s * b1loc_farMajorant D m f p₀ x :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- `LGag(V∞) + ∫_{B₇} |V∞|² ≤ 2 ∫_{B₇} W²`. -/
theorem b1loc_far_energy_le_W {D : ℝ}
    (hD : ∀ r : ℝ, 93 ≤ |r| → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      |fhp_highPassKernel b1loc_cutoff r| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s)| ≤ D * (|r| ^ (m + 8))⁻¹ ∧
      |fhp_highPassKernel b1loc_cutoff (r + s) - fhp_highPassKernel b1loc_cutoff r| ≤
        D * (|r| ^ (m + 8))⁻¹ * s)
    (hKm : AEStronglyMeasurable (fhp_highPassKernel b1loc_cutoff) volume)
    {f : Space m → ℝ} {B : ℝ} (hB : HasStandardParabolicBMOBound m f B) (p₀ : Space m) :
    b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
        (fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)) +
      ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
          (b1loc_farPart m f p₀) x‖ₑ ^ 2 ≤
      2 * ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        b1loc_farMajorant D m f p₀ x ^ 2 := by
  have hsec : ∀ᵐ x ∂(volume : Measure (FourierSpace m)), AEStronglyMeasurable
      (fun r : ℝ => b1loc_farPart m f p₀ (x - r • timeVector m)) volume :=
    (b1loc_aestronglyMeasurable_shift (b1loc_aestronglyMeasurable_farPart hB p₀)).prodMk_left
  have hae : ∀ᵐ x ∂(volume.restrict (Metric.ball ((fourierToParabolic m).symm p₀) 7)),
      ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x‖ₑ ≤
          b1loc_farMajorant D m f p₀ x ∧
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)
              (x + s • timeVector m) -
            fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀) x‖ₑ ≤
            ENNReal.ofReal s * b1loc_farMajorant D m f p₀ x := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hsec] with x hxs hx
    have hx' : ‖x - (fourierToParabolic m).symm p₀‖ < 7 := mem_ball_iff_norm.1 hx
    exact ⟨b1loc_far_V_le hD f p₀ hx', fun s hs0 hs1 =>
      b1loc_far_V_diff_le hD hKm f p₀ hx' hxs hs0 hs1⟩
  have h1 : ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
          (b1loc_farPart m f p₀) x‖ₑ ^ 2 ≤
      ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        b1loc_farMajorant D m f p₀ x ^ 2 :=
    lintegral_mono_ae (hae.mono fun x hx => pow_le_pow_left₀ zero_le hx.1 2)
  have h2 : b1loc_localGagliardo ((fourierToParabolic m).symm p₀)
        (fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)) ≤
      ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        b1loc_farMajorant D m f p₀ x ^ 2 := by
    unfold b1loc_localGagliardo
    calc ∫⁻ s in Ioc (0 : ℝ) 1, (ENNReal.ofReal s)⁻¹ ^ 2 *
          ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)
                (x + s • timeVector m) -
              fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
                (b1loc_farPart m f p₀) x‖ₑ ^ 2
        ≤ ∫⁻ _s in Ioc (0 : ℝ) 1, ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            b1loc_farMajorant D m f p₀ x ^ 2 := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          have hb : ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
              ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)
                  (x + s • timeVector m) -
                fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
                  (b1loc_farPart m f p₀) x‖ₑ ^ 2 ≤
              ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
                ENNReal.ofReal s ^ 2 * b1loc_farMajorant D m f p₀ x ^ 2 :=
            lintegral_mono_ae (hae.mono fun x hx => by
              rw [← mul_pow]
              exact pow_le_pow_left₀ zero_le (hx.2 s hs.1 hs.2) 2)
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)] at hb
          calc (ENNReal.ofReal s)⁻¹ ^ 2 *
                ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
                  ‖fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff) (b1loc_farPart m f p₀)
                      (x + s • timeVector m) -
                    fhp_timeConvolution (fhp_highPassKernel b1loc_cutoff)
                      (b1loc_farPart m f p₀) x‖ₑ ^ 2
              ≤ (ENNReal.ofReal s)⁻¹ ^ 2 * (ENNReal.ofReal s ^ 2 *
                  ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
                    b1loc_farMajorant D m f p₀ x ^ 2) :=
                mul_le_mul_of_nonneg_left hb zero_le
            _ = ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
                  b1loc_farMajorant D m f p₀ x ^ 2 := by
                rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel
                  (ENNReal.ofReal_pos.2 hs.1).ne' ENNReal.ofReal_ne_top, one_pow, one_mul]
      _ = ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            b1loc_farMajorant D m f p₀ x ^ 2 := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  calc _ ≤ (∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
          b1loc_farMajorant D m f p₀ x ^ 2) +
        ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
          b1loc_farMajorant D m f p₀ x ^ 2 := add_le_add h2 h1
    _ = _ := (two_mul _).symm

/-! ## The `L²` bound of the majorant -/

/-- Cauchy–Schwarz for lower integrals on `ℝ`. -/
theorem b1loc_lintegral_mul_sq_le {f g : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume)
    (hg : AEMeasurable g volume) :
    (∫⁻ r, f r * g r) ^ 2 ≤ (∫⁻ r, f r ^ 2) * ∫⁻ r, g r ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hf hg
  have e : ∀ X : ℝ≥0∞, (X ^ (1 / 2 : ℝ)) ^ 2 = X := fun X => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ r, f r * g r) ^ 2
      ≤ ((∫⁻ r, f r ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ r, g r ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = (∫⁻ r, f r ^ 2) * ∫⁻ r, g r ^ 2 := by rw [mul_pow, e, e]

/-- `|P(p,R)| = V_m R^{m+2}`, `V_m = (2 ω_m).toReal`. -/
def b1loc_Vm (m : ℕ) : ℝ := (2 * ParabolicRectifiability.omega m).toReal

theorem b1loc_Vm_nonneg (m : ℕ) : 0 ≤ b1loc_Vm m := ENNReal.toReal_nonneg

theorem b1loc_parabolicVolume_ball_eq (p : Space m) {R : ℝ} (hR : 0 < R) :
    parabolicVolume m (Metric.ball p R) = ENNReal.ofReal (b1loc_Vm m * R ^ (m + 2)) := by
  rw [parabolicVolume_ball p R hR, b1loc_Vm, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_pow hR.le,
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (by norm_num) (omega_lt_top m).ne)]

/-- `∫_{B₇} |w∞(x - r e_t)|² ≤ C_BMO B² V_m (10 + |r|)^{m+4}` (concentric BMO growth on
`P(p₀, 10 + |r|)`). -/
theorem b1loc_far_shift_L2 {f : Space m → ℝ} {B Cb : ℝ} (hCb : 0 ≤ Cb) (p₀ : Space m)
    (h3 : ∀ R : ℝ, 10 ≤ R →
      ∫⁻ q in Metric.ball p₀ R, ‖f q - standardBallAverage m f p₀ 10‖ₑ ^ 2
          ∂parabolicVolume m ≤
        ENNReal.ofReal (Cb * B ^ 2 * (1 + Real.log (R / 10)) ^ 2) *
          parabolicVolume m (Metric.ball p₀ R))
    (r : ℝ) :
    ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ^ 2 ≤
      ENNReal.ofReal (Cb * B ^ 2 * b1loc_Vm m * (10 + |r|) ^ (m + 4)) := by
  set R := 10 + |r| with hRdef
  have hR10 : 10 ≤ R := by rw [hRdef]; linarith [abs_nonneg r]
  have hR0 : 0 < R := by linarith
  set U := fourierToParabolic m ⁻¹' Metric.ball p₀ R with hU
  have hUm : MeasurableSet U :=
    (Metric.isOpen_ball.preimage (fourierToParabolic m).continuous).measurableSet
  have hsub : ∀ x ∈ Metric.ball ((fourierToParabolic m).symm p₀) 7,
      x - r • timeVector m ∈ U := by
    intro x hx
    exact b1loc_shift_mem_ball p₀ (mem_ball_iff_norm.1 hx) (by linarith)
      (by rw [hRdef]; nlinarith [abs_nonneg r])
  have hlog : (1 + Real.log (R / 10)) ^ 2 ≤ R ^ 2 := by
    have h1 : 0 ≤ Real.log (R / 10) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
    have h2 : Real.log (R / 10) ≤ R / 10 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hR0 (by norm_num))
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hV := b1loc_Vm_nonneg m
  have hCB : 0 ≤ Cb * B ^ 2 := mul_nonneg hCb (sq_nonneg B)
  calc ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ^ 2
      ≤ ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
          U.indicator (fun y => ‖b1loc_meanFree m f p₀ y‖ₑ ^ 2) (x - r • timeVector m) := by
        refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
        have hU' := hsub x hx
        simp only [indicator_of_mem hU']
        unfold b1loc_farPart
        by_cases h : x - r • timeVector m ∈ (b1loc_nearSet m p₀)ᶜ
        · simp only [indicator_of_mem h, le_refl]
        · simp [indicator_of_notMem h]
    _ ≤ ∫⁻ x, U.indicator (fun y => ‖b1loc_meanFree m f p₀ y‖ₑ ^ 2)
          (x - r • timeVector m) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, U.indicator (fun y => ‖b1loc_meanFree m f p₀ y‖ₑ ^ 2) y :=
        lintegral_sub_right_eq_self _ _
    _ = ∫⁻ y in U, ‖b1loc_meanFree m f p₀ y‖ₑ ^ 2 := lintegral_indicator hUm _
    _ = ∫⁻ q in Metric.ball p₀ R, ‖f q - standardBallAverage m f p₀ 10‖ₑ ^ 2
          ∂parabolicVolume m :=
        (fourierToParabolic_measurePreserving m).setLIntegral_comp_preimage_emb
          (fourierToParabolicMeasurableEquiv m).measurableEmbedding
          (fun q => ‖f q - standardBallAverage m f p₀ 10‖ₑ ^ 2) (Metric.ball p₀ R)
    _ ≤ ENNReal.ofReal (Cb * B ^ 2 * (1 + Real.log (R / 10)) ^ 2) *
          parabolicVolume m (Metric.ball p₀ R) := h3 R hR10
    _ = ENNReal.ofReal (Cb * B ^ 2 * (1 + Real.log (R / 10)) ^ 2 *
          (b1loc_Vm m * R ^ (m + 2))) := by
        rw [b1loc_parabolicVolume_ball_eq p₀ hR0,
          ← ENNReal.ofReal_mul (mul_nonneg hCB (sq_nonneg _))]
    _ ≤ ENNReal.ofReal (Cb * B ^ 2 * b1loc_Vm m * R ^ (m + 4)) := by
        apply ENNReal.ofReal_le_ofReal
        calc Cb * B ^ 2 * (1 + Real.log (R / 10)) ^ 2 * (b1loc_Vm m * R ^ (m + 2))
            ≤ Cb * B ^ 2 * R ^ 2 * (b1loc_Vm m * R ^ (m + 2)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hCB)
                (mul_nonneg hV (pow_nonneg hR0.le _))
          _ = Cb * B ^ 2 * b1loc_Vm m * R ^ (m + 4) := by ring

/-- The real inequality behind the far weight:
`c(r)² C_BMO B² V_m (10 + |r|)^{m+4} ≤ (D² C_BMO V_m 2^{m+4}) B² a(r)` for `|r| ≥ 93`. -/
theorem b1loc_far_weight_ineq {D Cb B : ℝ} (hCb : 0 ≤ Cb) (m : ℕ) {r : ℝ} (hr : 93 ≤ |r|) :
    (D * (|r| ^ (m + 7))⁻¹) ^ 2 * (Cb * B ^ 2 * b1loc_Vm m * (10 + |r|) ^ (m + 4)) ≤
      D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2 * (|r| ^ 2)⁻¹ := by
  have hρ0 : 0 < |r| := by linarith
  have hne : |r| ≠ 0 := hρ0.ne'
  have hV := b1loc_Vm_nonneg m
  have hCBV : 0 ≤ Cb * B ^ 2 * b1loc_Vm m := mul_nonneg (mul_nonneg hCb (sq_nonneg B)) hV
  have hpow : (10 + |r|) ^ (m + 4) ≤ (2 * |r|) ^ (m + 4) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hp4 : |r| ^ (m + 4) ≠ 0 := pow_ne_zero _ hne
  have hkey : ((|r| ^ (m + 7))⁻¹) ^ 2 * (2 * |r|) ^ (m + 4) =
      2 ^ (m + 4) * (|r| ^ (m + 10))⁻¹ := by
    calc ((|r| ^ (m + 7))⁻¹) ^ 2 * (2 * |r|) ^ (m + 4)
        = (|r| ^ (m + 10) * |r| ^ (m + 4))⁻¹ * (2 ^ (m + 4) * |r| ^ (m + 4)) := by
          rw [inv_pow, mul_pow,
            show (|r| ^ (m + 7)) ^ 2 = |r| ^ (m + 10) * |r| ^ (m + 4) by ring]
      _ = 2 ^ (m + 4) * (|r| ^ (m + 10))⁻¹ * (|r| ^ (m + 4) * (|r| ^ (m + 4))⁻¹) := by
          rw [mul_inv]
          ring
      _ = 2 ^ (m + 4) * (|r| ^ (m + 10))⁻¹ := by rw [mul_inv_cancel₀ hp4, mul_one]
  have hinv : (|r| ^ (m + 10))⁻¹ ≤ (|r| ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hρ0 2) (pow_le_pow_right₀ (by linarith) (by omega))
  calc (D * (|r| ^ (m + 7))⁻¹) ^ 2 * (Cb * B ^ 2 * b1loc_Vm m * (10 + |r|) ^ (m + 4))
      ≤ (D * (|r| ^ (m + 7))⁻¹) ^ 2 * (Cb * B ^ 2 * b1loc_Vm m * (2 * |r|) ^ (m + 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCBV) (sq_nonneg _)
    _ = D ^ 2 * (Cb * B ^ 2 * b1loc_Vm m) *
          (((|r| ^ (m + 7))⁻¹) ^ 2 * (2 * |r|) ^ (m + 4)) := by ring
    _ = D ^ 2 * (Cb * B ^ 2 * b1loc_Vm m) * (2 ^ (m + 4) * (|r| ^ (m + 10))⁻¹) := by
        rw [hkey]
    _ ≤ D ^ 2 * (Cb * B ^ 2 * b1loc_Vm m) * (2 ^ (m + 4) * (|r| ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv (by positivity))
          (mul_nonneg (sq_nonneg D) hCBV)
    _ = D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2 * (|r| ^ 2)⁻¹ := by ring

/-- **`L²` bound of the majorant:** `∫_{B₇} W² ≤ A (K₁ B²) A`, `A = ∫ a`,
`K₁ = D² C_BMO V_m 2^{m+4}`. -/
theorem b1loc_far_W_L2 {D : ℝ} (hD0 : 0 ≤ D) {f : Space m → ℝ} {B Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : HasStandardParabolicBMOBound m f B) (p₀ : Space m)
    (h3 : ∀ R : ℝ, 10 ≤ R →
      ∫⁻ q in Metric.ball p₀ R, ‖f q - standardBallAverage m f p₀ 10‖ₑ ^ 2
          ∂parabolicVolume m ≤
        ENNReal.ofReal (Cb * B ^ 2 * (1 + Real.log (R / 10)) ^ 2) *
          parabolicVolume m (Metric.ball p₀ R)) :
    ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        b1loc_farMajorant D m f p₀ x ^ 2 ≤
      (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
        (ENNReal.ofReal (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2) *
          ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) := by
  have hshift := b1loc_aestronglyMeasurable_shift (b1loc_aestronglyMeasurable_farPart hB p₀)
  have hsec : ∀ᵐ x ∂(volume.restrict (Metric.ball ((fourierToParabolic m).symm p₀) 7)),
      AEStronglyMeasurable (fun r : ℝ => b1loc_farPart m f p₀ (x - r • timeVector m)) volume :=
    ae_restrict_of_ae hshift.prodMk_left
  have hA1 : ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farB r) ^ 2 =
      ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r) :=
    lintegral_congr fun r => by
      rw [← ENNReal.ofReal_pow (b1loc_farB_nonneg r), b1loc_farB_sq]
  have hCS : ∀ᵐ x ∂(volume.restrict (Metric.ball ((fourierToParabolic m).symm p₀) 7)),
      b1loc_farMajorant D m f p₀ x ^ 2 ≤
        (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
          ∫⁻ r : ℝ, (ENNReal.ofReal (b1loc_farC D m r) *
            ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) ^ 2 := by
    filter_upwards [hsec] with x hx
    have hM : b1loc_farMajorant D m f p₀ x = ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farB r) *
        (ENNReal.ofReal (b1loc_farC D m r) *
          ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) :=
      lintegral_congr fun r => by
        rw [b1loc_farW_eq, ENNReal.ofReal_mul (b1loc_farB_nonneg r), mul_assoc]
    rw [hM, ← hA1]
    exact b1loc_lintegral_mul_sq_le b1loc_measurable_farB.ennreal_ofReal.aemeasurable
      ((b1loc_measurable_farC D m).ennreal_ofReal.aemeasurable.mul hx.enorm)
  have hAfin : ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r) ≠ ⊤ :=
    b1loc_lintegral_farA_lt_top.ne
  have hmeas : AEMeasurable (Function.uncurry fun (x : FourierSpace m) (r : ℝ) =>
      (ENNReal.ofReal (b1loc_farC D m r) *
        ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) ^ 2)
      ((volume.restrict (Metric.ball ((fourierToParabolic m).symm p₀) 7)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact ((((b1loc_measurable_farC D m).ennreal_ofReal.comp measurable_snd).aemeasurable.mul
      hshift.enorm).pow_const 2).restrict
  have hpt : ∀ r : ℝ, ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
      (ENNReal.ofReal (b1loc_farC D m r) *
        ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) ^ 2 ≤
      ENNReal.ofReal (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2) *
        ENNReal.ofReal (b1loc_farA r) := by
    intro r
    by_cases hr : 93 ≤ |r|
    · have hc : b1loc_farC D m r = D * (|r| ^ (m + 7))⁻¹ := ite_eq_left hr
      have ha : b1loc_farA r = (|r| ^ 2)⁻¹ := ite_eq_left hr
      have hc0 : 0 ≤ D * (|r| ^ (m + 7))⁻¹ :=
        mul_nonneg hD0 (inv_nonneg.2 (pow_nonneg (abs_nonneg r) _))
      have hK1 : 0 ≤ D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg D) hCb) (b1loc_Vm_nonneg m))
          (by positivity)) (sq_nonneg B)
      simp only [mul_pow]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), hc, ha]
      calc ENNReal.ofReal (D * (|r| ^ (m + 7))⁻¹) ^ 2 *
            ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
              ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ ^ 2
          ≤ ENNReal.ofReal (D * (|r| ^ (m + 7))⁻¹) ^ 2 *
              ENNReal.ofReal (Cb * B ^ 2 * b1loc_Vm m * (10 + |r|) ^ (m + 4)) :=
            mul_le_mul_of_nonneg_left (b1loc_far_shift_L2 hCb p₀ h3 r) zero_le
        _ = ENNReal.ofReal ((D * (|r| ^ (m + 7))⁻¹) ^ 2 *
              (Cb * B ^ 2 * b1loc_Vm m * (10 + |r|) ^ (m + 4))) := by
            rw [← ENNReal.ofReal_pow hc0, ← ENNReal.ofReal_mul (sq_nonneg _)]
        _ ≤ ENNReal.ofReal (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2 * (|r| ^ 2)⁻¹) :=
            ENNReal.ofReal_le_ofReal (b1loc_far_weight_ineq hCb m hr)
        _ = ENNReal.ofReal (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2) *
              ENNReal.ofReal ((|r| ^ 2)⁻¹) := ENNReal.ofReal_mul hK1
    · have hc : b1loc_farC D m r = 0 := ite_eq_right hr
      simp [hc]
  calc ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
        b1loc_farMajorant D m f p₀ x ^ 2
      ≤ ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
          (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
            ∫⁻ r : ℝ, (ENNReal.ofReal (b1loc_farC D m r) *
              ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) ^ 2 := lintegral_mono_ae hCS
    _ = (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
          ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            ∫⁻ r : ℝ, (ENNReal.ofReal (b1loc_farC D m r) *
              ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) ^ 2 :=
        lintegral_const_mul' _ _ hAfin
    _ = (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
          ∫⁻ r : ℝ, ∫⁻ x in Metric.ball ((fourierToParabolic m).symm p₀) 7,
            (ENNReal.ofReal (b1loc_farC D m r) *
              ‖b1loc_farPart m f p₀ (x - r • timeVector m)‖ₑ) ^ 2 := by
        rw [lintegral_lintegral_swap hmeas]
    _ ≤ (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
          ∫⁻ r : ℝ, ENNReal.ofReal (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2) *
            ENNReal.ofReal (b1loc_farA r) :=
        mul_le_mul_of_nonneg_left (lintegral_mono hpt) zero_le
    _ = (∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) *
          (ENNReal.ofReal (D ^ 2 * Cb * b1loc_Vm m * 2 ^ (m + 4) * B ^ 2) *
            ∫⁻ r : ℝ, ENNReal.ofReal (b1loc_farA r)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end ParabolicRectifiability.Characterization
