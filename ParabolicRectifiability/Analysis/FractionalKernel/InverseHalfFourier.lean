import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Gamma

/-! # The weak Fourier transform of `|t|^{-1/2}`

One-dimensional analysis; this module depends on Mathlib only.

Main result (`fhpbb2f_inverseHalf_fourier_schwartz`): for every `ψ : 𝓢(ℝ, ℂ)`,
`∫ |t|^{-1/2} ψ̂(t) dt = ∫ |τ|^{-1/2} ψ(τ) dτ`, with Mathlib's phase `ψ̂(t) = ∫ e^{-2πitx} ψ(x) dx`
and constant one.

Proof (Gaussian subordination with real Gamma integrals only). With
`C = Γ(1/4) π^{-1/4}` and, for **nonzero** variables only,
* `∫_0^∞ b^{-3/4} e^{-π b t²} db = C |t|^{-1/2}` (`t ≠ 0`; `fhpbb2f_integral_k1`),
* `∫_0^∞ b^{-3/4} b^{-1/2} e^{-π τ²/b} db = C |τ|^{-1/2}` (`τ ≠ 0`; substitution `b ↦ b⁻¹`,
  `fhpbb2f_integral_k2`),

the Gaussian transform `𝓕(e^{-π b x²})(τ) = b^{-1/2} e^{-π τ²/b}` and the multiplication formula,
the identity follows from two absolutely convergent interchanges (`fhpbb2f_weak_fourier`). Their
integrability is proved from `|·|^{-1/2} ‖𝓕 ψ‖ ∈ L¹` and `|·|^{-1/2} ‖ψ‖ ∈ L¹`. The parameter
integrals diverge at the zero variable; the subordination formulas are used only almost
everywhere (off `{0}`), never as finite integrals at zero.
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped FourierTransform SchwartzMap

namespace ParabolicRectifiability.FractionalKernel

/-! ## Subordination formulas (nonzero variables) -/

/-- The subordination constant `Γ(1/4) π^{-1/4}`. -/
def fhpbb2f_const : ℝ := Real.Gamma (1 / 4) * π ^ (-(1 / 4 : ℝ))

theorem fhpbb2f_const_pos : 0 < fhpbb2f_const :=
  mul_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.rpow_pos_of_pos Real.pi_pos _)

/-- The first subordination kernel `b^{-3/4} e^{-π b t²}` (variables `t`, then `b`). -/
def fhpbb2f_k1 (t b : ℝ) : ℝ := b ^ (-(3 / 4 : ℝ)) * exp (-π * b * t ^ 2)

/-- The second subordination kernel `b^{-3/4} (b^{-1/2} e^{-π τ²/b})` (variables `b`, then `τ`):
`b^{-3/4}` times the Fourier transform of the Gaussian `x ↦ e^{-π b x²}` at `τ`. -/
def fhpbb2f_k2 (b τ : ℝ) : ℝ := b ^ (-(3 / 4 : ℝ)) * (b ^ (-(1 / 2 : ℝ)) * exp (-(π / b) * τ ^ 2))

theorem fhpbb2f_k1_nonneg (t : ℝ) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ fhpbb2f_k1 t b :=
  mul_nonneg (Real.rpow_nonneg hb _) (Real.exp_pos _).le

theorem fhpbb2f_k2_nonneg {b : ℝ} (hb : 0 ≤ b) (τ : ℝ) : 0 ≤ fhpbb2f_k2 b τ :=
  mul_nonneg (Real.rpow_nonneg hb _) (mul_nonneg (Real.rpow_nonneg hb _) (Real.exp_pos _).le)

theorem fhpbb2f_sq_rpow (t : ℝ) : (t ^ 2) ^ (-(1 / 4 : ℝ)) = |t| ^ (-(1 / 2 : ℝ)) := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
  norm_num

theorem fhpbb2f_k1_eq (t : ℝ) :
    (fun b : ℝ => fhpbb2f_k1 t b) =
      fun b : ℝ => b ^ (-(3 / 4 : ℝ)) * exp (-(π * t ^ 2) * b ^ (1 : ℝ)) := by
  funext b
  rw [fhpbb2f_k1, Real.rpow_one, show -(π * t ^ 2) * b = -π * b * t ^ 2 by ring]

theorem fhpbb2f_integrableOn_k1 {t : ℝ} (ht : t ≠ 0) :
    IntegrableOn (fun b : ℝ => fhpbb2f_k1 t b) (Ioi 0) := by
  have hb : 0 < π * t ^ 2 := by positivity
  rw [fhpbb2f_k1_eq]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos hb

/-- First subordination formula: `∫_0^∞ b^{-3/4} e^{-π b t²} db = Γ(1/4) π^{-1/4} |t|^{-1/2}`
for `t ≠ 0`. -/
theorem fhpbb2f_integral_k1 {t : ℝ} (ht : t ≠ 0) :
    ∫ b in Ioi (0 : ℝ), fhpbb2f_k1 t b = fhpbb2f_const * |t| ^ (-(1 / 2 : ℝ)) := by
  have hb : 0 < π * t ^ 2 := by positivity
  rw [fhpbb2f_k1_eq, integral_rpow_mul_exp_neg_mul_rpow one_pos (by norm_num) hb,
    show (-(-(3 / 4 : ℝ) + 1) / 1) = -(1 / 4 : ℝ) by norm_num,
    show ((-(3 / 4 : ℝ) + 1) / 1) = 1 / 4 by norm_num,
    Real.mul_rpow Real.pi_pos.le (sq_nonneg t), fhpbb2f_sq_rpow, fhpbb2f_const]
  ring

/-- The substitution `b ↦ b⁻¹` turns the second kernel into the first. -/
theorem fhpbb2f_subst (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
        ((x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) *
          ((x ^ (-1 : ℝ)) ^ (-(1 / 2 : ℝ)) * exp (-(π / x ^ (-1 : ℝ)) * τ ^ 2))) =
      fhpbb2f_k1 τ x := by
  have h1 : x ^ ((-1 : ℝ) - 1) * x ^ (3 / 4 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    norm_num
  rw [abs_neg, abs_one, one_mul, smul_eq_mul, Real.rpow_neg_one, Real.inv_rpow hx.le,
    Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_neg hx.le, neg_neg, neg_neg,
    div_inv_eq_mul, fhpbb2f_k1, ← h1, show -(π * x) * τ ^ 2 = -π * x * τ ^ 2 by ring]
  ring

theorem fhpbb2f_integrableOn_k2 {τ : ℝ} (hτ : τ ≠ 0) :
    IntegrableOn (fun b : ℝ => fhpbb2f_k2 b τ) (Ioi 0) := by
  have h := fhpbb2f_integrableOn_k1 hτ
  rw [← integrableOn_Ioi_comp_rpow_iff (fun b : ℝ => fhpbb2f_k2 b τ)
    (by norm_num : (-1 : ℝ) ≠ 0)]
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  exact (fhpbb2f_subst τ hx).symm

/-- Second subordination formula:
`∫_0^∞ b^{-3/4} b^{-1/2} e^{-π τ²/b} db = Γ(1/4) π^{-1/4} |τ|^{-1/2}` for `τ ≠ 0`. -/
theorem fhpbb2f_integral_k2 {τ : ℝ} (hτ : τ ≠ 0) :
    ∫ b in Ioi (0 : ℝ), fhpbb2f_k2 b τ = fhpbb2f_const * |τ| ^ (-(1 / 2 : ℝ)) := by
  rw [← integral_comp_rpow_Ioi (fun b : ℝ => fhpbb2f_k2 b τ) (by norm_num : (-1 : ℝ) ≠ 0),
    ← fhpbb2f_integral_k1 hτ]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => fhpbb2f_subst τ hx)

/-! ## The Gaussian pairing -/

/-- Multiplication formula `∫ g 𝓕 f = ∫ 𝓕 g f` for integrable `f, g : ℝ → ℂ`. -/
theorem fhpbb2f_integral_mul_fourier {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ t, g t * 𝓕 f t = ∫ x, 𝓕 g x * f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) Real.continuous_fourierChar
    continuous_inner hf hg
  rw [flip_innerₗ] at h
  simp only [smul_eq_mul] at h
  calc ∫ t, g t * 𝓕 f t = ∫ t, 𝓕 f t * g t := by simp_rw [mul_comm]
    _ = ∫ x, f x * 𝓕 g x := h
    _ = ∫ x, 𝓕 g x * f x := by simp_rw [mul_comm]

/-- Pairing with a Gaussian: for `b > 0`,
`∫ e^{-π b t²} 𝓕 f(t) dt = ∫ b^{-1/2} e^{-π τ²/b} f(τ) dτ`. -/
theorem fhpbb2f_gaussian_pairing {f : ℝ → ℂ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    ∫ t, ((exp (-π * b * t ^ 2) : ℝ) : ℂ) * 𝓕 f t =
      ∫ τ, ((b ^ (-(1 / 2 : ℝ)) * exp (-(π / b) * τ ^ 2) : ℝ) : ℂ) * f τ := by
  have hbc : 0 < (b : ℂ).re := by simpa using hb
  have hG : ∀ t : ℝ, ((exp (-π * b * t ^ 2) : ℝ) : ℂ) =
      Complex.exp (-(π : ℂ) * (b : ℂ) * (t : ℂ) ^ 2) := by
    intro t
    push_cast
    ring_nf
  have hGint : Integrable (fun t : ℝ => Complex.exp (-(π : ℂ) * (b : ℂ) * (t : ℂ) ^ 2)) := by
    have h := Integrable.ofReal (𝕜 := ℂ) (integrable_exp_neg_mul_sq (by positivity : 0 < π * b))
    refine h.congr (ae_of_all _ fun t => ?_)
    simp only
    rw [← hG t]
    congr 2
    ring
  have hFG := fourier_gaussian_pi hbc
  calc ∫ t : ℝ, ((exp (-π * b * t ^ 2) : ℝ) : ℂ) * 𝓕 f t
      = ∫ t : ℝ, Complex.exp (-(π : ℂ) * (b : ℂ) * (t : ℂ) ^ 2) * 𝓕 f t := by
        simp_rw [hG]
    _ = ∫ τ : ℝ, 𝓕 (fun t : ℝ => Complex.exp (-(π : ℂ) * (b : ℂ) * (t : ℂ) ^ 2)) τ * f τ :=
        fhpbb2f_integral_mul_fourier hf hGint
    _ = ∫ τ : ℝ, ((b ^ (-(1 / 2 : ℝ)) * exp (-(π / b) * τ ^ 2) : ℝ) : ℂ) * f τ := by
        rw [hFG]
        congr 1
        funext τ
        congr 1
        rw [Complex.ofReal_mul, Complex.ofReal_cpow hb.le, Complex.ofReal_exp]
        push_cast
        rw [Complex.cpow_neg, one_div, neg_div]

/-! ## The weak identity for integrable data -/

/-- The weak Fourier identity of `|t|^{-1/2}` for an integrable continuous `f` with continuous
transform such that `|·|^{-1/2} ‖f‖` and `|·|^{-1/2} ‖𝓕 f‖` are integrable. -/
theorem fhpbb2f_weak_fourier {f : ℝ → ℂ} (hf : Integrable f) (hfc : Continuous f)
    (hFc : Continuous (𝓕 f))
    (hIf : Integrable (fun τ : ℝ => |τ| ^ (-(1 / 2 : ℝ)) * ‖f τ‖))
    (hIFf : Integrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ)) * ‖𝓕 f t‖)) :
    ∫ t : ℝ, ((|t| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * 𝓕 f t =
      ∫ τ : ℝ, ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f τ := by
  have hC : (fhpbb2f_const : ℂ) ≠ 0 := by exact_mod_cast fhpbb2f_const_pos.ne'
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := Measure.ae_ne volume 0
  -- the left side as a parameter integral (a.e. in `t`)
  have L1 : ∫ t : ℝ, ((|t| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * 𝓕 f t =
      (fhpbb2f_const : ℂ)⁻¹ *
        ∫ t : ℝ, ∫ b in Ioi (0 : ℝ), ((fhpbb2f_k1 t b : ℝ) : ℂ) * 𝓕 f t := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [h0] with t ht
    rw [integral_mul_const, integral_complex_ofReal, fhpbb2f_integral_k1 ht, Complex.ofReal_mul,
      ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  -- the right side as a parameter integral (a.e. in `τ`)
  have R1 : ∫ τ : ℝ, ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f τ =
      (fhpbb2f_const : ℂ)⁻¹ *
        ∫ τ : ℝ, ∫ b in Ioi (0 : ℝ), ((fhpbb2f_k2 b τ : ℝ) : ℂ) * f τ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [h0] with τ hτ
    rw [integral_mul_const, integral_complex_ofReal, fhpbb2f_integral_k2 hτ, Complex.ofReal_mul,
      ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  -- first absolute interchange
  have I1 : Integrable (Function.uncurry fun (t b : ℝ) => ((fhpbb2f_k1 t b : ℝ) : ℂ) * 𝓕 f t)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have meas : AEStronglyMeasurable
        (Function.uncurry fun (t b : ℝ) => ((fhpbb2f_k1 t b : ℝ) : ℂ) * 𝓕 f t)
        ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      change AEStronglyMeasurable (fun p : ℝ × ℝ => ((fhpbb2f_k1 p.1 p.2 : ℝ) : ℂ) * 𝓕 f p.1) _
      refine AEStronglyMeasurable.mul ?_ (hFc.comp continuous_fst).aestronglyMeasurable
      refine ((Complex.measurable_ofReal).comp ?_).aestronglyMeasurable
      unfold fhpbb2f_k1
      fun_prop
    rw [integrable_prod_iff meas]
    constructor
    · filter_upwards [h0] with t ht
      simp only [Function.uncurry_apply_pair]
      exact Integrable.mul_const (Integrable.ofReal (fhpbb2f_integrableOn_k1 ht)) _
    · refine (hIFf.const_mul fhpbb2f_const).congr ?_
      filter_upwards [h0] with t ht
      simp only [Function.uncurry_apply_pair]
      have : ∫ b in Ioi (0 : ℝ), ‖((fhpbb2f_k1 t b : ℝ) : ℂ) * 𝓕 f t‖ =
          ∫ b in Ioi (0 : ℝ), fhpbb2f_k1 t b * ‖𝓕 f t‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun b hb => ?_)
        simp only [norm_mul, Complex.norm_of_nonneg (fhpbb2f_k1_nonneg t (le_of_lt hb))]
      rw [this, integral_mul_const, fhpbb2f_integral_k1 ht]
      ring
  -- second absolute interchange
  have I2 : Integrable (Function.uncurry fun (b τ : ℝ) => ((fhpbb2f_k2 b τ : ℝ) : ℂ) * f τ)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)) := by
    have meas : AEStronglyMeasurable
        (Function.uncurry fun (b τ : ℝ) => ((fhpbb2f_k2 b τ : ℝ) : ℂ) * f τ)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)) := by
      change AEStronglyMeasurable (fun p : ℝ × ℝ => ((fhpbb2f_k2 p.1 p.2 : ℝ) : ℂ) * f p.2) _
      refine AEStronglyMeasurable.mul ?_ (hfc.comp continuous_snd).aestronglyMeasurable
      refine ((Complex.measurable_ofReal).comp ?_).aestronglyMeasurable
      unfold fhpbb2f_k2
      fun_prop
    rw [integrable_prod_iff' meas]
    constructor
    · filter_upwards [h0] with τ hτ
      simp only [Function.uncurry_apply_pair]
      exact Integrable.mul_const (Integrable.ofReal (fhpbb2f_integrableOn_k2 hτ)) _
    · refine (hIf.const_mul fhpbb2f_const).congr ?_
      filter_upwards [h0] with τ hτ
      simp only [Function.uncurry_apply_pair]
      have : ∫ b in Ioi (0 : ℝ), ‖((fhpbb2f_k2 b τ : ℝ) : ℂ) * f τ‖ =
          ∫ b in Ioi (0 : ℝ), fhpbb2f_k2 b τ * ‖f τ‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun b hb => ?_)
        simp only [norm_mul, Complex.norm_of_nonneg (fhpbb2f_k2_nonneg (le_of_lt hb) τ)]
      rw [this, integral_mul_const, fhpbb2f_integral_k2 hτ]
      ring
  -- the Gaussian step, for each parameter `b > 0`
  have G3 : ∫ b in Ioi (0 : ℝ), ∫ t : ℝ, ((fhpbb2f_k1 t b : ℝ) : ℂ) * 𝓕 f t =
      ∫ b in Ioi (0 : ℝ), ∫ τ : ℝ, ((fhpbb2f_k2 b τ : ℝ) : ℂ) * f τ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun b hb => ?_)
    have e1 : ∀ t : ℝ, ((fhpbb2f_k1 t b : ℝ) : ℂ) * 𝓕 f t =
        ((b ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) * (((exp (-π * b * t ^ 2) : ℝ) : ℂ) * 𝓕 f t) := by
      intro t
      simp only [fhpbb2f_k1, Complex.ofReal_mul]
      ring
    have e2 : ∀ τ : ℝ, ((fhpbb2f_k2 b τ : ℝ) : ℂ) * f τ =
        ((b ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) *
          (((b ^ (-(1 / 2 : ℝ)) * exp (-(π / b) * τ ^ 2) : ℝ) : ℂ) * f τ) := by
      intro τ
      simp only [fhpbb2f_k2, Complex.ofReal_mul]
      ring
    simp_rw [e1, e2]
    rw [integral_const_mul, integral_const_mul, fhpbb2f_gaussian_pairing hf hb]
  rw [L1, integral_integral_swap I1, G3, integral_integral_swap I2, R1]

/-! ## Schwartz tests -/

/-- `|t|^{-1/2} ‖g t‖` is integrable for an integrable, continuous, bounded `g`. -/
theorem fhpbb2f_integrable_rpow_mul_norm {g : ℝ → ℂ} (hg : Integrable g) (hgc : Continuous g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ)) * ‖g t‖) := by
  have meas : AEStronglyMeasurable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ)) * ‖g t‖) volume := by
    refine AEStronglyMeasurable.mul ?_ hgc.norm.aestronglyMeasurable
    exact (continuous_abs.measurable.pow_const _).aestronglyMeasurable
  rw [← integrableOn_univ, ← union_compl_self (Metric.ball (0 : ℝ) 1)]
  refine IntegrableOn.union ?_ ?_
  · refine integrableOn_ball_of_norm_le_rpow (α := 1 / 2) (C := C) (by simp) (by simp; norm_num)
      (ae_of_all _ fun t => ?_) meas
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg t) _)
      (norm_nonneg _)), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC t) (Real.rpow_nonneg (abs_nonneg t) _)
  · refine Integrable.mono' hg.norm.integrableOn meas.restrict ?_
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet.compl (fun t ht => ?_)
    have h1 : 1 ≤ |t| := by
      simpa [Metric.mem_ball, Real.dist_eq] using ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg t) _)
      (norm_nonneg _))]
    calc |t| ^ (-(1 / 2 : ℝ)) * ‖g t‖ ≤ 1 * ‖g t‖ :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)) (norm_nonneg _)
      _ = ‖g t‖ := one_mul _

/-- **The weak Fourier identity of `|t|^{-1/2}` against Schwartz tests**, constant one and
Mathlib's phase: `∫ |t|^{-1/2} ψ̂(t) dt = ∫ |τ|^{-1/2} ψ(τ) dτ`. -/
theorem fhpbb2f_inverseHalf_fourier_schwartz (ψ : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, ((|t| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * 𝓕 (fun x : ℝ => ψ x) t =
      ∫ τ : ℝ, ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ := by
  set Ψ : 𝓢(ℝ, ℂ) := 𝓕 ψ with hΨ
  have hF : 𝓕 (fun x : ℝ => ψ x) = ⇑Ψ := rfl
  refine fhpbb2f_weak_fourier ψ.integrable ψ.continuous ?_ ?_ ?_
  · rw [hF]
    exact Ψ.continuous
  · exact fhpbb2f_integrable_rpow_mul_norm ψ.integrable ψ.continuous
      (fun x => SchwartzMap.norm_le_seminorm ℝ ψ x)
  · rw [hF]
    exact fhpbb2f_integrable_rpow_mul_norm Ψ.integrable Ψ.continuous
      (fun x => SchwartzMap.norm_le_seminorm ℝ Ψ x)

end ParabolicRectifiability.FractionalKernel
