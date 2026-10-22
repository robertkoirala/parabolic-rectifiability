import ParabolicRectifiability.Analysis.FourierAffine.Kernel

/-! # Pointwise control of the smoothed function by the affine error

The vanishing integral and first
spatial moments of `ψ_r` cancel every spatial affine function; Cauchy–Schwarz on
the parabolic ball `P_b(p,r)` then bounds `|ψ_r ⋆ f (p)|²`. The squared affine
error is an extended nonnegative `lintegral`, so no square-integrability of `f`
on the ball is assumed by the bound itself.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.FourierAffine

variable {m : ℕ}

/-- `(ψ_r ⋆ f)(p) = ∫ ψ_r(p - q) f(q) dq`. -/
def smoothing (r : ℝ) (f : FourierSpace m → ℝ) (p : FourierSpace m) : ℝ :=
  ∫ q, scaleKernel r (p - q) * f q

/-- The squared error of the best spatial affine fit, `inf_{a,b} ∫_{P_b(p,r)} |f - a - b·u|²`. -/
def affineError (f : FourierSpace m → ℝ) (p : FourierSpace m) (r : ℝ) : ℝ≥0∞ :=
  ⨅ (a : ℝ) (B : Spatial m →L[ℝ] ℝ),
    ∫⁻ q in coordBall p r, ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ ^ 2

/-- `a_f(p,r)² = r^(-k-2) · affineError`, with `k = m + 2`. -/
def affineEnergy (f : FourierSpace m → ℝ) (p : FourierSpace m) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ ^ (m + 4) * affineError f p r

/-- The constant `‖ψ_1‖₂²` of the pointwise bound. -/
def scaleKernelEnergy (m : ℕ) : ℝ := ∫ w : FourierSpace m, scaleKernelOne w ^ 2

theorem scaleKernelEnergy_nonneg (m : ℕ) : 0 ≤ scaleKernelEnergy m :=
  integral_nonneg fun _ => sq_nonneg _

theorem isOpen_coordBall (p : FourierSpace m) (r : ℝ) : IsOpen (coordBall p r) :=
  (isOpen_lt ((WithLp.fstL 2 ℝ (Spatial m) ℝ).continuous.sub continuous_const).norm
      continuous_const).inter
    (isOpen_lt ((WithLp.sndL 2 ℝ (Spatial m) ℝ).continuous.sub continuous_const).abs
      continuous_const)

theorem measurableSet_coordBall (p : FourierSpace m) (r : ℝ) : MeasurableSet (coordBall p r) :=
  (isOpen_coordBall p r).measurableSet

theorem sub_mem_coordBall_zero {p q : FourierSpace m} {r : ℝ} (h : p - q ∈ coordBall 0 r) :
    q ∈ coordBall p r := by
  simp only [coordBall, mem_ofPred_eq, WithLp.ofLp_sub, WithLp.ofLp_zero, Prod.fst_sub,
    Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero] at h ⊢
  rw [norm_sub_rev, abs_sub_comm]
  exact h

theorem continuous_scaleKernel_sub (r : ℝ) (p : FourierSpace m) :
    Continuous fun q => scaleKernel r (p - q) :=
  (continuous_scaleKernel r).comp (continuous_const.sub continuous_id)

theorem hasCompactSupport_scaleKernel_sub (r : ℝ) (p : FourierSpace m) :
    HasCompactSupport fun q => scaleKernel r (p - q) :=
  (hasCompactSupport_scaleKernel r).comp_homeomorph (Homeomorph.subLeft p)

theorem scaleKernel_sub_eq_zero {r : ℝ} (hr : 0 < r) {p q : FourierSpace m}
    (hq : q ∉ coordBall p r) : scaleKernel r (p - q) = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem =>
    hq (sub_mem_coordBall_zero (tsupport_scaleKernel_subset hr hmem))

theorem continuous_linear_fst (B : Spatial m →L[ℝ] ℝ) :
    Continuous fun q : FourierSpace m => B (WithLp.ofLp q).1 :=
  B.continuous.comp (WithLp.fstL 2 ℝ (Spatial m) ℝ).continuous

/-- Cancellation of a fixed spatial affine function. -/
theorem smoothing_eq_affine {r : ℝ} (hr : 0 < r) {f : FourierSpace m → ℝ}
    (hf : LocallyIntegrable f volume)
    (p : FourierSpace m) (a : ℝ) (B : Spatial m →L[ℝ] ℝ) :
    smoothing r f p = ∫ q, scaleKernel r (p - q) * (f q - (a + B (WithLp.ofLp q).1)) := by
  rw [smoothing]
  have h1 : Integrable (fun q => scaleKernel r (p - q) * f q) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport
      (continuous_scaleKernel_sub r p) (hasCompactSupport_scaleKernel_sub r p)
  have h2 : Integrable (fun q => scaleKernel r (p - q) * (a + B (WithLp.ofLp q).1)) :=
    ((continuous_scaleKernel_sub r p).mul (continuous_const.add (continuous_linear_fst B))).integrable_of_hasCompactSupport
      ((hasCompactSupport_scaleKernel_sub r p).mul_right)
  have hBint : Integrable (fun w : FourierSpace m => B (WithLp.ofLp w).1 * scaleKernel r w) :=
    ((continuous_linear_fst B).mul (continuous_scaleKernel r)).integrable_of_hasCompactSupport
      (hasCompactSupport_scaleKernel r).mul_left
  have h3 : ∫ q, scaleKernel r (p - q) * (a + B (WithLp.ofLp q).1) = 0 := by
    have hs := integral_sub_left_eq_self (μ := volume)
      (fun w => scaleKernel r w * (a + B (WithLp.ofLp (p - w)).1)) p
    simp only [sub_sub_cancel] at hs
    rw [hs]
    have hexp : (fun w => scaleKernel r w * (a + B (WithLp.ofLp (p - w)).1)) =
        fun w => (a + B (WithLp.ofLp p).1) * scaleKernel r w -
          B (WithLp.ofLp w).1 * scaleKernel r w := by
      funext w
      simp only [WithLp.ofLp_sub, Prod.fst_sub, map_sub]
      ring
    rw [hexp, integral_sub ((integrable_scaleKernel r).const_mul _) hBint, integral_const_mul,
      integral_scaleKernel hr, integral_linear_mul_scaleKernel, mul_zero, sub_zero]
  have hsplit : (fun q => scaleKernel r (p - q) * (f q - (a + B (WithLp.ofLp q).1))) =
      fun q => scaleKernel r (p - q) * f q -
        scaleKernel r (p - q) * (a + B (WithLp.ofLp q).1) := by
    funext q
    ring
  rw [hsplit, integral_sub h1 h2, h3, sub_zero]

theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem enorm_sq_eq_ofReal (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- `∫ |ψ_r(p - q)|² dq = r^(-k) ‖ψ_1‖₂²`. -/
theorem lintegral_scaleKernel_sub_sq {r : ℝ} (hr : 0 < r) (p : FourierSpace m) :
    ∫⁻ q, ‖scaleKernel r (p - q)‖ₑ ^ 2 =
      ENNReal.ofReal (scaleKernelEnergy m) * (ENNReal.ofReal r)⁻¹ ^ (m + 2) := by
  rw [lintegral_sub_left_eq_self (fun w => ‖scaleKernel r w‖ₑ ^ 2) p]
  simp_rw [enorm_sq_eq_ofReal]
  have hint : Integrable fun w : FourierSpace m => scaleKernel r w ^ 2 :=
    ((continuous_scaleKernel r).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : FourierSpace m) (|r| + r ^ 2))
        fun z hz => by
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
          rw [Pi.pow_apply, scaleKernel_eq_zero hz, zero_pow two_ne_zero])
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => sq_nonneg _),
    integral_sq_scaleKernel hr, ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity)),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hr.le, ENNReal.inv_pow,
    scaleKernelEnergy, mul_comm]

/-- `|(ψ_r ⋆ f)(p)|² ≤ ‖ψ_1‖₂² r^(-k) ∫_{P_b(p,r)} |f - a - B u|²`. -/
theorem enorm_smoothing_sq_le {r : ℝ} (hr : 0 < r) {f : FourierSpace m → ℝ}
    (hf : LocallyIntegrable f volume) (p : FourierSpace m) (a : ℝ) (B : Spatial m →L[ℝ] ℝ) :
    ‖smoothing r f p‖ₑ ^ 2 ≤
      ENNReal.ofReal (scaleKernelEnergy m) * (ENNReal.ofReal r)⁻¹ ^ (m + 2) *
        ∫⁻ q in coordBall p r, ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ ^ 2 := by
  rw [smoothing_eq_affine hr hf p a B]
  set G : FourierSpace m → ℝ≥0∞ :=
    (coordBall p r).indicator fun q => ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ with hG
  have hle : ‖∫ q, scaleKernel r (p - q) * (f q - (a + B (WithLp.ofLp q).1))‖ₑ ≤
      ∫⁻ q, ‖scaleKernel r (p - q)‖ₑ * G q := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun q => ?_)
    rw [enorm_mul, hG]
    by_cases hq : q ∈ coordBall p r
    · rw [indicator_of_mem hq]
    · rw [indicator_of_notMem hq, mul_zero, scaleKernel_sub_eq_zero hr hq, enorm_zero, zero_mul]
  have hFm : AEMeasurable (fun q => ‖scaleKernel r (p - q)‖ₑ) volume :=
    (continuous_scaleKernel_sub r p).measurable.enorm.aemeasurable
  have hGm : AEMeasurable G volume :=
    ((hf.aestronglyMeasurable.sub
      (continuous_const.add (continuous_linear_fst B)).aestronglyMeasurable).enorm).indicator
      (measurableSet_coordBall p r)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hFm hGm
  simp only [Pi.mul_apply] at hH
  have hF2 : ∫⁻ q, ‖scaleKernel r (p - q)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (scaleKernelEnergy m) * (ENNReal.ofReal r)⁻¹ ^ (m + 2) := by
    simp only [ENNReal.rpow_two]
    exact lintegral_scaleKernel_sub_sq hr p
  have hG2 : ∫⁻ q, G q ^ (2 : ℝ) =
      ∫⁻ q in coordBall p r, ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ ^ 2 := by
    rw [← lintegral_indicator (measurableSet_coordBall p r)]
    refine lintegral_congr fun q => ?_
    rw [hG, ENNReal.rpow_two]
    by_cases hq : q ∈ coordBall p r
    · rw [indicator_of_mem hq, indicator_of_mem hq]
    · rw [indicator_of_notMem hq, indicator_of_notMem hq]
      simp
  rw [hF2, hG2] at hH
  calc ‖∫ q, scaleKernel r (p - q) * (f q - (a + B (WithLp.ofLp q).1))‖ₑ ^ 2
      ≤ ((ENNReal.ofReal (scaleKernelEnergy m) * (ENNReal.ofReal r)⁻¹ ^ (m + 2)) ^ (1 / (2 : ℝ)) *
          (∫⁻ q in coordBall p r, ‖f q - (a + B (WithLp.ofLp q).1)‖ₑ ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ zero_le (hle.trans hH) 2
    _ = _ := by rw [mul_pow, rpow_half_sq, rpow_half_sq]

/-- After the infimum: `|(ψ_r ⋆ f)(p)|² ≤ ‖ψ_1‖₂² r² a_f(p,r)²`. -/
theorem enorm_smoothing_sq_le_affineEnergy {r : ℝ} (hr : 0 < r) {f : FourierSpace m → ℝ}
    (hf : LocallyIntegrable f volume) (p : FourierSpace m) :
    ‖smoothing r f p‖ₑ ^ 2 ≤
      ENNReal.ofReal (scaleKernelEnergy m) * ENNReal.ofReal r ^ 2 * affineEnergy f p r := by
  set K := ENNReal.ofReal (scaleKernelEnergy m) * (ENNReal.ofReal r)⁻¹ ^ (m + 2) with hK
  have hx0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hxt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hx0))
  have h1 : ‖smoothing r f p‖ₑ ^ 2 ≤ K * affineError f p r := by
    rcases eq_or_ne K 0 with h0 | h0
    · have := enorm_smoothing_sq_le hr hf p 0 0
      rw [← hK, h0, zero_mul] at this
      rw [h0, zero_mul]
      exact this
    · rw [affineError, ENNReal.mul_iInf_of_ne h0 hKt]
      refine le_iInf fun a => ?_
      rw [ENNReal.mul_iInf_of_ne h0 hKt]
      exact le_iInf fun B => enorm_smoothing_sq_le hr hf p a B
  have hx : ENNReal.ofReal r ^ 2 * (ENNReal.ofReal r)⁻¹ ^ (m + 4) =
      (ENNReal.ofReal r)⁻¹ ^ (m + 2) := by
    rw [show m + 4 = (m + 2) + 2 by omega, pow_add, mul_comm, mul_assoc, ← mul_pow,
      ENNReal.inv_mul_cancel hx0 hxt, one_pow, mul_one]
  calc ‖smoothing r f p‖ₑ ^ 2 ≤ K * affineError f p r := h1
    _ = _ := by
        rw [hK, ← hx, affineEnergy]
        ring

end ParabolicRectifiability.FourierAffine
