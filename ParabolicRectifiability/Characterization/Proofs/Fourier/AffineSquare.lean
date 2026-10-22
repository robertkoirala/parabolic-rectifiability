import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Characterization.Proofs.Fourier.AffineSquareMultiplier

/-! # The parabolic Fourier affine-square inequality

This file proves `ba1_fourier_affine_square_proof : FourierAffineSquareStatement`: the parabolic
affine Carleson energy of a real `H ∈ L²` is bounded by `C ∫ (|ξ|² + |τ|) |Ĥ|²`.

**Route.** For every centre `p` and scale `r > 0` test the affine competitor
`a + B·u` with `a + B·u_p = H(p)` and the finite-difference gradient
`B_j = (H(p + r e_j) - H(p)) / r` (`b1fas_grad`). For `q = p + w ∈ P_b(p,r)` the residual
`H(q) - a - B·u_q` is the finite combination of translate differences `b1fas_resid H r w p`.
Hence `affineError H p r ≤ ∫_{P_b(0,r)} |b1fas_resid H r w p|² dw` for every `p`.
Tonelli, Plancherel for translate combinations (`b1fas_lintegral_comb_sq`), the multiplier bound
`|M| ≤ K_m min(1, r²(|ξ|² + |τ|))` on the testing ball (`b1fas_norm_mult_le_min`), the exact volume
`|P_b(0,r)| = r^{m+2} |P_b(0,1)|` and the scale integral
`∫_0^∞ r^{-2} min(1, r²a)² dr/r ≤ a` give
`affineCarlesonEnergy H ≤ |P_b(0,1)| K_m² ∫ (|ξ|² + |τ|) |Ĥ|²`.
The argument works directly for every real `H ∈ L²` (both sides in `[0,∞]`): no Schwartz
approximation, no Fatou step, and no smoothing kernel (in particular not
`FourierAffine.smoothing`). A non-measurable representative is first replaced by a measurable
one; neither side changes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.FourierAffine ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

/-! ### The competitor and its residual -/

/-- The finite-difference gradient `B_j = (H(p + r e_j) - H(p)) / r` at the centre `p`. -/
def b1fas_grad (H : FourierSpace m → ℝ) (r : ℝ) (p : FourierSpace m) : Spatial m →L[ℝ] ℝ :=
  ∑ j : Fin m, ((H (p + r • b1fas_unit j) - H p) / r) • EuclideanSpace.proj j

theorem b1fas_grad_apply (H : FourierSpace m → ℝ) (r : ℝ) (p : FourierSpace m)
    (v : Spatial m) :
    b1fas_grad H r p v = ∑ j : Fin m, (H (p + r • b1fas_unit j) - H p) / r * v j := by
  simp [b1fas_grad]

/-- The residual `H(p + w) - H(p) - ∑_j (w_j / r) (H(p + r e_j) - H(p))`. -/
def b1fas_resid (H : FourierSpace m → ℝ) (r : ℝ) (w p : FourierSpace m) : ℝ :=
  ∑ k : Option (Fin m), b1fas_coef r w k * (H (p + b1fas_vec r w k) - H p)

theorem b1fas_resid_eq (H : FourierSpace m → ℝ) (r : ℝ) (w p : FourierSpace m) :
    H (p + w) - ((H p - b1fas_grad H r p (WithLp.ofLp p).1) +
        b1fas_grad H r p (WithLp.ofLp (p + w)).1) = b1fas_resid H r w p := by
  rw [WithLp.ofLp_add, Prod.fst_add, map_add, b1fas_grad_apply H r p (WithLp.ofLp w).1]
  simp only [b1fas_resid, Fintype.sum_option, b1fas_coef, b1fas_vec, one_mul]
  have hs : ∑ j : Fin m, -((WithLp.ofLp w).1 j / r) * (H (p + r • b1fas_unit j) - H p) =
      -∑ j : Fin m, (H (p + r • b1fas_unit j) - H p) / r * (WithLp.ofLp w).1 j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  ring

theorem b1fas_add_mem_coordBall {p w : FourierSpace m} {r : ℝ} :
    p + w ∈ coordBall p r ↔ w ∈ coordBall 0 r := by
  simp [coordBall]

/-- **The pointwise competitor bound.** -/
theorem b1fas_affineError_le (H : FourierSpace m → ℝ) (p : FourierSpace m) (r : ℝ) :
    affineError H p r ≤ ∫⁻ w in coordBall 0 r, ‖b1fas_resid H r w p‖ₑ ^ 2 := by
  unfold affineError
  refine (iInf₂_le (H p - b1fas_grad H r p (WithLp.ofLp p).1) (b1fas_grad H r p)).trans
    (le_of_eq ?_)
  rw [← lintegral_indicator (measurableSet_coordBall p r),
    ← lintegral_indicator (measurableSet_coordBall 0 r),
    ← lintegral_add_left_eq_self ((coordBall p r).indicator fun q =>
      ‖H q - ((H p - b1fas_grad H r p (WithLp.ofLp p).1) +
        b1fas_grad H r p (WithLp.ofLp q).1)‖ₑ ^ 2) p]
  congr 1
  funext w
  by_cases hw : w ∈ coordBall 0 r
  · rw [indicator_of_mem (b1fas_add_mem_coordBall.2 hw), indicator_of_mem hw, b1fas_resid_eq]
  · rw [indicator_of_notMem (fun h => hw (b1fas_add_mem_coordBall.1 h)), indicator_of_notMem hw]

theorem b1fas_affineCarlesonEnergy_congr {H H' : FourierSpace m → ℝ}
    (h : H =ᵐ[volume] H') : affineCarlesonEnergy H = affineCarlesonEnergy H' := by
  have he : ∀ p r, affineError H p r = affineError H' p r := by
    intro p r
    unfold affineError
    refine iInf_congr fun a => iInf_congr fun B => lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae h] with q hq
    rw [hq]
  simp only [affineCarlesonEnergy, affineEnergy, he]

/-! ### Measurability -/

theorem b1fas_measurable_resid {H : FourierSpace m → ℝ} (hH : Measurable H) :
    Measurable fun x : (FourierSpace m × ℝ) × FourierSpace m =>
      b1fas_resid H x.1.2 x.2 x.1.1 := by
  unfold b1fas_resid
  refine Finset.measurable_sum _ fun k _ => ?_
  cases k with
  | none =>
    simp only [b1fas_coef, b1fas_vec, one_mul]
    exact (hH.comp (continuous_fst.fst.add continuous_snd).measurable).sub
      (hH.comp measurable_fst.fst)
  | some j =>
    simp only [b1fas_coef, b1fas_vec]
    have hc : Measurable fun x : (FourierSpace m × ℝ) × FourierSpace m =>
        (WithLp.ofLp x.2).1 j :=
      ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp
        ((WithLp.fstL 2 ℝ (Spatial m) ℝ).continuous.comp continuous_snd)).measurable
    exact ((hc.div measurable_fst.snd).neg).mul
      ((hH.comp (continuous_fst.fst.add
        (continuous_fst.snd.smul continuous_const)).measurable).sub (hH.comp measurable_fst.fst))

theorem b1fas_measurableSet_graph :
    MeasurableSet {x : (FourierSpace m × ℝ) × FourierSpace m | x.2 ∈ coordBall 0 x.1.2} := by
  simp only [b1fas_mem_coordBall_zero]
  exact (measurableSet_lt (((WithLp.fstL 2 ℝ (Spatial m) ℝ).continuous.comp
      continuous_snd).norm.measurable) measurable_fst.snd).inter
    (measurableSet_lt (((WithLp.sndL 2 ℝ (Spatial m) ℝ).continuous.comp
      continuous_snd).abs.measurable) (measurable_fst.snd.pow_const 2))

theorem b1fas_measurable_integrand {H : FourierSpace m → ℝ} (hH : Measurable H) :
    Measurable fun y : (FourierSpace m × ℝ) × FourierSpace m =>
      (coordBall 0 y.1.2).indicator (fun w => ‖b1fas_resid H y.1.2 w y.1.1‖ₑ ^ 2) y.2 := by
  have heq : (fun y : (FourierSpace m × ℝ) × FourierSpace m =>
      (coordBall 0 y.1.2).indicator (fun w => ‖b1fas_resid H y.1.2 w y.1.1‖ₑ ^ 2) y.2) =
      {y : (FourierSpace m × ℝ) × FourierSpace m | y.2 ∈ coordBall 0 y.1.2}.indicator
        (fun y => ‖b1fas_resid H y.1.2 y.2 y.1.1‖ₑ ^ 2) := by
    funext y
    by_cases hy : y.2 ∈ coordBall 0 y.1.2
    · rw [indicator_of_mem hy, indicator_of_mem
        (show y ∈ {y : (FourierSpace m × ℝ) × FourierSpace m | y.2 ∈ coordBall 0 y.1.2} from hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem
        (show y ∉ {y : (FourierSpace m × ℝ) × FourierSpace m | y.2 ∈ coordBall 0 y.1.2} from hy)]
  rw [heq]
  exact ((b1fas_measurable_resid hH).enorm.pow_const 2).indicator b1fas_measurableSet_graph

/-! ### Volumes of the testing balls -/

theorem b1fas_volume_coordBall_one_lt_top :
    volume (coordBall (0 : FourierSpace m) 1) < ⊤ := by
  refine (measure_mono (show coordBall (0 : FourierSpace m) 1 ⊆ Metric.ball 0 3 from
    fun w hw => ?_)).trans_lt MeasureTheory.measure_ball_lt_top
  obtain ⟨h1, h2⟩ := b1fas_mem_coordBall_zero.1 hw
  rw [Metric.mem_ball, dist_zero_right]
  have := norm_le_of_coords w h1.le h2.le
  norm_num at this
  linarith

theorem b1fas_volume_coordBall {r : ℝ} (hr : 0 < r) :
    volume (coordBall (0 : FourierSpace m) r) =
      ENNReal.ofReal (r ^ (m + 2)) * volume (coordBall (0 : FourierSpace m) 1) := by
  have h := FourierAffine.lintegral_comp_dilate_inv (m := m) hr
    ((coordBall (0 : FourierSpace m) 1).indicator 1)
  rw [lintegral_indicator_one (measurableSet_coordBall 0 1)] at h
  have hmem : ∀ z : FourierSpace m,
      FourierAffine.dilate r⁻¹ z ∈ coordBall (0 : FourierSpace m) 1 ↔
        z ∈ coordBall (0 : FourierSpace m) r := by
    intro z
    rw [b1fas_mem_coordBall_zero, b1fas_mem_coordBall_zero, FourierAffine.ofLp_dilate]
    simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, abs_mul, abs_pow, one_pow]
    rw [inv_mul_lt_iff₀ hr, inv_pow, inv_mul_lt_iff₀ (by positivity : (0 : ℝ) < r ^ 2), mul_one,
      mul_one]
  have hset : (fun z : FourierSpace m =>
      (coordBall (0 : FourierSpace m) 1).indicator (1 : FourierSpace m → ℝ≥0∞)
        (FourierAffine.dilate r⁻¹ z)) =
      (coordBall (0 : FourierSpace m) r).indicator 1 := by
    funext z
    by_cases hz : z ∈ coordBall (0 : FourierSpace m) r
    · rw [indicator_of_mem ((hmem z).2 hz), indicator_of_mem hz, Pi.one_apply, Pi.one_apply]
    · rw [indicator_of_notMem (fun h => hz ((hmem z).1 h)), indicator_of_notMem hz]
  rw [hset, lintegral_indicator_one (measurableSet_coordBall 0 r)] at h
  exact h

/-! ### Plancherel at a fixed scale and increment -/

theorem b1fas_resid_plancherel {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) (r : ℝ)
    (w : FourierSpace m) :
    ∫⁻ p, ‖b1fas_resid H r w p‖ₑ ^ 2 =
      ∫⁻ ζ, ‖b1fas_mult Finset.univ (b1fas_coef r w) (b1fas_vec r w) ζ‖ₑ ^ 2 *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 :=
  b1fas_lintegral_comb_sq Finset.univ (b1fas_coef r w) (b1fas_vec r w) hH

/-- The frequency weight `|ξ|² + |τ|`. -/
def b1fas_amp (ζ : FourierSpace m) : ℝ := ‖(WithLp.ofLp ζ).1‖ ^ 2 + |(WithLp.ofLp ζ).2|

theorem b1fas_amp_nonneg (ζ : FourierSpace m) : 0 ≤ b1fas_amp ζ := by
  unfold b1fas_amp
  positivity

theorem b1fas_continuous_amp : Continuous (b1fas_amp (m := m)) :=
  (((WithLp.fstL 2 ℝ (Spatial m) ℝ).continuous).norm.pow 2).add
    ((WithLp.sndL 2 ℝ (Spatial m) ℝ).continuous.abs)

theorem b1fas_ennreal_alg (A B I V D : ℝ≥0∞) (h : A * B = D) :
    A * (I * (B * V)) = V * (D * I) := by
  rw [← h]
  ring

theorem b1fas_pow_identity {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal r)⁻¹ ^ (m + 4) * ENNReal.ofReal (r ^ (m + 2)) =
      (ENNReal.ofReal r)⁻¹ ^ 2 := by
  have hx0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  rw [ENNReal.ofReal_pow hr.le, show m + 4 = 2 + (m + 2) by ring,
    pow_add (ENNReal.ofReal r)⁻¹ 2 (m + 2), mul_assoc,
    ← mul_pow (ENNReal.ofReal r)⁻¹ (ENNReal.ofReal r) (m + 2),
    ENNReal.inv_mul_cancel hx0 ENNReal.ofReal_ne_top, one_pow, mul_one]

theorem b1fas_measurable_slice {H : FourierSpace m → ℝ} (hHm : Measurable H) (r : ℝ) :
    Measurable (Function.uncurry fun (p w : FourierSpace m) =>
      (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w) := by
  have hg : Measurable fun z : FourierSpace m × FourierSpace m => ((z.1, r), z.2) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hcomp := (b1fas_measurable_integrand hHm).comp hg
  exact hcomp

theorem b1fas_measurable_slice_p {H : FourierSpace m → ℝ} (hHm : Measurable H) (r : ℝ) :
    Measurable fun p : FourierSpace m =>
      ∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w := by
  have hpm0 := (b1fas_measurable_slice hHm r).lintegral_prod_right' (ν := volume)
  exact hpm0

/-- Tonelli in `(p, w)` at a fixed scale. -/
theorem b1fas_slice_swap {H : FourierSpace m → ℝ} (hHm : Measurable H) (r : ℝ) (c : ℝ≥0∞) :
    ∫⁻ p, c * ∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w =
      c * ∫⁻ w, ∫⁻ p, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w := by
  have hmeas2 := b1fas_measurable_slice hHm r
  have hpm := b1fas_measurable_slice_p hHm r
  calc ∫⁻ p, c * ∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w
      = c * ∫⁻ p, ∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w :=
        lintegral_const_mul c hpm
    _ = c * ∫⁻ w, ∫⁻ p, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w :=
        congrArg (fun X => c * X)
          (lintegral_lintegral_swap (μ := volume) (ν := volume) hmeas2.aemeasurable)

/-- Plancherel and the multiplier bound at a fixed increment. -/
theorem b1fas_slice_inner {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) {r : ℝ}
    (hr : 0 < r) (w : FourierSpace m) :
    ∫⁻ p, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w ≤
      (coordBall (0 : FourierSpace m) r).indicator (fun _ =>
        ∫⁻ ζ, ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) w := by
  by_cases hw : w ∈ coordBall 0 r
  · rw [indicator_of_mem hw]
    simp only [indicator_of_mem hw]
    rw [b1fas_resid_plancherel hH r w]
    exact lintegral_mono fun ζ => mul_le_mul_left (b1fas_enorm_mult_sq_le hr hw ζ) _
  · rw [indicator_of_notMem hw]
    simp only [indicator_of_notMem hw, lintegral_zero, le_refl]

/-- The `p`-integral at a fixed scale `r > 0`. -/
theorem b1fas_scale_slice {H : FourierSpace m → ℝ} (hHm : Measurable H)
    (hH : MemLp H 2 volume) {r : ℝ} (hr : 0 < r) :
    ∫⁻ p, (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
        ∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w ≤
      volume (coordBall (0 : FourierSpace m) 1) *
        ∫⁻ ζ, (ENNReal.ofReal r)⁻¹ ^ 2 *
          ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) *
          ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  have hfin : (ENNReal.ofReal r)⁻¹ ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne')
  rw [b1fas_slice_swap hHm r]
  refine (mul_le_mul_right (lintegral_mono (b1fas_slice_inner hH hr)) _).trans (le_of_eq ?_)
  rw [lintegral_indicator_const (measurableSet_coordBall 0 r), b1fas_volume_coordBall hr,
    b1fas_ennreal_alg _ _ _ _ _ (b1fas_pow_identity hr), ← lintegral_const_mul' _ _ hfin]
  simp only [mul_assoc]

/-- The scale integral at a fixed frequency. -/
theorem b1fas_scale_frequency (ζ : FourierSpace m) :
    ∫⁻ r, (ENNReal.ofReal r)⁻¹ ^ 2 *
        ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) ∂scaleMeasure ≤
      ENNReal.ofReal (b1fas_K m ^ 2) * ENNReal.ofReal (b1fas_amp ζ) := by
  have h : ∀ r : ℝ, (ENNReal.ofReal r)⁻¹ ^ 2 *
      ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) =
      ENNReal.ofReal (b1fas_K m ^ 2) * ((ENNReal.ofReal r)⁻¹ ^ 2 *
        ENNReal.ofReal (min 1 (r ^ 2 * b1fas_amp ζ) ^ 2)) := by
    intro r
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  simp only [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_right (b1fas_lintegral_scale_le (b1fas_amp_nonneg ζ)) _

/-! ### Assembly -/

/-- The inequality for a measurable representative. -/
theorem b1fas_main {H : FourierSpace m → ℝ} (hHm : Measurable H) (hH : MemLp H 2 volume) :
    affineCarlesonEnergy H ≤
      ENNReal.ofReal ((volume (coordBall (0 : FourierSpace m) 1)).toReal * b1fas_K m ^ 2) *
        parabolicFourierEnergy hH := by
  have hVt : volume (coordBall (0 : FourierSpace m) 1) ≠ ⊤ :=
    b1fas_volume_coordBall_one_lt_top.ne
  have hpos : ∀ᵐ r ∂scaleMeasure, 0 < r := by
    rw [ae_iff]
    have hs : {r : ℝ | ¬ 0 < r} = (Ioi 0)ᶜ := by
      ext r
      simp
    rw [hs]
    exact scaleMeasure_compl_positive
  have hΦm : Measurable (Function.uncurry fun (p : FourierSpace m) (r : ℝ) =>
      (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
        ∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w) :=
    ((ENNReal.measurable_ofReal.comp measurable_snd).inv.pow_const _).mul
      (b1fas_measurable_integrand hHm).lintegral_prod_right'
  have hc : Continuous fun x : ℝ × FourierSpace m =>
      b1fas_K m ^ 2 * min 1 (x.1 ^ 2 * b1fas_amp x.2) ^ 2 :=
    continuous_const.mul ((continuous_const.min ((continuous_fst.pow 2).mul
      (b1fas_continuous_amp.comp continuous_snd))).pow 2)
  have hΨm : Measurable (Function.uncurry fun (r : ℝ) (ζ : FourierSpace m) =>
      (ENNReal.ofReal r)⁻¹ ^ 2 *
        ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) :=
    (((ENNReal.measurable_ofReal.comp measurable_fst).inv.pow_const 2).mul
      (ENNReal.measurable_ofReal.comp hc.measurable)).mul
      (((Lp.stronglyMeasurable (𝓕 (realLp hH) :
        Lp ℂ 2 (volume : Measure (FourierSpace m)))).measurable.enorm.pow_const 2).comp
        measurable_snd)
  have hrm : ∀ ζ : FourierSpace m, Measurable fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ 2 *
      ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) := fun ζ =>
    (ENNReal.measurable_ofReal.inv.pow_const 2).mul (ENNReal.measurable_ofReal.comp
      (hc.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => ζ))).measurable)
  calc affineCarlesonEnergy H
      ≤ ∫⁻ p, ∫⁻ r, (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
          (∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w)
            ∂scaleMeasure := by
        unfold affineCarlesonEnergy
        refine lintegral_mono fun p => lintegral_mono fun r => ?_
        unfold affineEnergy
        rw [lintegral_indicator (measurableSet_coordBall 0 r)]
        exact mul_le_mul_right (b1fas_affineError_le H p r) _
    _ = ∫⁻ r, ∫⁻ p, (ENNReal.ofReal r)⁻¹ ^ (m + 4) *
          (∫⁻ w, (coordBall 0 r).indicator (fun w => ‖b1fas_resid H r w p‖ₑ ^ 2) w)
            ∂volume ∂scaleMeasure :=
        lintegral_lintegral_swap hΦm.aemeasurable
    _ ≤ ∫⁻ r, volume (coordBall (0 : FourierSpace m) 1) *
          (∫⁻ ζ, (ENNReal.ofReal r)⁻¹ ^ 2 *
            ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) *
            ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2)
              ∂scaleMeasure := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpos] with r hr
        exact b1fas_scale_slice hHm hH hr
    _ = volume (coordBall (0 : FourierSpace m) 1) * ∫⁻ ζ, ∫⁻ r, (ENNReal.ofReal r)⁻¹ ^ 2 *
            ENNReal.ofReal (b1fas_K m ^ 2 * min 1 (r ^ 2 * b1fas_amp ζ) ^ 2) *
            ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2
              ∂scaleMeasure := by
        rw [lintegral_const_mul' _ _ hVt, lintegral_lintegral_swap hΨm.aemeasurable]
    _ ≤ volume (coordBall (0 : FourierSpace m) 1) * ∫⁻ ζ, ENNReal.ofReal (b1fas_K m ^ 2) *
            ENNReal.ofReal (b1fas_amp ζ) *
            ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
        refine mul_le_mul_right (lintegral_mono fun ζ => ?_) _
        rw [lintegral_mul_const _ (hrm ζ)]
        exact mul_le_mul_left (b1fas_scale_frequency ζ) _
    _ = ENNReal.ofReal ((volume (coordBall (0 : FourierSpace m) 1)).toReal * b1fas_K m ^ 2) *
          parabolicFourierEnergy hH := by
        have hpt : ∀ ζ : FourierSpace m, ENNReal.ofReal (b1fas_K m ^ 2) *
            ENNReal.ofReal (b1fas_amp ζ) *
            ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 =
            ENNReal.ofReal (b1fas_K m ^ 2) * ((ENNReal.ofReal (‖(WithLp.ofLp ζ).1‖ ^ 2) +
              ENNReal.ofReal |(WithLp.ofLp ζ).2|) *
              ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2) := by
          intro ζ
          rw [b1fas_amp, ENNReal.ofReal_add (sq_nonneg _) (abs_nonneg _), mul_assoc]
        simp only [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt,
          parabolicFourierEnergy]

/-- **The parabolic Fourier affine-square inequality** (`FourierAffineSquareStatement`). For every `m` there is `C > 0` such that every real `H ∈ L²`
satisfies `affineCarlesonEnergy H ≤ C ∫ (|ξ|² + |τ|) |Ĥ|²`; here
`C = |P_b(0,1)| (38π² + 2m + 2)² + 1`. -/
theorem ba1_fourier_affine_square_proof : FourierAffineSquareStatement := by
  intro m
  refine ⟨(volume (coordBall (0 : FourierSpace m) 1)).toReal * b1fas_K m ^ 2 + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) one_pos, ?_⟩
  intro H hH
  have hHH' : H =ᵐ[volume] hH.aestronglyMeasurable.mk H := hH.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable (hH.aestronglyMeasurable.mk H) :=
    hH.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hH2 : MemLp (hH.aestronglyMeasurable.mk H) 2 volume := hH.ae_eq hHH'
  have hR : realLp hH = realLp hH2 := by
    unfold realLp
    exact MemLp.toLp_congr _ _ (hHH'.fun_comp fun x : ℝ => (x : ℂ))
  have hP : parabolicFourierEnergy hH = parabolicFourierEnergy hH2 := by
    simp only [parabolicFourierEnergy, hR]
  rw [b1fas_affineCarlesonEnergy_congr hHH', hP]
  refine (b1fas_main hm hH2).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  linarith

end ParabolicRectifiability.Characterization
