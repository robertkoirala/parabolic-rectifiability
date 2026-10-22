import ParabolicRectifiability.Analysis.FourierAffine.Estimate

/-! # Plancherel for finite combinations of translates

First step towards the parabolic Fourier affine-square inequality
(`ba1_fourier_affine_square_proof`). For a real `H ∈ L²(FourierSpace m)`, real coefficients `c_k` and translations `v_k`,
`∫ |∑_k c_k (H(x + v_k) - H(x))|² dx = ∫ |∑_k c_k (e(⟨v_k,ζ⟩) - 1)|² |Ĥ(ζ)|² dζ`,
where `Ĥ = 𝓕 (realLp hH)` is the L² Fourier transform and `e = Real.fourierChar` is the phase
of mathlib's `𝓕`. The inverse L² transform of the multiplied transform is identified with the
physical combination by testing against smooth compactly supported real functions, as in
`FourierAffine.lintegral_enorm_smoothing_sq`; no `L¹` hypothesis on `H` is used.
All helpers carry the prefix `b1fas_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology FourierTransform ContDiff SchwartzMap

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.FourierAffine ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

/-! ### Translated tests -/

theorem b1fas_contDiff_translate {g : FourierSpace m → ℝ} (hg : ContDiff ℝ ∞ g)
    (v : FourierSpace m) : ContDiff ℝ ∞ (fun y => g (y - v)) :=
  hg.comp (contDiff_id.sub contDiff_const)

theorem b1fas_hasCompactSupport_translate {g : FourierSpace m → ℝ} (hgc : HasCompactSupport g)
    (v : FourierSpace m) : HasCompactSupport (fun y => g (y - v)) :=
  hgc.comp_homeomorph (Homeomorph.subRight v)

theorem b1fas_continuous_char (v : FourierSpace m) :
    Continuous fun ζ : FourierSpace m => ((𝐞 (inner ℝ v ζ) : Circle) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id))

/-- The inverse Fourier transform of the translated test `y ↦ g (y - v)`. -/
theorem b1fas_fourierInv_translate (g : FourierSpace m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (v ζ : FourierSpace m) :
    (𝓕⁻ (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
        (b1fas_hasCompactSupport_translate hgc v)) : 𝓢(FourierSpace m, ℂ)) ζ =
      (𝐞 (inner ℝ v ζ) : ℂ) * (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ := by
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    Real.fourierInv_eq, ← integral_const_mul]
  simp only [realCompactTest_apply]
  have hs : ∫ x, 𝐞 (inner ℝ (x + v) ζ) • ((g (x + v - v) : ℝ) : ℂ) =
      ∫ y, 𝐞 (inner ℝ y ζ) • ((g (y - v) : ℝ) : ℂ) :=
    integral_add_right_eq_self (μ := volume)
      (fun y : FourierSpace m => 𝐞 (inner ℝ y ζ) • ((g (y - v) : ℝ) : ℂ)) v
  rw [← hs]
  congr 1
  funext x
  rw [add_sub_cancel_right, inner_add_left, AddChar.map_add_eq_mul, Circle.smul_def,
    Circle.smul_def, Circle.coe_mul, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Integrability -/

theorem b1fas_memLp_translate {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (v : FourierSpace m) : MemLp (fun x => H (x + v)) 2 volume :=
  hH.comp_measurePreserving (measurePreserving_add_right volume v)

theorem b1fas_integrable_test_translate {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (g : FourierSpace m → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : FourierSpace m) :
    Integrable (fun x => (g x : ℂ) * (H (x + v) : ℂ)) volume :=
  ((realCompactTest g hg hgc).memLp 2 volume).integrable_mul (b1fas_memLp_translate hH v).ofReal

theorem b1fas_memLp_char_mul (v : FourierSpace m) (ψ : 𝓢(FourierSpace m, ℂ)) :
    MemLp (fun ζ => (𝐞 (inner ℝ v ζ) : ℂ) * ψ ζ) 2 volume :=
  (ψ.memLp 2 volume).of_le ((b1fas_continuous_char v).mul ψ.continuous).aestronglyMeasurable
    (Eventually.of_forall fun ζ => by rw [norm_mul, Circle.norm_coe, one_mul])

/-! ### Testing identities -/

/-- Testing identity for one translate: `∫ g(x) H(x + v) dx = ∫ Ĥ(ζ) e(⟨v,ζ⟩) (𝓕⁻ g)(ζ) dζ`. -/
theorem b1fas_integral_test_translate {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (g : FourierSpace m → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : FourierSpace m) :
    ∫ x, (g x : ℂ) * (H (x + v) : ℂ) =
      ∫ ζ, (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
        ((𝐞 (inner ℝ v ζ) : ℂ) * (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ) := by
  have h1 : ∫ x, (g x : ℂ) * (H (x + v) : ℂ) =
      ∫ y, (H y : ℂ) * (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
        (b1fas_hasCompactSupport_translate hgc v)) y := by
    have hs : ∫ x, (H (x + v) : ℂ) * (realCompactTest (fun y => g (y - v))
          (b1fas_contDiff_translate hg v) (b1fas_hasCompactSupport_translate hgc v)) (x + v) =
        ∫ y, (H y : ℂ) * (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
          (b1fas_hasCompactSupport_translate hgc v)) y :=
      integral_add_right_eq_self (μ := volume) (fun y : FourierSpace m => (H y : ℂ) *
        (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
          (b1fas_hasCompactSupport_translate hgc v)) y) v
    rw [← hs]
    congr 1
    funext x
    simp only [realCompactTest_apply, add_sub_cancel_right]
    ring
  have h2 : ∫ y, (H y : ℂ) * (realCompactTest (fun y => g (y - v))
        (b1fas_contDiff_translate hg v) (b1fas_hasCompactSupport_translate hgc v)) y =
      l2Pairing m (realLp hH) ((realCompactTest (fun y => g (y - v))
        (b1fas_contDiff_translate hg v) (b1fas_hasCompactSupport_translate hgc v)).toLp 2 volume) := by
    rw [l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [coeFn_realLp hH, (realCompactTest (fun y => g (y - v))
        (b1fas_contDiff_translate hg v) (b1fas_hasCompactSupport_translate hgc v)).coeFn_toLp 2
        volume] with q hq1 hq2
    rw [hq1, hq2]
  have hFF : 𝓕⁻ (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) = realLp hH :=
    (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm_apply_apply _
  have h3 : l2Pairing m (realLp hH) ((realCompactTest (fun y => g (y - v))
        (b1fas_contDiff_translate hg v) (b1fas_hasCompactSupport_translate hgc v)).toLp 2 volume) =
      l2Pairing m (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m)))
        ((𝓕⁻ (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
          (b1fas_hasCompactSupport_translate hgc v))).toLp 2 volume) := by
    conv_lhs => rw [← hFF]
    rw [l2Pairing_fourierInv_left, SchwartzMap.toLp_fourierInv_eq]
  have h4 : l2Pairing m (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m)))
        ((𝓕⁻ (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
          (b1fas_hasCompactSupport_translate hgc v))).toLp 2 volume) =
      ∫ ζ, (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
        (𝓕⁻ (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
          (b1fas_hasCompactSupport_translate hgc v)) : 𝓢(FourierSpace m, ℂ)) ζ := by
    rw [l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [(𝓕⁻ (realCompactTest (fun y => g (y - v)) (b1fas_contDiff_translate hg v)
        (b1fas_hasCompactSupport_translate hgc v))).coeFn_toLp 2 volume] with ζ hζ
    rw [hζ]
  rw [h1, h2, h3, h4]
  congr 1
  funext ζ
  rw [b1fas_fourierInv_translate]

/-- The multiplier `∑_k c_k (e(⟨v_k,ζ⟩) - 1)` of `x ↦ ∑_k c_k (H(x + v_k) - H x)`. -/
def b1fas_mult {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → FourierSpace m)
    (ζ : FourierSpace m) : ℂ :=
  ∑ k ∈ s, (c k : ℂ) * ((𝐞 (inner ℝ (v k) ζ) : ℂ) - 1)

theorem b1fas_continuous_mult {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → FourierSpace m) :
    Continuous (b1fas_mult s c v) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul ((b1fas_continuous_char (v k)).sub continuous_const)

theorem b1fas_norm_mult_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → FourierSpace m)
    (ζ : FourierSpace m) : ‖b1fas_mult s c v ζ‖ ≤ ∑ k ∈ s, 2 * |c k| := by
  unfold b1fas_mult
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖((𝐞 (inner ℝ (v k) ζ) : ℂ) - 1)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [Circle.norm_coe, norm_one]; norm_num)
  calc |c k| * ‖((𝐞 (inner ℝ (v k) ζ) : ℂ) - 1)‖ ≤ |c k| * 2 :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = 2 * |c k| := mul_comm _ _

/-- Testing identity for a finite combination of translate differences. -/
theorem b1fas_integral_test_comb {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → FourierSpace m) {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume)
    (g : FourierSpace m → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, (g x : ℂ) * ((∑ k ∈ s, c k * (H (x + v k) - H x) : ℝ) : ℂ) =
      ∫ ζ, (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
        (b1fas_mult s c v ζ * (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ) := by
  have hzero : ∫ x, (g x : ℂ) * (H x : ℂ) =
      ∫ ζ, (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
        (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ := by
    have h := b1fas_integral_test_translate hH g hg hgc 0
    simp only [add_zero, inner_zero_left, AddChar.map_zero_eq_one, Circle.coe_one, one_mul] at h
    exact h
  have hiP0 : Integrable (fun x => (g x : ℂ) * (H x : ℂ)) volume := by
    simpa using b1fas_integrable_test_translate hH g hg hgc 0
  have hiF : ∀ w : FourierSpace m, Integrable (fun ζ =>
      (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
        ((𝐞 (inner ℝ w ζ) : ℂ) * (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ))
      volume := fun w =>
    (Lp.memLp _).integrable_mul (b1fas_memLp_char_mul w _)
  have hiF0 : Integrable (fun ζ =>
      (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
        (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ) volume :=
    (Lp.memLp _).integrable_mul ((𝓕⁻ (realCompactTest g hg hgc)).memLp 2 volume)
  calc ∫ x, (g x : ℂ) * ((∑ k ∈ s, c k * (H (x + v k) - H x) : ℝ) : ℂ)
      = ∫ x, ∑ k ∈ s, (c k : ℂ) * ((g x : ℂ) * (H (x + v k) : ℂ) - (g x : ℂ) * (H x : ℂ)) := by
        congr 1
        funext x
        push_cast
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k ∈ s, (c k : ℂ) * ((∫ x, (g x : ℂ) * (H (x + v k) : ℂ)) -
          ∫ x, (g x : ℂ) * (H x : ℂ)) := by
        rw [integral_finsetSum s (f := fun k x =>
            (c k : ℂ) * ((g x : ℂ) * (H (x + v k) : ℂ) - (g x : ℂ) * (H x : ℂ))) fun k _ =>
          ((b1fas_integrable_test_translate hH g hg hgc (v k)).sub hiP0).const_mul (c k : ℂ)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, integral_sub (b1fas_integrable_test_translate hH g hg hgc (v k))
          hiP0]
    _ = ∑ k ∈ s, (c k : ℂ) * ((∫ ζ, (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
          ((𝐞 (inner ℝ (v k) ζ) : ℂ) * (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ)) -
          ∫ ζ, (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
            (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [b1fas_integral_test_translate hH g hg hgc (v k), hzero]
    _ = ∫ ζ, ∑ k ∈ s, (c k : ℂ) *
          ((𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
            ((𝐞 (inner ℝ (v k) ζ) : ℂ) * (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ) -
          (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
            (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ) := by
        rw [integral_finsetSum s (f := fun k ζ => (c k : ℂ) *
            ((𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
              ((𝐞 (inner ℝ (v k) ζ) : ℂ) * (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ) -
            (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
              (𝓕⁻ (realCompactTest g hg hgc) : 𝓢(FourierSpace m, ℂ)) ζ)) fun k _ =>
          ((hiF (v k)).sub hiF0).const_mul (c k : ℂ)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, integral_sub (hiF (v k)) hiF0]
    _ = _ := by
        congr 1
        funext ζ
        simp only [b1fas_mult, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-! ### Plancherel -/

/-- **Plancherel for finite combinations of translate differences.** For real `H ∈ L²`,
`∫ |∑_k c_k (H(x + v_k) - H x)|² dx = ∫ |∑_k c_k (e(⟨v_k,ζ⟩) - 1)|² |Ĥ(ζ)|² dζ`. -/
theorem b1fas_lintegral_comb_sq {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → FourierSpace m) {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    ∫⁻ x, ‖∑ k ∈ s, c k * (H (x + v k) - H x)‖ₑ ^ 2 =
      ∫⁻ ζ, ‖b1fas_mult s c v ζ‖ₑ ^ 2 *
        ‖(𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
  have hGm : MemLp (fun ζ => b1fas_mult s c v ζ *
      (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ) 2 volume :=
    (Lp.memLp (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m)))).of_le_mul
      (c := ∑ k ∈ s, 2 * |c k|)
      ((b1fas_continuous_mult s c v).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun ζ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (b1fas_norm_mult_le s c v ζ) (norm_nonneg _))
  have hphys : MemLp (fun x => ∑ k ∈ s, c k * (H (x + v k) - H x)) 2 volume :=
    memLp_finsetSum s fun k _ => ((b1fas_memLp_translate hH (v k)).sub hH).const_mul (c k)
  have hae : ∀ᵐ p ∂volume, (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) p =
      ((∑ k ∈ s, c k * (H (p + v k) - H p) : ℝ) : ℂ) := by
    apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
      (hphys.ofReal.locallyIntegrable (by norm_num))
    intro g hg hgc
    simp only [Complex.real_smul]
    rw [b1fas_integral_test_comb s c v hH g hg hgc]
    have h1 : ∫ x, (g x : ℂ) * (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x =
        l2Pairing m (𝓕⁻ (hGm.toLp _)) ((realCompactTest g hg hgc).toLp 2 volume) := by
      rw [l2Pairing_apply]
      apply integral_congr_ae
      filter_upwards [(realCompactTest g hg hgc).coeFn_toLp 2 volume] with x hx
      rw [hx, realCompactTest_apply, mul_comm]
    rw [h1, l2Pairing_fourierInv_left, SchwartzMap.toLp_fourierInv_eq, l2Pairing_apply]
    apply integral_congr_ae
    filter_upwards [hGm.coeFn_toLp, (𝓕⁻ (realCompactTest g hg hgc)).coeFn_toLp 2 volume]
      with ζ h1 h2
    rw [h1, h2]
    ring
  have hHn : ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ =
      ‖hGm.toLp _‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact congrArg _ ((Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).symm.nnnorm_map _)
  calc ∫⁻ x, ‖∑ k ∈ s, c k * (H (x + v k) - H x)‖ₑ ^ 2
      = ∫⁻ p, ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) p‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [hae] with p hp
        rw [hp, enorm_complex_ofReal]
    _ = ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m)))‖ₑ ^ 2 := by
        rw [lintegral_enorm_sq_eq (Lp.aestronglyMeasurable _), Lp.enorm_def]
    _ = ‖hGm.toLp _‖ₑ ^ 2 := by rw [hHn]
    _ = ∫⁻ ζ, ‖b1fas_mult s c v ζ *
          (𝓕 (realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ‖ₑ ^ 2 := by
        rw [Lp.enorm_def, eLpNorm_congr_ae hGm.coeFn_toLp,
          ← lintegral_enorm_sq_eq hGm.aestronglyMeasurable]
    _ = _ := by simp only [enorm_mul, mul_pow]

end ParabolicRectifiability.Characterization
