import ParabolicRectifiability.Analysis.FourierAffine.Estimate

/-! # Plancherel for finite combinations of spatial translates

First step towards the spatial affine-square estimate (`ba1_spatial_affine_square_proof`). For a real `G ∈ L²(ℝ^k)` (`ℝ^k = Spatial k`), real coefficients `c_i` and translations `v_i`,
`∫ |∑_i c_i (G(x + v_i) - G(x))|² dx = ∫ |∑_i c_i (e(⟨v_i,ξ⟩) - 1)|² |Ĝ(ξ)|² dξ`,
where `Ĝ = 𝓕 (b1sas_realLp hG)` is mathlib's L² Fourier transform of the complexification and
`e = Real.fourierChar` is the phase of mathlib's `𝓕`. The inverse L² transform of the multiplied
transform is identified with the physical combination by testing against smooth compactly
supported real functions; no `L¹` hypothesis on `G` is used.

This is the spatial transcription of `b1fas_lintegral_comb_sq` (on `FourierSpace m`); the
bilinear pairing, the complexification and the compact tests of the `HalfTimeDerivative`
namespace exist only on `FourierSpace m`, so their spatial versions are restated here. All helpers carry
the prefix `b1sas_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology FourierTransform ContDiff SchwartzMap

namespace ParabolicRectifiability.Characterization

variable {k : ℕ}

/-! ### The bilinear `L²` pairing on `Spatial k` -/

/-- Continuous complex-bilinear integration on complex `L²(ℝ^k)` (no conjugation). -/
def b1sas_pair (k : ℕ) :
    Lp ℂ 2 (volume : Measure (Spatial k)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Spatial k)) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2

theorem b1sas_pair_apply (f g : Lp ℂ 2 (volume : Measure (Spatial k))) :
    b1sas_pair k f g = ∫ x, f x * g x :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral f g

theorem b1sas_pair_toLp (f : Lp ℂ 2 (volume : Measure (Spatial k)))
    (η : 𝓢(Spatial k, ℂ)) :
    b1sas_pair k f (η.toLp 2 volume) = (f : 𝓢'(Spatial k, ℂ)) η := by
  rw [b1sas_pair_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [η.coeFn_toLp 2 volume] with x hx
  simp [hx, mul_comm]

/-- The inverse Fourier transform is symmetric for the bilinear `L²` pairing. -/
theorem b1sas_pair_fourierInv_left (f g : Lp ℂ 2 (volume : Measure (Spatial k))) :
    b1sas_pair k (𝓕⁻ f) g = b1sas_pair k f (𝓕⁻ g) := by
  apply DenseRange.induction_on (p := fun g =>
    b1sas_pair k (𝓕⁻ f) g = b1sas_pair k f (𝓕⁻ g))
    (SchwartzMap.denseRange_toLpCLM (E := Spatial k) (F := ℂ)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) g
  · exact isClosed_eq (b1sas_pair k (𝓕⁻ f)).continuous
      ((b1sas_pair k f).continuous.comp FourierTransform.continuous_fourierInv)
  intro η
  change b1sas_pair k (𝓕⁻ f) (η.toLp 2 volume) =
    b1sas_pair k f (𝓕⁻ (η.toLp 2 volume))
  rw [SchwartzMap.toLp_fourierInv_eq, b1sas_pair_toLp, b1sas_pair_toLp]
  exact congrArg (fun T : 𝓢'(Spatial k, ℂ) => T η)
    (Lp.fourierInv_toTemperedDistribution_eq f).symm

/-! ### Complexification and compact tests -/

/-- Complexification of a real `L²` function on `ℝ^k`. -/
def b1sas_realLp {G : Spatial k → ℝ} (hG : MemLp G 2 volume) :
    Lp ℂ 2 (volume : Measure (Spatial k)) :=
  hG.ofReal.toLp (fun x => (G x : ℂ))

theorem b1sas_coeFn_realLp {G : Spatial k → ℝ} (hG : MemLp G 2 volume) :
    b1sas_realLp hG =ᵐ[volume] fun x => (G x : ℂ) :=
  MemLp.coeFn_toLp _

/-- Complexification of a real smooth compactly supported test on `ℝ^k`, as a Schwartz map. -/
def b1sas_test (φ : Spatial k → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    𝓢(Spatial k, ℂ) :=
  (hc.comp_left (g := Complex.ofReal) rfl).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφ)

@[simp] theorem b1sas_test_apply (φ : Spatial k → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (x : Spatial k) : b1sas_test φ hφ hc x = (φ x : ℂ) := rfl

/-! ### Translated tests -/

theorem b1sas_contDiff_translate {g : Spatial k → ℝ} (hg : ContDiff ℝ ∞ g)
    (v : Spatial k) : ContDiff ℝ ∞ (fun y => g (y - v)) :=
  hg.comp (contDiff_id.sub contDiff_const)

theorem b1sas_hasCompactSupport_translate {g : Spatial k → ℝ} (hgc : HasCompactSupport g)
    (v : Spatial k) : HasCompactSupport (fun y => g (y - v)) :=
  hgc.comp_homeomorph (Homeomorph.subRight v)

theorem b1sas_continuous_char (v : Spatial k) :
    Continuous fun ξ : Spatial k => ((𝐞 (inner ℝ v ξ) : Circle) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_const.inner continuous_id))

/-- The inverse Fourier transform of the translated test `y ↦ g (y - v)`. -/
theorem b1sas_fourierInv_translate (g : Spatial k → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (v ξ : Spatial k) :
    (𝓕⁻ (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
        (b1sas_hasCompactSupport_translate hgc v)) : 𝓢(Spatial k, ℂ)) ξ =
      (𝐞 (inner ℝ v ξ) : ℂ) * (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ := by
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    Real.fourierInv_eq, ← integral_const_mul]
  simp only [b1sas_test_apply]
  have hs : ∫ x, 𝐞 (inner ℝ (x + v) ξ) • ((g (x + v - v) : ℝ) : ℂ) =
      ∫ y, 𝐞 (inner ℝ y ξ) • ((g (y - v) : ℝ) : ℂ) :=
    integral_add_right_eq_self (μ := volume)
      (fun y : Spatial k => 𝐞 (inner ℝ y ξ) • ((g (y - v) : ℝ) : ℂ)) v
  rw [← hs]
  congr 1
  funext x
  rw [add_sub_cancel_right, inner_add_left, AddChar.map_add_eq_mul, Circle.smul_def,
    Circle.smul_def, Circle.coe_mul, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Integrability -/

theorem b1sas_memLp_translate {G : Spatial k → ℝ} (hG : MemLp G 2 volume)
    (v : Spatial k) : MemLp (fun x => G (x + v)) 2 volume :=
  hG.comp_measurePreserving (measurePreserving_add_right volume v)

theorem b1sas_integrable_test_translate {G : Spatial k → ℝ} (hG : MemLp G 2 volume)
    (g : Spatial k → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : Spatial k) :
    Integrable (fun x => (g x : ℂ) * (G (x + v) : ℂ)) volume :=
  ((b1sas_test g hg hgc).memLp 2 volume).integrable_mul (b1sas_memLp_translate hG v).ofReal

theorem b1sas_memLp_char_mul (v : Spatial k) (ψ : 𝓢(Spatial k, ℂ)) :
    MemLp (fun ξ => (𝐞 (inner ℝ v ξ) : ℂ) * ψ ξ) 2 volume :=
  (ψ.memLp 2 volume).of_le ((b1sas_continuous_char v).mul ψ.continuous).aestronglyMeasurable
    (Eventually.of_forall fun ξ => by rw [norm_mul, Circle.norm_coe, one_mul])

/-! ### Testing identities -/

/-- Testing identity for one translate: `∫ g(x) G(x + v) dx = ∫ Ĝ(ξ) e(⟨v,ξ⟩) (𝓕⁻ g)(ξ) dξ`. -/
theorem b1sas_integral_test_translate {G : Spatial k → ℝ} (hG : MemLp G 2 volume)
    (g : Spatial k → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : Spatial k) :
    ∫ x, (g x : ℂ) * (G (x + v) : ℂ) =
      ∫ ξ, (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
        ((𝐞 (inner ℝ v ξ) : ℂ) * (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ) := by
  have h1 : ∫ x, (g x : ℂ) * (G (x + v) : ℂ) =
      ∫ y, (G y : ℂ) * (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
        (b1sas_hasCompactSupport_translate hgc v)) y := by
    have hs : ∫ x, (G (x + v) : ℂ) * (b1sas_test (fun y => g (y - v))
          (b1sas_contDiff_translate hg v) (b1sas_hasCompactSupport_translate hgc v)) (x + v) =
        ∫ y, (G y : ℂ) * (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
          (b1sas_hasCompactSupport_translate hgc v)) y :=
      integral_add_right_eq_self (μ := volume) (fun y : Spatial k => (G y : ℂ) *
        (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
          (b1sas_hasCompactSupport_translate hgc v)) y) v
    rw [← hs]
    congr 1
    funext x
    simp only [b1sas_test_apply, add_sub_cancel_right]
    ring
  have h2 : ∫ y, (G y : ℂ) * (b1sas_test (fun y => g (y - v))
        (b1sas_contDiff_translate hg v) (b1sas_hasCompactSupport_translate hgc v)) y =
      b1sas_pair k (b1sas_realLp hG) ((b1sas_test (fun y => g (y - v))
        (b1sas_contDiff_translate hg v) (b1sas_hasCompactSupport_translate hgc v)).toLp 2
          volume) := by
    rw [b1sas_pair_apply]
    apply integral_congr_ae
    filter_upwards [b1sas_coeFn_realLp hG, (b1sas_test (fun y => g (y - v))
        (b1sas_contDiff_translate hg v) (b1sas_hasCompactSupport_translate hgc v)).coeFn_toLp 2
        volume] with q hq1 hq2
    rw [hq1, hq2]
  have hFF : 𝓕⁻ (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) =
      b1sas_realLp hG :=
    (Lp.fourierTransformₗᵢ (Spatial k) ℂ).symm_apply_apply _
  have h3 : b1sas_pair k (b1sas_realLp hG) ((b1sas_test (fun y => g (y - v))
        (b1sas_contDiff_translate hg v) (b1sas_hasCompactSupport_translate hgc v)).toLp 2
          volume) =
      b1sas_pair k (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k)))
        ((𝓕⁻ (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
          (b1sas_hasCompactSupport_translate hgc v))).toLp 2 volume) := by
    conv_lhs => rw [← hFF]
    rw [b1sas_pair_fourierInv_left, SchwartzMap.toLp_fourierInv_eq]
  have h4 : b1sas_pair k (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k)))
        ((𝓕⁻ (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
          (b1sas_hasCompactSupport_translate hgc v))).toLp 2 volume) =
      ∫ ξ, (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
        (𝓕⁻ (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
          (b1sas_hasCompactSupport_translate hgc v)) : 𝓢(Spatial k, ℂ)) ξ := by
    rw [b1sas_pair_apply]
    apply integral_congr_ae
    filter_upwards [(𝓕⁻ (b1sas_test (fun y => g (y - v)) (b1sas_contDiff_translate hg v)
        (b1sas_hasCompactSupport_translate hgc v))).coeFn_toLp 2 volume] with ξ hξ
    rw [hξ]
  rw [h1, h2, h3, h4]
  congr 1
  funext ξ
  rw [b1sas_fourierInv_translate]

/-- The multiplier `∑_i c_i (e(⟨v_i,ξ⟩) - 1)` of `x ↦ ∑_i c_i (G(x + v_i) - G x)`. -/
def b1sas_mult {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → Spatial k)
    (ξ : Spatial k) : ℂ :=
  ∑ i ∈ s, (c i : ℂ) * ((𝐞 (inner ℝ (v i) ξ) : ℂ) - 1)

theorem b1sas_continuous_mult {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → Spatial k) :
    Continuous (b1sas_mult s c v) :=
  continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((b1sas_continuous_char (v i)).sub continuous_const)

theorem b1sas_norm_mult_le_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → Spatial k)
    (ξ : Spatial k) : ‖b1sas_mult s c v ξ‖ ≤ ∑ i ∈ s, 2 * |c i| := by
  unfold b1sas_mult
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖((𝐞 (inner ℝ (v i) ξ) : ℂ) - 1)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [Circle.norm_coe, norm_one]; norm_num)
  calc |c i| * ‖((𝐞 (inner ℝ (v i) ξ) : ℂ) - 1)‖ ≤ |c i| * 2 :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = 2 * |c i| := mul_comm _ _

/-- Testing identity for a finite combination of translate differences. -/
theorem b1sas_integral_test_comb {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → Spatial k) {G : Spatial k → ℝ} (hG : MemLp G 2 volume)
    (g : Spatial k → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, (g x : ℂ) * ((∑ i ∈ s, c i * (G (x + v i) - G x) : ℝ) : ℂ) =
      ∫ ξ, (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
        (b1sas_mult s c v ξ * (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ) := by
  have hzero : ∫ x, (g x : ℂ) * (G x : ℂ) =
      ∫ ξ, (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
        (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ := by
    have h := b1sas_integral_test_translate hG g hg hgc 0
    simp only [add_zero, inner_zero_left, AddChar.map_zero_eq_one, Circle.coe_one, one_mul] at h
    exact h
  have hiP0 : Integrable (fun x => (g x : ℂ) * (G x : ℂ)) volume := by
    simpa using b1sas_integrable_test_translate hG g hg hgc 0
  have hiF : ∀ w : Spatial k, Integrable (fun ξ =>
      (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
        ((𝐞 (inner ℝ w ξ) : ℂ) * (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ))
      volume := fun w =>
    (Lp.memLp _).integrable_mul (b1sas_memLp_char_mul w _)
  have hiF0 : Integrable (fun ξ =>
      (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
        (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ) volume :=
    (Lp.memLp _).integrable_mul ((𝓕⁻ (b1sas_test g hg hgc)).memLp 2 volume)
  calc ∫ x, (g x : ℂ) * ((∑ i ∈ s, c i * (G (x + v i) - G x) : ℝ) : ℂ)
      = ∫ x, ∑ i ∈ s, (c i : ℂ) * ((g x : ℂ) * (G (x + v i) : ℂ) - (g x : ℂ) * (G x : ℂ)) := by
        congr 1
        funext x
        push_cast
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i ∈ s, (c i : ℂ) * ((∫ x, (g x : ℂ) * (G (x + v i) : ℂ)) -
          ∫ x, (g x : ℂ) * (G x : ℂ)) := by
        rw [integral_finsetSum s (f := fun i x =>
            (c i : ℂ) * ((g x : ℂ) * (G (x + v i) : ℂ) - (g x : ℂ) * (G x : ℂ))) fun i _ =>
          ((b1sas_integrable_test_translate hG g hg hgc (v i)).sub hiP0).const_mul (c i : ℂ)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_sub (b1sas_integrable_test_translate hG g hg hgc (v i))
          hiP0]
    _ = ∑ i ∈ s, (c i : ℂ) * ((∫ ξ, (𝓕 (b1sas_realLp hG) :
          Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
          ((𝐞 (inner ℝ (v i) ξ) : ℂ) * (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ)) -
          ∫ ξ, (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
            (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [b1sas_integral_test_translate hG g hg hgc (v i), hzero]
    _ = ∫ ξ, ∑ i ∈ s, (c i : ℂ) *
          ((𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
            ((𝐞 (inner ℝ (v i) ξ) : ℂ) * (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ) -
          (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
            (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ) := by
        rw [integral_finsetSum s (f := fun i ξ => (c i : ℂ) *
            ((𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
              ((𝐞 (inner ℝ (v i) ξ) : ℂ) * (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ) -
            (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ *
              (𝓕⁻ (b1sas_test g hg hgc) : 𝓢(Spatial k, ℂ)) ξ)) fun i _ =>
          ((hiF (v i)).sub hiF0).const_mul (c i : ℂ)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_sub (hiF (v i)) hiF0]
    _ = _ := by
        congr 1
        funext ξ
        simp only [b1sas_mult, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Plancherel -/

/-- **Plancherel for finite combinations of spatial translate differences.** For real
`G ∈ L²(ℝ^k)`, `∫ |∑_i c_i (G(x + v_i) - G x)|² dx = ∫ |∑_i c_i (e(⟨v_i,ξ⟩) - 1)|² |Ĝ(ξ)|² dξ`. -/
theorem b1sas_lintegral_comb_sq {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (v : ι → Spatial k) {G : Spatial k → ℝ} (hG : MemLp G 2 volume) :
    ∫⁻ x, ‖∑ i ∈ s, c i * (G (x + v i) - G x)‖ₑ ^ 2 =
      ∫⁻ ξ, ‖b1sas_mult s c v ξ‖ₑ ^ 2 *
        ‖(𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
  have hGm : MemLp (fun ξ => b1sas_mult s c v ξ *
      (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ) 2 volume :=
    (Lp.memLp (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k)))).of_le_mul
      (c := ∑ i ∈ s, 2 * |c i|)
      ((b1sas_continuous_mult s c v).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun ξ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (b1sas_norm_mult_le_sum s c v ξ) (norm_nonneg _))
  have hphys : MemLp (fun x => ∑ i ∈ s, c i * (G (x + v i) - G x)) 2 volume :=
    memLp_finsetSum s fun i _ => ((b1sas_memLp_translate hG (v i)).sub hG).const_mul (c i)
  have hae : ∀ᵐ p ∂volume, (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (Spatial k))) p =
      ((∑ i ∈ s, c i * (G (p + v i) - G p) : ℝ) : ℂ) := by
    apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
      (hphys.ofReal.locallyIntegrable (by norm_num))
    intro g hg hgc
    simp only [Complex.real_smul]
    rw [b1sas_integral_test_comb s c v hG g hg hgc]
    have h1 : ∫ x, (g x : ℂ) * (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (Spatial k))) x =
        b1sas_pair k (𝓕⁻ (hGm.toLp _)) ((b1sas_test g hg hgc).toLp 2 volume) := by
      rw [b1sas_pair_apply]
      apply integral_congr_ae
      filter_upwards [(b1sas_test g hg hgc).coeFn_toLp 2 volume] with x hx
      rw [hx, b1sas_test_apply, mul_comm]
    rw [h1, b1sas_pair_fourierInv_left, SchwartzMap.toLp_fourierInv_eq, b1sas_pair_apply]
    apply integral_congr_ae
    filter_upwards [hGm.coeFn_toLp, (𝓕⁻ (b1sas_test g hg hgc)).coeFn_toLp 2 volume]
      with ξ h1 h2
    rw [h1, h2]
    ring
  have hHn : ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (Spatial k)))‖ₑ =
      ‖hGm.toLp _‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact congrArg _ ((Lp.fourierTransformₗᵢ (Spatial k) ℂ).symm.nnnorm_map _)
  calc ∫⁻ x, ‖∑ i ∈ s, c i * (G (x + v i) - G x)‖ₑ ^ 2
      = ∫⁻ p, ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (Spatial k))) p‖ₑ ^ 2 := by
        apply lintegral_congr_ae
        filter_upwards [hae] with p hp
        rw [hp, FourierAffine.enorm_complex_ofReal]
    _ = ‖(𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (Spatial k)))‖ₑ ^ 2 := by
        rw [FourierAffine.lintegral_enorm_sq_eq (Lp.aestronglyMeasurable _), Lp.enorm_def]
    _ = ‖hGm.toLp _‖ₑ ^ 2 := by rw [hHn]
    _ = ∫⁻ ξ, ‖b1sas_mult s c v ξ *
          (𝓕 (b1sas_realLp hG) : Lp ℂ 2 (volume : Measure (Spatial k))) ξ‖ₑ ^ 2 := by
        rw [Lp.enorm_def, eLpNorm_congr_ae hGm.coeFn_toLp,
          ← FourierAffine.lintegral_enorm_sq_eq hGm.aestronglyMeasurable]
    _ = _ := by simp only [enorm_mul, mul_pow]

end ParabolicRectifiability.Characterization
