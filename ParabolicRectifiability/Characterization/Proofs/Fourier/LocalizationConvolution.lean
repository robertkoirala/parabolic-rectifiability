import ParabolicRectifiability.Characterization.Proofs.Fourier.LocalizationPlancherel
import ParabolicRectifiability.Foundations.Statements.HighPass

/-! # Critical Sobolev localization: time convolutions on `L²`

Tools for the near estimate in the proof of `ba1_critical_sobolev_localization_proof`.

For an integrable kernel `K : ℝ → ℝ` and a real `w ∈ L²(ℝ^m × ℝ)`, the time convolution
`N = K *_t w`, `N(x) = ∫ K(s) w(x - s e_t) ds` (`fhp_timeConvolution`), is in `L²` and its L²
Fourier transform is `N̂(ξ,τ) = K̂(τ) ŵ(ξ,τ)` almost everywhere (`b1loc_timeConvolution_fourier`).
This is the convolution theorem along the time direction; the kernel is not an integrable
function on `ℝ^m × ℝ`, so the library convolution theorem does not apply. It is proved by the
testing method used for `b1loc_lintegral_translate_sub_sq`: Tonelli/Fubini through the time shear
`(x, s) ↦ x - s e_t` (quasi-measure-preserving), the bilinear Parseval identity against the
translated tests `g(· + s e_t)`, whose inverse transforms carry the phase `e(-sτ)`, and Fubini in
`(s, ζ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ContDiff SchwartzMap

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

attribute [local instance] FourierAffine.continuousSMul_fourierSpace

variable {m : ℕ}

/-! ## The time shear -/

/-- `(x, s) ↦ x - s e_t` is quasi-measure-preserving from `volume ⊗ volume` to `volume`. -/
theorem b1loc_qmp_timeShift :
    QuasiMeasurePreserving (fun p : FourierSpace m × ℝ => p.1 - p.2 • timeVector m)
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) volume := by
  have hskew : MeasurePreserving (fun p : ℝ × FourierSpace m => (p.1, p.2 - p.1 • timeVector m))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m)))
      ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) :=
    MeasurePreserving.skew_product (MeasurePreserving.id volume)
      (g := fun (s : ℝ) (x : FourierSpace m) => x - s • timeVector m)
      (measurable_snd.sub (measurable_fst.smul_const _))
      (Eventually.of_forall fun s =>
        (measurePreserving_sub_right volume (s • timeVector m)).map_eq)
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure (FourierSpace m)))
    (ν := (volume : Measure ℝ))
  exact (Measure.quasiMeasurePreserving_snd.comp hskew.quasiMeasurePreserving).comp
    hswap.quasiMeasurePreserving

theorem b1loc_aestronglyMeasurable_shift {E : Type*} [NormedAddCommGroup E]
    {w : FourierSpace m → E} (hw : AEStronglyMeasurable w volume) :
    AEStronglyMeasurable (fun p : FourierSpace m × ℝ => w (p.1 - p.2 • timeVector m))
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) :=
  hw.comp_quasiMeasurePreserving b1loc_qmp_timeShift

/-! ## A uniform local `L¹` bound for translates -/

/-- `∫_S |w(x - c)| dx ≤ ‖w‖₂ |S|^{1/2}`, uniformly in the translation `c`. -/
theorem b1loc_lintegral_shift_le {w : FourierSpace m → ℝ} (hw : MemLp w 2 volume)
    (S : Set (FourierSpace m)) (c : FourierSpace m) :
    ∫⁻ x in S, ‖w (x - c)‖ₑ ≤ eLpNorm w 2 volume * volume S ^ (1 / 2 : ℝ) := by
  have hwc : AEStronglyMeasurable (fun x => w (x - c)) volume :=
    hw.aestronglyMeasurable.comp_measurePreserving (measurePreserving_sub_right volume c)
  rw [← eLpNorm_one_eq_lintegral_enorm hwc.restrict]
  have he : 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
  calc eLpNorm (fun x => w (x - c)) 1 (volume.restrict S)
      ≤ eLpNorm (fun x => w (x - c)) 2 (volume.restrict S) *
          (volume.restrict S) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hwc.restrict
    _ ≤ eLpNorm w 2 volume * volume S ^ (1 / 2 : ℝ) := by
        rw [he, Measure.restrict_apply_univ]
        gcongr
        calc eLpNorm (fun x => w (x - c)) 2 (volume.restrict S)
            ≤ eLpNorm (fun x => w (x - c)) 2 volume :=
              eLpNorm_mono_measure _ Measure.restrict_le_self
          _ = eLpNorm w 2 volume :=
              eLpNorm_comp_measurePreserving hw.aestronglyMeasurable (measurePreserving_sub_right volume c)

/-- The absolute product integral `∫∫ 1_S(x) |K(s)| |w(x - s e_t)| ds dx` is finite for
measurable `S` of finite measure. -/
theorem b1loc_lintegral_indicator_timeConv_lt_top {K : ℝ → ℝ} (hK : Integrable K)
    {w : FourierSpace m → ℝ} (hw : MemLp w 2 volume) {S : Set (FourierSpace m)}
    (hS : MeasurableSet S) (hSf : volume S < ⊤) :
    ∫⁻ p : FourierSpace m × ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) p.1 *
        ‖K p.2 * w (p.1 - p.2 • timeVector m)‖ₑ
      ∂((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) < ⊤ := by
  have hmeas : AEMeasurable (fun p : FourierSpace m × ℝ =>
      S.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ‖K p.2 * w (p.1 - p.2 • timeVector m)‖ₑ)
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) :=
    ((measurable_const.indicator hS).comp measurable_fst).aemeasurable.mul
      ((hK.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
        (b1loc_aestronglyMeasurable_shift hw.aestronglyMeasurable)).enorm
  rw [lintegral_prod_symm _ hmeas]
  calc ∫⁻ s : ℝ, ∫⁻ x : FourierSpace m, S.indicator (fun _ => (1 : ℝ≥0∞)) x *
        ‖K s * w (x - s • timeVector m)‖ₑ
      ≤ ∫⁻ s : ℝ, ‖K s‖ₑ * (eLpNorm w 2 volume * volume S ^ (1 / 2 : ℝ)) := by
        refine lintegral_mono fun s => ?_
        calc ∫⁻ x : FourierSpace m, S.indicator (fun _ => (1 : ℝ≥0∞)) x *
              ‖K s * w (x - s • timeVector m)‖ₑ
            = ‖K s‖ₑ * ∫⁻ x in S, ‖w (x - s • timeVector m)‖ₑ := by
              rw [← lintegral_indicator hS, ← lintegral_const_mul' _ _ enorm_ne_top]
              refine lintegral_congr fun x => ?_
              by_cases hx : x ∈ S
              · rw [indicator_of_mem hx, indicator_of_mem hx, one_mul, enorm_mul]
              · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, mul_zero]
          _ ≤ ‖K s‖ₑ * (eLpNorm w 2 volume * volume S ^ (1 / 2 : ℝ)) := by
              gcongr
              exact b1loc_lintegral_shift_le hw S _
    _ = (∫⁻ s : ℝ, ‖K s‖ₑ) * (eLpNorm w 2 volume * volume S ^ (1 / 2 : ℝ)) :=
        lintegral_mul_const' _ _ (ENNReal.mul_ne_top (memLp_iff.1 hw).ne
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSf.ne))
    _ < ⊤ := ENNReal.mul_lt_top hK.2 (ENNReal.mul_lt_top (memLp_iff.1 hw)
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSf.ne))

/-! ## Local integrability of the time convolution -/

theorem b1loc_aestronglyMeasurable_timeConvolution {K : ℝ → ℝ} (hK : Integrable K)
    {w : FourierSpace m → ℝ} (hw : MemLp w 2 volume) :
    AEStronglyMeasurable (fhp_timeConvolution K w) volume :=
  ((hK.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
    (b1loc_aestronglyMeasurable_shift hw.aestronglyMeasurable)).integral_prod_right'

theorem b1loc_locallyIntegrable_timeConvolution {K : ℝ → ℝ} (hK : Integrable K)
    {w : FourierSpace m → ℝ} (hw : MemLp w 2 volume) :
    LocallyIntegrable (fhp_timeConvolution K w) volume := by
  rw [locallyIntegrable_iff]
  intro S hS
  refine ⟨(b1loc_aestronglyMeasurable_timeConvolution hK hw).restrict, ?_⟩
  have hfin := b1loc_lintegral_indicator_timeConv_lt_top hK hw hS.measurableSet
    hS.measure_lt_top
  have hmeas : AEMeasurable (fun p : FourierSpace m × ℝ =>
      S.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ‖K p.2 * w (p.1 - p.2 • timeVector m)‖ₑ)
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) :=
    ((measurable_const.indicator hS.measurableSet).comp measurable_fst).aemeasurable.mul
      ((hK.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
        (b1loc_aestronglyMeasurable_shift hw.aestronglyMeasurable)).enorm
  rw [lintegral_prod _ hmeas] at hfin
  refine lt_of_le_of_lt ?_ hfin
  rw [← lintegral_indicator hS.measurableSet]
  refine lintegral_mono fun x => ?_
  dsimp only
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx, one_mul]
    exact enorm_integral_le_lintegral_enorm _
  · rw [indicator_of_notMem hx]
    exact zero_le

/-! ## The convolution theorem along the time direction -/

/-- Bilinear Parseval for a real `L²` function against a Schwartz test. -/
theorem b1loc_integral_real_mul_schwartz {G : FourierSpace m → ℝ} (hG : MemLp G 2 volume)
    (T : 𝓢(FourierSpace m, ℂ)) :
    ∫ x, (G x : ℂ) * T x =
      ∫ ζ, (𝓕 (realLp hG) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T) ζ := by
  rw [← b1loc_integral_mul_schwartz]
  apply integral_congr_ae
  filter_upwards [coeFn_realLp hG] with x hx
  rw [hx]

/-- **Convolution theorem for a time convolution.** For integrable `K : ℝ → ℝ` and real
`w ∈ L²(ℝ^m × ℝ)`, `N = K *_t w` is in `L²` and `N̂(ζ) = K̂(τ) ŵ(ζ)` almost everywhere,
`K̂(τ) = ∫ e^{-2πi sτ} K(s) ds`. -/
theorem b1loc_timeConvolution_fourier {K : ℝ → ℝ} (hK : Integrable K)
    {w : FourierSpace m → ℝ} (hw : MemLp w 2 volume) :
    ∃ hN : MemLp (fhp_timeConvolution K w) 2 volume,
      (𝓕 (realLp hN) : Lp ℂ 2 (volume : Measure (FourierSpace m))) =ᵐ[volume]
        fun ζ => 𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2 *
          (𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ := by
  have hKc : Integrable (fun t : ℝ => (K t : ℂ)) := hK.ofReal
  have hKh_cont : Continuous (𝓕 (fun t : ℝ => (K t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hKc
  have hKhc : Continuous fun ζ : FourierSpace m =>
      𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2 :=
    hKh_cont.comp (continuous_snd.comp (WithLp.prod_continuous_ofLp _ _ _))
  have hGm : MemLp (fun ζ => 𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2 *
      (𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ) 2 volume :=
    (Lp.memLp (𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m)))).of_le_mul
      (c := ∫ t, ‖(K t : ℂ)‖) (hKhc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
      (Eventually.of_forall fun ζ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (Real.norm_fourier_le_integral_norm _ _)
          (norm_nonneg _))
  have hloc := b1loc_locallyIntegrable_timeConvolution hK hw
  have hlocC : LocallyIntegrable (fun x => ((fhp_timeConvolution K w x : ℝ) : ℂ)) volume :=
    locallyIntegrable_iff.2 fun S hS => (locallyIntegrable_iff.1 hloc S hS).ofReal
  -- Integrability of `(x, s) ↦ g(x) K(s) w(x - s e_t)` for a compact test `g`.
  have hprod : ∀ g : FourierSpace m → ℝ, Continuous g → HasCompactSupport g →
      Integrable (Function.uncurry fun (x : FourierSpace m) (s : ℝ) =>
        (g x : ℂ) * ((K s * w (x - s • timeVector m) : ℝ) : ℂ))
        ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) := by
    intro g hgc hgs
    obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hm1 : AEStronglyMeasurable (fun p : FourierSpace m × ℝ =>
        K p.2 * w (p.1 - p.2 • timeVector m))
        ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) :=
      (hK.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
        (b1loc_aestronglyMeasurable_shift hw.aestronglyMeasurable)
    refine ⟨(Complex.continuous_ofReal.comp (hgc.comp continuous_fst)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hm1), ?_⟩
    have hfin := b1loc_lintegral_indicator_timeConv_lt_top hK hw (isClosed_tsupport g).measurableSet
      hgs.isCompact.measure_lt_top
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := M)) hfin)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun p => ?_
    obtain ⟨x, s⟩ := p
    simp only [Function.uncurry_apply_pair, enorm_mul, FourierAffine.enorm_complex_ofReal]
    by_cases hx : x ∈ tsupport g
    · rw [indicator_of_mem hx, one_mul]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM x)
    · rw [image_eq_zero_of_notMem_tsupport hx, enorm_zero, zero_mul]
      exact zero_le
  have hid : ∀ᵐ x ∂volume,
      (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x =
        ((fhp_timeConvolution K w x : ℝ) : ℂ) := by
    apply ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num)) hlocC
    intro g hg hgc
    simp only [Complex.real_smul]
    have hL : ∫ x, (g x : ℂ) *
          (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x =
        ∫ ζ, 𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2 *
          (𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
            (𝓕⁻ (realCompactTest g hg hgc)) ζ := by
      calc _ = ∫ x, (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) x *
            realCompactTest g hg hgc x := by
            congr 1
            funext x
            rw [realCompactTest_apply, mul_comm]
        _ = ∫ ζ, (hGm.toLp _ : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
            (𝓕⁻ (realCompactTest g hg hgc)) ζ := b1loc_integral_fourierInv_mul _ _
        _ = _ := by
            apply integral_congr_ae
            filter_upwards [hGm.coeFn_toLp] with ζ hζ
            rw [hζ]
    -- The translated tests and their inverse transforms.
    have hgs : ∀ s : ℝ, ContDiff ℝ ∞ (fun y => g (y + s • timeVector m)) := fun s =>
      hg.comp (contDiff_id.add contDiff_const)
    have hgcs : ∀ s : ℝ, HasCompactSupport (fun y => g (y + s • timeVector m)) := fun s =>
      hgc.comp_homeomorph (Homeomorph.addRight (s • timeVector m))
    have hFT : ∀ (s : ℝ) (ζ : FourierSpace m),
        (𝓕⁻ (realCompactTest _ (hgs s) (hgcs s))) ζ =
          ((𝐞 (-(s * (WithLp.ofLp ζ).2)) : Circle) : ℂ) * (𝓕⁻ (realCompactTest g hg hgc)) ζ := by
      intro s ζ
      have e1 : (⇑(realCompactTest _ (hgs s) (hgcs s)) : FourierSpace m → ℂ) =
          fun x => realCompactTest g hg hgc (x + -(-(s • timeVector m))) := by
        funext x
        simp only [realCompactTest_apply, neg_neg]
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_coe, e1,
        b1loc_fourierInv_comp_add_neg, inner_neg_left, b1loc_inner_smul_timeVector]
    have hWT : ∀ T : 𝓢(FourierSpace m, ℂ), Integrable (fun ζ =>
        (𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ * (𝓕⁻ T) ζ) volume :=
      fun T => (Lp.memLp _).integrable_mul ((𝓕⁻ T).memLp 2 volume)
    -- Integrability in `(s, ζ)`.
    have hprod2 : Integrable (Function.uncurry fun (s : ℝ) (ζ : FourierSpace m) =>
        ((𝐞 (-(s * (WithLp.ofLp ζ).2)) : Circle) : ℂ) * (K s : ℂ) *
          ((𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
            (𝓕⁻ (realCompactTest g hg hgc)) ζ))
        ((volume : Measure ℝ).prod (volume : Measure (FourierSpace m))) := by
      have hph : Continuous fun p : ℝ × FourierSpace m =>
          ((𝐞 (-(p.1 * (WithLp.ofLp p.2).2)) : Circle) : ℂ) :=
        b1loc_continuous_fourierChar_coe.comp ((continuous_fst.mul
          ((continuous_snd.comp (WithLp.prod_continuous_ofLp _ _ _)).comp continuous_snd)).neg)
      refine (hKc.norm.mul_prod (hWT (realCompactTest g hg hgc)).norm).mono' ?_
        (Eventually.of_forall fun p => ?_)
      · exact (hph.aestronglyMeasurable.mul
          (hKc.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)).mul
          ((hWT (realCompactTest g hg hgc)).1.comp_quasiMeasurePreserving
            Measure.quasiMeasurePreserving_snd)
      · obtain ⟨s, ζ⟩ := p
        simp only [Function.uncurry_apply_pair, norm_mul, Circle.norm_coe, one_mul]
        exact le_rfl
    have hR : ∫ x, (g x : ℂ) * ((fhp_timeConvolution K w x : ℝ) : ℂ) =
        ∫ ζ, 𝓕 (fun t : ℝ => (K t : ℂ)) (WithLp.ofLp ζ).2 *
          (𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
            (𝓕⁻ (realCompactTest g hg hgc)) ζ := by
      calc ∫ x, (g x : ℂ) * ((fhp_timeConvolution K w x : ℝ) : ℂ)
          = ∫ x, ∫ s, (g x : ℂ) * ((K s * w (x - s • timeVector m) : ℝ) : ℂ) := by
            congr 1
            funext x
            rw [fhp_timeConvolution, ← integral_complex_ofReal, ← integral_const_mul]
        _ = ∫ s, ∫ x, (g x : ℂ) * ((K s * w (x - s • timeVector m) : ℝ) : ℂ) :=
            integral_integral_swap (hprod g hg.continuous hgc)
        _ = ∫ s, (K s : ℂ) * ∫ ζ, (𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
              (𝓕⁻ (realCompactTest _ (hgs s) (hgcs s))) ζ := by
            congr 1
            funext s
            rw [← b1loc_integral_real_mul_schwartz hw, ← integral_const_mul]
            have hsh := integral_sub_right_eq_self (μ := (volume : Measure (FourierSpace m)))
              (fun y => (K s : ℂ) * ((w y : ℂ) * realCompactTest _ (hgs s) (hgcs s) y))
              (s • timeVector m)
            rw [← hsh]
            congr 1
            funext x
            simp only [realCompactTest_apply, sub_add_cancel]
            push_cast
            ring
        _ = ∫ s, ∫ ζ, ((𝐞 (-(s * (WithLp.ofLp ζ).2)) : Circle) : ℂ) * (K s : ℂ) *
              ((𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
                (𝓕⁻ (realCompactTest g hg hgc)) ζ) := by
            congr 1
            funext s
            rw [← integral_const_mul]
            congr 1
            funext ζ
            rw [hFT]
            ring
        _ = ∫ ζ, ∫ s, ((𝐞 (-(s * (WithLp.ofLp ζ).2)) : Circle) : ℂ) * (K s : ℂ) *
              ((𝓕 (realLp hw) : Lp ℂ 2 (volume : Measure (FourierSpace m))) ζ *
                (𝓕⁻ (realCompactTest g hg hgc)) ζ) := integral_integral_swap hprod2
        _ = _ := by
            congr 1
            funext ζ
            rw [integral_mul_const, Real.fourier_real_eq]
            simp only [Circle.smul_def, smul_eq_mul]
            ring
    exact hL.trans hR.symm
  have hNC : MemLp (fun x => ((fhp_timeConvolution K w x : ℝ) : ℂ)) 2 volume :=
    (Lp.memLp _).ae_eq hid
  have hN : MemLp (fhp_timeConvolution K w) 2 volume := by
    have h := hNC.re
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using h
  refine ⟨hN, ?_⟩
  have hid' : (fun x => ((fhp_timeConvolution K w x : ℝ) : ℂ)) =ᵐ[volume]
      (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) := by
    filter_upwards [hid] with x hx
    exact hx.symm
  have hLp : realLp hN = (𝓕⁻ (hGm.toLp _) : Lp ℂ 2 (volume : Measure (FourierSpace m))) :=
    Lp.ext ((coeFn_realLp hN).trans hid')
  have hFF : (𝓕 (realLp hN) : Lp ℂ 2 (volume : Measure (FourierSpace m))) = hGm.toLp _ := by
    rw [hLp]
    exact (Lp.fourierTransformₗᵢ (FourierSpace m) ℂ).apply_symm_apply _
  rw [hFF]
  exact hGm.coeFn_toLp

end ParabolicRectifiability.Characterization
