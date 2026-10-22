import ParabolicRectifiability.Analysis.FractionalKernel.InverseHalfFourier
import ParabolicRectifiability.Analysis.FractionalKernel.InverseHalfConvolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Integrability, cancellation and Fourier transform of `K = I - η * I`

One-dimensional analysis. It uses the weak Fourier identity of `|t|^{-1/2}`
(`fhpbb2f_weak_fourier`, for integrable continuous data), the multiplication formula
`fhpbb2f_integral_mul_fourier`, `fhpbb2f_integrable_rpow_mul_norm`, and from the convolution
estimates `fhpbb2b_integrable`, `fhpbb2b_abs_le`, `fhpbb2a_remote`, `fhpbb2a_integrable_weight`.

Write `I(t) = |t|^{-1/2}` (Mathlib's `Real.rpow`, so `I(0) = 0`), `η̂(τ) = ∫ e^{-2πitτ} η(t) dt`
(Mathlib's phase) and, for a real Schwartz `η`, `K(t) = I(t) - ∫ η(s) I(t - s) ds`.
Main results:
* `fhpbb2h_integrable_of_bounds`: a function continuous off `0` with
  `|f t| ≤ C₀ (1 + |t|^{-1/2})` on `|t| ≤ 1` and `|f t| ≤ C₁ |t|^{-2}` on `|t| ≥ 1` is
  integrable;
* `fhpbb2h_weak_identity` (the weak identity with absolute bounds): if `K ∈ L¹`,
  then `∫ K ψ̂ = ∫ (1 - η̂) I ψ` for every complex Schwartz `ψ`;
* `fhpbb2h_fourier_eq` (pointwise identification): if `K ∈ L¹` and `η̂ = 1` near
  `0`, then `K̂(τ) = (1 - η̂(τ)) I(τ)` for **every** `τ`;
* `fhpbb2h_kernelFourier_main`: hence also `∫ K = K̂(0) = 0`.

Proof. The weak identity: `∫ K ψ̂ = ∫ I ψ̂ - ∫ (η * I) ψ̂`, with
`∫ I ψ̂ = ∫ I ψ` (`fhpbb2f_inverseHalf_fourier_schwartz`) and
`∫ (η * I) ψ̂ = ∫ η(s) ∫ I(u) ψ̂(u + s) du ds = ∫ η(s) ∫ I(τ) e^{-2πiτs} ψ(τ) dτ ds = ∫ η̂ I ψ`
(`fhpbb2h_conv_pairing`): two absolutely convergent interchanges (the first from the uniform
bound `∫ |η(s)| I(t - s) ds ≤ 6 B`, the second a product of integrable functions) and the weak
identity of `I` against the modulated test `τ ↦ e^{-2πiτs} ψ(τ)`, whose transform is
`ψ̂(· + s)` (`fhpbb2h_weak_modulated`). Identification: `∫ g K̂ = ∫ ĝ K = ∫ M g` for real
compact smooth `g` (multiplication formula), so the continuous functions `K̂` and
`M = (1 - η̂) I` agree almost everywhere (`ae_eq_of_integral_contDiff_smul_eq`), hence
everywhere. `M` is continuous because it vanishes near `0` (`η̂ ≡ 1` there); its value at `0` is
`0`, which gives `∫ K = K̂(0) = 0`.
-/

noncomputable section

open MeasureTheory Set Filter Function
open scoped FourierTransform SchwartzMap Topology ContDiff

namespace ParabolicRectifiability.FractionalKernel

/-! ## Integrability from the near-zero bound and the tails -/

/-- A function continuous off `0` with `|f t| ≤ C₀ (1 + |t|^{-1/2})` for `|t| ≤ 1` and
`|f t| ≤ C₁ |t|^{-2}` for `|t| ≥ 1` is integrable. -/
theorem fhpbb2h_integrable_of_bounds {f : ℝ → ℝ} (hc : ContinuousOn f {0}ᶜ) {C₀ C₁ : ℝ}
    (h0 : ∀ t : ℝ, |t| ≤ 1 → |f t| ≤ C₀ * (1 + |t| ^ (-(1 / 2 : ℝ))))
    (h1 : ∀ t : ℝ, 1 ≤ |t| → |f t| ≤ C₁ * |t| ^ (-(2 : ℝ))) : Integrable f := by
  have hmeas : AEStronglyMeasurable f volume := by
    have h := hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
    rwa [restrict_compl_singleton] at h
  rw [← integrableOn_univ, ← union_compl_self (Icc (-1 : ℝ) 1)]
  refine IntegrableOn.union ?_ ?_
  · have hdom : IntegrableOn (fun t : ℝ => |C₀| * (1 + |t| ^ (-(1 / 2 : ℝ)))) (Icc (-1 : ℝ) 1) :=
      Integrable.const_mul (Integrable.add
        ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).integrableOn_Icc)
        (fhpbb2a_locallyIntegrable_inverseHalf.integrableOn_isCompact isCompact_Icc)) _
    refine Integrable.mono' hdom hmeas.restrict
      (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact (h0 t (abs_le.mpr ht)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C₀) (by positivity))
  · have hdom : Integrable (fun t : ℝ => 4 * |C₁| * ((1 + |t|) ^ 2)⁻¹) :=
      fhpbb2a_integrable_weight.const_mul _
    refine Integrable.mono' hdom.integrableOn hmeas.restrict
      (ae_restrict_of_forall_mem measurableSet_Icc.compl fun t ht => ?_)
    have ht1 : 1 ≤ |t| := by
      by_contra h
      exact ht (abs_le.mp (not_le.mp h).le)
    have hpos : 0 < |t| := by linarith
    rw [Real.norm_eq_abs]
    refine (h1 t ht1).trans ?_
    have hrw : |t| ^ (-(2 : ℝ)) = (|t| ^ 2)⁻¹ := by
      rw [Real.rpow_neg hpos.le, Real.rpow_two]
    have hsq : (1 + |t|) ^ 2 / 4 ≤ |t| ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (by positivity : (0 : ℝ) ≤ 3 * |t| + 1)]
    have hkey : (|t| ^ 2)⁻¹ ≤ 4 * ((1 + |t|) ^ 2)⁻¹ := by
      calc (|t| ^ 2)⁻¹ ≤ ((1 + |t|) ^ 2 / 4)⁻¹ := inv_anti₀ (by positivity) hsq
        _ = 4 * ((1 + |t|) ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [hrw]
    calc C₁ * (|t| ^ 2)⁻¹ ≤ |C₁| * (|t| ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₁| * (4 * ((1 + |t|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
      _ = 4 * |C₁| * ((1 + |t|) ^ 2)⁻¹ := by ring

/-! ## The weak identity of `I` against modulated tests -/

theorem fhpbb2h_norm_inverseHalf (τ : ℝ) :
    ‖((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ = |τ| ^ (-(1 / 2 : ℝ)) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg τ) _)]

theorem fhpbb2h_continuous_char (s : ℝ) :
    Continuous (fun τ : ℝ => ((𝐞 (-(τ * s)) : Circle) : ℂ)) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const).neg)

/-- Modulation: `𝓕 (τ ↦ e^{-2πiτs} f(τ))(u) = 𝓕 f (u + s)`. -/
theorem fhpbb2h_fourier_modulate (f : ℝ → ℂ) (s u : ℝ) :
    𝓕 (fun τ : ℝ => ((𝐞 (-(τ * s)) : Circle) : ℂ) * f τ) u = 𝓕 f (u + s) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  beta_reduce
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  have h : -(v * u) + -(v * s) = -(v * (u + s)) := by ring
  rw [h]

/-- `|·|^{-1/2} ‖ψ‖` is integrable for a complex Schwartz `ψ`. -/
theorem fhpbb2h_integrable_rpow_mul_norm (ψ : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ)) * ‖ψ t‖) :=
  fhpbb2f_integrable_rpow_mul_norm ψ.integrable ψ.continuous
    (fun x => SchwartzMap.norm_le_seminorm ℝ ψ x)

/-- `I ψ` is integrable for a complex Schwartz `ψ`. -/
theorem fhpbb2h_integrable_inverseHalf_mul (ψ : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => ((|t| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ t) := by
  refine (fhpbb2h_integrable_rpow_mul_norm ψ).mono' ?_ (ae_of_all _ fun t => le_of_eq ?_)
  · exact ((Complex.measurable_ofReal.comp fhpbb2b_measurable_inverseHalf).mul
      ψ.continuous.measurable).aestronglyMeasurable
  · simp only [norm_mul, fhpbb2h_norm_inverseHalf]

/-- **Weak identity against a modulated test.** For a complex Schwartz `ψ` and `s ∈ ℝ`,
`∫ I(u) ψ̂(u + s) du = ∫ I(τ) e^{-2πiτs} ψ(τ) dτ`. -/
theorem fhpbb2h_weak_modulated (ψ : 𝓢(ℝ, ℂ)) (s : ℝ) :
    ∫ u : ℝ, ((|u| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * 𝓕 (⇑ψ) (u + s) =
      ∫ τ : ℝ, ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : 𝓢(ℝ, ℂ), 𝓕 (⇑ψ) = ⇑Ψ := ⟨𝓕 ψ, rfl⟩
  have hFf : 𝓕 (fun τ : ℝ => ((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ) = fun u => Ψ (u + s) := by
    funext u
    rw [fhpbb2h_fourier_modulate, hΨ]
  have hnorm : ∀ τ : ℝ, ‖((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ‖ = ‖ψ τ‖ := fun τ => by
    rw [norm_mul, Circle.norm_coe, one_mul]
  have hfc : Continuous (fun τ : ℝ => ((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ) :=
    (fhpbb2h_continuous_char s).mul ψ.continuous
  have hfi : Integrable (fun τ : ℝ => ((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ) :=
    ψ.integrable.norm.mono' hfc.aestronglyMeasurable (ae_of_all _ fun τ => (hnorm τ).le)
  have hΨs : Continuous (fun u : ℝ => Ψ (u + s)) :=
    Ψ.continuous.comp (continuous_id.add continuous_const)
  have hIf : Integrable (fun τ : ℝ => |τ| ^ (-(1 / 2 : ℝ)) *
      ‖((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ‖) :=
    (fhpbb2h_integrable_rpow_mul_norm ψ).congr
      (ae_of_all _ fun τ => by simp only [hnorm])
  have hIFf : Integrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ)) *
      ‖𝓕 (fun τ : ℝ => ((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ) t‖) := by
    rw [hFf]
    exact fhpbb2f_integrable_rpow_mul_norm (Ψ.integrable.comp_add_right s) hΨs
      (fun x => SchwartzMap.norm_le_seminorm ℝ Ψ (x + s))
  have h := fhpbb2f_weak_fourier hfi hfc (by rw [hFf]; exact hΨs) hIf hIFf
  rw [hFf] at h
  rw [hΨ]
  exact h

/-! ## The convolution pairing `∫ (η * I) ψ̂ = ∫ η̂ I ψ` -/

/-- The uniform bound `∫ |η(s) I(t - s)| ds ≤ 6 B` behind the first interchange. -/
theorem fhpbb2h_conv_abs_le (η : 𝓢(ℝ, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ∫ s : ℝ, |η s * |t - s| ^ (-(1 / 2 : ℝ))| ≤ 6 * B := by
  obtain ⟨B, hB0, hB⟩ := fhpbb2b_abs_le η
  refine ⟨B, hB0, fun t => ?_⟩
  calc ∫ s : ℝ, |η s * |t - s| ^ (-(1 / 2 : ℝ))|
      ≤ ∫ s : ℝ, B * (((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ))) := by
        refine integral_mono (fhpbb2b_integrable η t).abs ((fhpbb2a_remote t).1.const_mul B)
          (fun s => ?_)
        have hI : (0 : ℝ) ≤ |t - s| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
        show |η s * |t - s| ^ (-(1 / 2 : ℝ))| ≤
          B * (((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)))
        rw [abs_mul, abs_of_nonneg hI, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hB s) hI
    _ = B * ∫ s : ℝ, ((1 + |s|) ^ 2)⁻¹ * |t - s| ^ (-(1 / 2 : ℝ)) := integral_const_mul _ _
    _ ≤ B * 6 := mul_le_mul_of_nonneg_left (fhpbb2a_remote t).2 hB0
    _ = 6 * B := mul_comm _ _

/-- **The convolution pairing.** For a real Schwartz `η` and a complex Schwartz `ψ`,
`∫ (η * I)(t) ψ̂(t) dt = ∫ η̂(τ) I(τ) ψ(τ) dτ`, by two absolutely convergent interchanges and
`fhpbb2h_weak_modulated`. -/
theorem fhpbb2h_conv_pairing (η : 𝓢(ℝ, ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, (((∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * 𝓕 (⇑ψ) t =
      ∫ τ : ℝ, 𝓕 (fun t : ℝ => (η t : ℂ)) τ * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : 𝓢(ℝ, ℂ), 𝓕 (⇑ψ) = ⇑Ψ := ⟨𝓕 ψ, rfl⟩
  rw [hΨ]
  -- the first interchange: absolute integrability on `ℝ × ℝ` (variables `(t, s)`)
  have hm1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((η p.2 * |p.1 - p.2| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ p.1) (volume.prod volume) :=
    ((Complex.measurable_ofReal.comp ((η.continuous.measurable.comp measurable_snd).mul
      (fhpbb2b_measurable_inverseHalf.comp (measurable_fst.sub measurable_snd)))).mul
      (Ψ.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
  have hint1 : Integrable (fun p : ℝ × ℝ =>
      ((η p.2 * |p.1 - p.2| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ p.1) (volume.prod volume) := by
    rw [integrable_prod_iff hm1]
    obtain ⟨B, hB0, hB⟩ := fhpbb2h_conv_abs_le η
    refine ⟨ae_of_all _ fun t => ((fhpbb2b_integrable η t).ofReal (𝕜 := ℂ)).mul_const (Ψ t), ?_⟩
    refine (Ψ.integrable.norm.const_mul (6 * B)).mono' hm1.norm.integral_prod_right'
      (ae_of_all _ fun t => ?_)
    have hpt : ∀ s : ℝ, ‖((η s * |t - s| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ t‖ =
        |η s * |t - s| ^ (-(1 / 2 : ℝ))| * ‖Ψ t‖ := fun s => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hJ0 : 0 ≤ ∫ s : ℝ, |η s * |t - s| ^ (-(1 / 2 : ℝ))| :=
      integral_nonneg fun s => abs_nonneg _
    show ‖∫ s : ℝ, ‖((η s * |t - s| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ t‖‖ ≤ 6 * B * ‖Ψ t‖
    simp only [hpt]
    rw [integral_mul_const, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hJ0 (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _)
  -- the second interchange: a product of integrable functions (variables `(s, τ)`)
  have hint2 : Integrable (fun p : ℝ × ℝ => (η p.1 : ℂ) * (((|p.2| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (((𝐞 (-(p.2 * p.1)) : Circle) : ℂ) * ψ p.2))) (volume.prod volume) := by
    refine (η.integrable.norm.mul_prod (fhpbb2h_integrable_rpow_mul_norm ψ)).mono' ?_
      (ae_of_all _ fun p => le_of_eq ?_)
    · have hc : Continuous (fun p : ℝ × ℝ => ((𝐞 (-(p.2 * p.1)) : Circle) : ℂ) * ψ p.2) :=
        (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
          (continuous_snd.mul continuous_fst).neg)).mul (ψ.continuous.comp continuous_snd)
      exact ((Complex.measurable_ofReal.comp (η.continuous.measurable.comp measurable_fst)).mul
        ((Complex.measurable_ofReal.comp (fhpbb2b_measurable_inverseHalf.comp measurable_snd)).mul
          hc.measurable)).aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe, one_mul,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg p.2) (-(1 / 2 : ℝ)))]
  -- the chain
  calc ∫ t : ℝ, (((∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * Ψ t
      = ∫ t : ℝ, ∫ s : ℝ, ((η s * |t - s| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ t := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        beta_reduce
        rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ s : ℝ, ∫ t : ℝ, ((η s * |t - s| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ t :=
        integral_integral_swap hint1
    _ = ∫ s : ℝ, (η s : ℂ) * ∫ τ : ℝ, ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ) := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        beta_reduce
        have h1 := integral_add_right_eq_self (μ := volume)
          (fun t : ℝ => ((η s * |t - s| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ t) s
        simp only [add_sub_cancel_right] at h1
        rw [← h1, ← fhpbb2h_weak_modulated ψ s, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        beta_reduce
        simp only [hΨ, Complex.ofReal_mul]
        ring
    _ = ∫ s : ℝ, ∫ τ : ℝ, (η s : ℂ) * (((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ)) :=
        integral_congr_ae (ae_of_all _ fun s => (integral_const_mul _ _).symm)
    _ = ∫ τ : ℝ, ∫ s : ℝ, (η s : ℂ) * (((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          (((𝐞 (-(τ * s)) : Circle) : ℂ) * ψ τ)) :=
        integral_integral_swap hint2
    _ = ∫ τ : ℝ, 𝓕 (fun t : ℝ => (η t : ℂ)) τ * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ := by
        refine integral_congr_ae (ae_of_all _ fun τ => ?_)
        beta_reduce
        rw [Real.fourier_real_eq, ← integral_mul_const, ← integral_mul_const]
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        beta_reduce
        simp only [Circle.smul_def, smul_eq_mul]
        rw [mul_comm τ s]
        ring

/-! ## The weak identity for `K` -/

/-- **Weak identity of the high-pass kernel.** If `K = I - η * I` is integrable, then
`∫ K ψ̂ = ∫ (1 - η̂) I ψ` for every complex Schwartz `ψ`. -/
theorem fhpbb2h_weak_identity {η : 𝓢(ℝ, ℝ)} {K : ℝ → ℝ}
    (hKdef : ∀ t, K t = |t| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ)))
    (hK : Integrable K) (ψ : 𝓢(ℝ, ℂ)) :
    ∫ t : ℝ, (K t : ℂ) * 𝓕 (⇑ψ) t =
      ∫ τ : ℝ, (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : 𝓢(ℝ, ℂ), 𝓕 (⇑ψ) = ⇑Ψ := ⟨𝓕 ψ, rfl⟩
  have hIΨ := fhpbb2h_integrable_inverseHalf_mul Ψ
  have hKΨ : Integrable (fun t : ℝ => (K t : ℂ) * Ψ t) :=
    (hK.ofReal (𝕜 := ℂ)).mul_bdd Ψ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => SchwartzMap.norm_le_seminorm ℝ Ψ x)
  have hJΨ : Integrable
      (fun t : ℝ => (((∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * Ψ t) := by
    refine (hIΨ.sub hKΨ).congr (ae_of_all _ fun t => ?_)
    simp only [Pi.sub_apply, hKdef, Complex.ofReal_sub]
    ring
  have hIψ := fhpbb2h_integrable_inverseHalf_mul ψ
  have hηc : Continuous (𝓕 (fun t : ℝ => (η t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (η.integrable.ofReal (𝕜 := ℂ))
  have hηIψ : Integrable (fun τ : ℝ =>
      𝓕 (fun t : ℝ => (η t : ℂ)) τ * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ) := by
    have h := hIψ.bdd_mul hηc.aestronglyMeasurable
      (ae_of_all _ fun τ => Real.norm_fourier_le_integral_norm (fun t : ℝ => (η t : ℂ)) τ)
    exact h.congr (ae_of_all _ fun τ => (mul_assoc _ _ _).symm)
  calc ∫ t : ℝ, (K t : ℂ) * 𝓕 (⇑ψ) t
      = ∫ t : ℝ, (((|t| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ t -
          (((∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * Ψ t) := by
        rw [hΨ]
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        beta_reduce
        simp only [hKdef, Complex.ofReal_sub]
        ring
    _ = (∫ t : ℝ, ((|t| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Ψ t) -
          ∫ t : ℝ, (((∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * Ψ t :=
        integral_sub hIΨ hJΨ
    _ = (∫ τ : ℝ, ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ) -
          ∫ τ : ℝ, 𝓕 (fun t : ℝ => (η t : ℂ)) τ * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ := by
        rw [← hΨ, fhpbb2f_inverseHalf_fourier_schwartz ψ, fhpbb2h_conv_pairing η ψ]
    _ = ∫ τ : ℝ, (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ := by
        rw [← integral_sub hIψ hηIψ]
        refine integral_congr_ae (ae_of_all _ fun τ => ?_)
        beta_reduce
        ring

/-! ## Pointwise identification -/

/-- The multiplier `M(τ) = (1 - η̂(τ)) |τ|^{-1/2}` is continuous when `η̂ = 1` near `0`: it
vanishes on a neighbourhood of `0`. -/
theorem fhpbb2h_continuous_multiplier (η : 𝓢(ℝ, ℝ))
    (hη : ∀ᶠ τ in 𝓝 (0 : ℝ), 𝓕 (fun t : ℝ => (η t : ℂ)) τ = 1) :
    Continuous (fun τ : ℝ =>
      (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hηc : Continuous (𝓕 (fun t : ℝ => (η t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (η.integrable.ofReal (𝕜 := ℂ))
  rw [continuous_iff_continuousAt]
  intro τ₀
  by_cases h0 : τ₀ = 0
  · subst h0
    refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) 0).congr ?_
    filter_upwards [hη] with τ hτ
    rw [hτ, sub_self, zero_mul]
  · have hI : ContinuousAt (fun τ : ℝ => |τ| ^ (-(1 / 2 : ℝ))) τ₀ :=
      (Real.continuousAt_rpow_const _ _ (Or.inl (abs_ne_zero.mpr h0))).comp
        continuous_abs.continuousAt
    exact ((continuous_const.sub hηc).continuousAt).mul
      (Complex.continuous_ofReal.continuousAt.comp hI)

/-- **Fourier transform of the high-pass kernel.** If `K = I - η * I` is integrable and `η̂ = 1`
near `0`, then `K̂(τ) = (1 - η̂(τ)) |τ|^{-1/2}` for every `τ` (at `τ = 0` both sides vanish). -/
theorem fhpbb2h_fourier_eq {η : 𝓢(ℝ, ℝ)}
    (hη : ∀ᶠ τ in 𝓝 (0 : ℝ), 𝓕 (fun t : ℝ => (η t : ℂ)) τ = 1) {K : ℝ → ℝ}
    (hKdef : ∀ t, K t = |t| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ)))
    (hK : Integrable K) :
    𝓕 (fun t : ℝ => (K t : ℂ)) = fun τ : ℝ =>
      (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hKc : Integrable (fun t : ℝ => (K t : ℂ)) := hK.ofReal
  have hcK : Continuous (𝓕 (fun t : ℝ => (K t : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hKc
  have hcM := fhpbb2h_continuous_multiplier η hη
  refine (hcK.ae_eq_iff_eq volume hcM).mp ?_
  refine ae_eq_of_integral_contDiff_smul_eq hcK.locallyIntegrable hcM.locallyIntegrable
    (fun g hg hgs => ?_)
  have hgs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgs.comp_left (map_zero _)
  obtain ⟨ψ, hψg⟩ : ∃ ψ : 𝓢(ℝ, ℂ), ∀ x, ψ x = (g x : ℂ) :=
    ⟨hgs'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg), fun x => rfl⟩
  calc ∫ x : ℝ, g x • 𝓕 (fun t : ℝ => (K t : ℂ)) x
      = ∫ x : ℝ, ψ x * 𝓕 (fun t : ℝ => (K t : ℂ)) x := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [hψg, Complex.real_smul]
    _ = ∫ x : ℝ, 𝓕 (⇑ψ) x * (K x : ℂ) := fhpbb2f_integral_mul_fourier hKc ψ.integrable
    _ = ∫ x : ℝ, (K x : ℂ) * 𝓕 (⇑ψ) x :=
        integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    _ = ∫ τ : ℝ, (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ψ τ :=
        fhpbb2h_weak_identity hKdef hK ψ
    _ = ∫ x : ℝ, g x • ((1 - 𝓕 (fun t : ℝ => (η t : ℂ)) x) *
          ((|x| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [hψg, Complex.real_smul]
        ring

/-- **The one-dimensional high-pass kernel.** If `K = I - η * I` is integrable and `η̂ = 1` near `0`,
then `∫ K = 0` and `K̂(τ) = (1 - η̂(τ)) |τ|^{-1/2}` for every `τ`. -/
theorem fhpbb2h_kernelFourier_main {η : 𝓢(ℝ, ℝ)}
    (hη : ∀ᶠ τ in 𝓝 (0 : ℝ), 𝓕 (fun t : ℝ => (η t : ℂ)) τ = 1) {K : ℝ → ℝ}
    (hKdef : ∀ t, K t = |t| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ)))
    (hK : Integrable K) :
    ∫ t, K t = 0 ∧
      ∀ τ : ℝ, 𝓕 (fun t : ℝ => (K t : ℂ)) τ =
        (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have hF := fhpbb2h_fourier_eq hη hKdef hK
  refine ⟨?_, fun τ => congrFun hF τ⟩
  have h0 : 𝓕 (fun t : ℝ => (K t : ℂ)) 0 =
      (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) 0) * ((|(0 : ℝ)| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
    congrFun hF 0
  have hlhs : 𝓕 (fun t : ℝ => (K t : ℂ)) 0 = ((∫ t, K t : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    beta_reduce
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  have hrhs : ((|(0 : ℝ)| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 0 := by
    rw [abs_zero, Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0), Complex.ofReal_zero]
  rw [hlhs, hrhs, mul_zero] at h0
  exact_mod_cast h0

end ParabolicRectifiability.FractionalKernel
