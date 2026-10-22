import ParabolicRectifiability.Foundations.Statements.HighPass

/-! # Critical Sobolev localization: the fixed cutoff and the high-pass statements

Preliminaries for `ba1_critical_sobolev_localization_proof`, which takes the high-pass
statements `HighPassKernelStatement` (kernel bounds) and `HighPassIdentityStatement` (the
high-pass identity) as hypotheses. This file provides:

* **one fixed admissible cutoff** `b1loc_cutoff` (a real even Schwartz `η`
  whose transform is smooth, compactly supported and one near zero), with `∫ η = 1`; all
  constants of the localization may depend on this fixed choice;
* **kernel facts** for `K = I - η * I`: `K ∈ L¹`, `C¹` off `0`, `|K t| ≤ 2C|t|^{-1/2}` for
  `0 < |t| ≤ 1`, combined `K, K'` tails from `j = 0, 1`, and
  `√|τ| |K̂(τ)| = |1 - η̂(τ)| ≤ 1 + ‖η̂‖_∞`;
* **transport of the high-pass identity** to `parabolicVolume m` on `Space m` for the **given**
  representative, keeping both convergence clauses, through
  `Ψ(Ψ⁻¹p - s e_t) = point p.1 (p.2.val - s)`; and the same identity in ordinary coordinates
  `FourierSpace m`, where the localization is assembled (`b1loc_highPass_coordinates`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform ComplexConjugate

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability ParabolicRectifiability.Foundations
open ParabolicRectifiability.HalfTimeDerivative

/-! ## An admissible cutoff exists, and `∫ η = 1` -/

/-- An even smooth bump on `ℝ`: one on `[-1/2, 1/2]`, supported in `(-1, 1)`. -/
def b1loc_bump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- `χ`, complexified. -/
def b1loc_chiFun (τ : ℝ) : ℂ := (b1loc_bump τ : ℂ)

theorem b1loc_chiFun_contDiff : ContDiff ℝ ∞ b1loc_chiFun :=
  Complex.ofRealCLM.contDiff.comp b1loc_bump.contDiff

theorem b1loc_chiFun_hasCompactSupport : HasCompactSupport b1loc_chiFun :=
  b1loc_bump.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero

/-- `χ` as a complex Schwartz function. -/
def b1loc_chi : 𝓢(ℝ, ℂ) :=
  b1loc_chiFun_hasCompactSupport.toSchwartzMap b1loc_chiFun_contDiff

theorem b1loc_chi_apply (τ : ℝ) : b1loc_chi τ = b1loc_chiFun τ := rfl

/-- `χ` is even, so its inverse and forward transforms agree. -/
theorem b1loc_fourierInv_chi : 𝓕⁻ (⇑b1loc_chi) = 𝓕 (⇑b1loc_chi) := by
  have h : (fun x : ℝ => b1loc_chi (-x)) = ⇑b1loc_chi := by
    funext x
    show b1loc_chiFun (-x) = b1loc_chiFun x
    simp only [b1loc_chiFun, ContDiffBump.neg]
  rw [Real.fourierInv_eq_fourier_comp_neg, h]

theorem b1loc_fourierInv_chi_schwartz : 𝓕⁻ b1loc_chi = 𝓕 b1loc_chi := by
  ext x
  rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, b1loc_fourierInv_chi]

/-- `η_ℂ = 𝓕 χ` (forward transform). -/
def b1loc_etaC : 𝓢(ℝ, ℂ) := 𝓕 b1loc_chi

theorem b1loc_etaC_coe : ⇑b1loc_etaC = 𝓕 (⇑b1loc_chi) :=
  SchwartzMap.fourier_coe b1loc_chi

theorem b1loc_fourier_etaC : 𝓕 b1loc_etaC = b1loc_chi := by
  rw [b1loc_etaC, ← b1loc_fourierInv_chi_schwartz, FourierInvPair.fourier_fourierInv_eq]

theorem b1loc_etaC_neg (t : ℝ) : b1loc_etaC (-t) = b1loc_etaC t := by
  rw [b1loc_etaC_coe, ← Real.fourierInv_eq_fourier_neg, b1loc_fourierInv_chi]

theorem b1loc_etaC_conj (t : ℝ) : conj (b1loc_etaC t) = b1loc_etaC t := by
  have h1 : b1loc_etaC t = ∫ v : ℝ, Real.fourierChar (-(v * t)) • b1loc_chi v := by
    rw [b1loc_etaC_coe, Real.fourier_real_eq]
  have h2 : b1loc_etaC t = ∫ v : ℝ, Real.fourierChar (v * t) • b1loc_chi v := by
    rw [b1loc_etaC_coe, ← b1loc_fourierInv_chi, Real.fourierInv_eq_fourier_neg,
      Real.fourier_real_eq]
    simp only [mul_neg, neg_neg]
  conv_lhs => rw [h1]
  conv_rhs => rw [h2]
  rw [← integral_conj]
  congr 1
  funext v
  simp only [Circle.smul_def, smul_eq_mul]
  rw [map_mul, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg,
    b1loc_chi_apply, b1loc_chiFun, Complex.conj_ofReal]

/-- The real cutoff `η = Re η_ℂ` (and `η_ℂ` is real). -/
def b1loc_eta : 𝓢(ℝ, ℝ) := SchwartzMap.postcompCLM Complex.reCLM b1loc_etaC

theorem b1loc_eta_ofReal (t : ℝ) : ((b1loc_eta t : ℝ) : ℂ) = b1loc_etaC t := by
  rw [b1loc_eta, SchwartzMap.postcompCLM_apply, Complex.reCLM_apply]
  exact Complex.conj_eq_iff_re.mp (b1loc_etaC_conj t)

theorem b1loc_eta_fourier : 𝓕 (fun t : ℝ => (b1loc_eta t : ℂ)) = b1loc_chiFun := by
  have h : (fun t : ℝ => (b1loc_eta t : ℂ)) = ⇑b1loc_etaC := funext b1loc_eta_ofReal
  rw [h, ← SchwartzMap.fourier_coe, b1loc_fourier_etaC]
  rfl

/-- **An admissible frequency cutoff exists.** -/
theorem b1loc_exists_cutoff : ∃ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η := by
  refine ⟨b1loc_eta, fun t => ?_, ?_, ?_, ?_⟩
  · rw [b1loc_eta, SchwartzMap.postcompCLM_apply, SchwartzMap.postcompCLM_apply,
      b1loc_etaC_neg]
  · rw [b1loc_eta_fourier]
    exact b1loc_chiFun_contDiff
  · rw [b1loc_eta_fourier]
    exact b1loc_chiFun_hasCompactSupport
  · rw [b1loc_eta_fourier]
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)]
      with τ hτ
    rw [b1loc_chiFun, b1loc_bump.one_of_mem_closedBall hτ, Complex.ofReal_one]

/-- Every admissible cutoff has `∫ η = η̂(0) = 1`. -/
theorem b1loc_integral_cutoff (η : 𝓢(ℝ, ℝ)) (hη : fhp_IsFrequencyCutoff η) :
    ∫ s : ℝ, η s = 1 := by
  have h0 : 𝓕 (fun t : ℝ => (η t : ℂ)) 0 = 1 := hη.2.2.2.self_of_nhds
  rw [Real.fourier_real_eq] at h0
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul,
    integral_complex_ofReal] at h0
  exact_mod_cast h0

/-! ## The fixed cutoff -/

/-- **The fixed admissible cutoff** of the localization (the kernel constants may depend on
this fixed choice): the real part of the
forward transform of an even bump that is one on `[-1/2, 1/2]`. -/
def b1loc_cutoff : 𝓢(ℝ, ℝ) := b1loc_eta

theorem b1loc_cutoff_admissible : fhp_IsFrequencyCutoff b1loc_cutoff := by
  refine ⟨fun t => ?_, ?_, ?_, ?_⟩
  · rw [b1loc_cutoff, b1loc_eta, SchwartzMap.postcompCLM_apply, SchwartzMap.postcompCLM_apply,
      b1loc_etaC_neg]
  · rw [b1loc_cutoff, b1loc_eta_fourier]
    exact b1loc_chiFun_contDiff
  · rw [b1loc_cutoff, b1loc_eta_fourier]
    exact b1loc_chiFun_hasCompactSupport
  · rw [b1loc_cutoff, b1loc_eta_fourier]
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)]
      with τ hτ
    rw [b1loc_chiFun, b1loc_bump.one_of_mem_closedBall hτ, Complex.ofReal_one]

theorem b1loc_integral_cutoff_eq_one : ∫ s : ℝ, b1loc_cutoff s = 1 :=
  b1loc_integral_cutoff b1loc_cutoff b1loc_cutoff_admissible

/-! ## Kernel facts and transport -/

/-- The kernel facts used in the localization, for every admissible cutoff: integrability,
`C¹` regularity off `0`, the bound near `0`, the tails, and the bound on `√|τ| |K̂(τ)|`. -/
theorem b1loc_kernel_adapter (hK : HighPassKernelStatement) (η : 𝓢(ℝ, ℝ))
    (hη : fhp_IsFrequencyCutoff η) :
    Integrable (fhp_highPassKernel η) ∧ ContDiffOn ℝ 1 (fhp_highPassKernel η) {0}ᶜ ∧
    (∃ C : ℝ, ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      |fhp_highPassKernel η t| ≤ C * |t| ^ (-(1 / 2 : ℝ))) ∧
    (∀ N : ℕ, ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
      |fhp_highPassKernel η t| + |deriv (fhp_highPassKernel η) t| ≤ C * |t| ^ (-(N : ℤ))) ∧
    (∃ C : ℝ, ∀ τ : ℝ,
      Real.sqrt |τ| * ‖𝓕 (fun t : ℝ => (fhp_highPassKernel η t : ℂ)) τ‖ ≤ C) := by
  obtain ⟨-, hint, -, hsmooth, ⟨C0, hC0⟩, htail, hfour, -⟩ := hK η hη
  refine ⟨hint, hsmooth.of_le (by exact_mod_cast le_top), ?_, ?_, ?_⟩
  · refine ⟨2 * |C0|, fun t ht0 ht1 => ?_⟩
    have hpos : 0 < |t| := abs_pos.mpr ht0
    have hr : 1 ≤ |t| ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos ht1 (by norm_num)
    calc |fhp_highPassKernel η t| ≤ C0 * (1 + |t| ^ (-(1 / 2 : ℝ))) := hC0 t ht1
      _ ≤ |C0| * (1 + |t| ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self C0) (by positivity)
      _ ≤ |C0| * (2 * |t| ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C0)
      _ = 2 * |C0| * |t| ^ (-(1 / 2 : ℝ)) := by ring
  · intro N
    obtain ⟨C₁, h₁⟩ := htail 0 N
    obtain ⟨C₂, h₂⟩ := htail 1 N
    refine ⟨C₁ + C₂, fun t ht => ?_⟩
    have hz : |t| ^ (-(N : ℝ)) = |t| ^ (-(N : ℤ)) := by
      rw [← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast]
    have e1 := h₁ t ht
    have e2 := h₂ t ht
    rw [iteratedDeriv_zero] at e1
    rw [iteratedDeriv_one] at e2
    rw [← hz, add_mul]
    exact add_le_add e1 e2
  · obtain ⟨Cη, hCη⟩ := hη.2.1.continuous.bounded_above_of_compact_support hη.2.2.1
    have hCη0 : 0 ≤ Cη := le_trans (norm_nonneg _) (hCη 0)
    refine ⟨1 + Cη, fun τ => ?_⟩
    rcases eq_or_ne τ 0 with rfl | hτ
    · rw [abs_zero, Real.sqrt_zero, zero_mul]
      linarith
    · rw [hfour τ hτ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg τ) _)]
      have hpos : 0 < |τ| := abs_pos.mpr hτ
      have hsq : Real.sqrt |τ| * |τ| ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hpos]
        norm_num
      calc Real.sqrt |τ| * (‖1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ‖ * |τ| ^ (-(1 / 2 : ℝ)))
          = ‖1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ‖ * (Real.sqrt |τ| * |τ| ^ (-(1 / 2 : ℝ))) := by
            ring
        _ = ‖1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ‖ := by rw [hsq, mul_one]
        _ ≤ ‖(1 : ℂ)‖ + ‖𝓕 (fun t : ℝ => (η t : ℂ)) τ‖ := norm_sub_le _ _
        _ ≤ 1 + Cη := by
            rw [norm_one]
            linarith [hCη τ]

/-- `Ψ(Ψ⁻¹p - s e_t) = (p.1, p.2 - s)`. -/
theorem b1loc_shift (m : ℕ) (p : Space m) (s : ℝ) :
    fourierToParabolic m ((fourierToParabolic m).symm p - s • timeVector m) =
      point p.1 (p.2.val - s) := by
  rw [fourierToParabolic_apply, coordinates_sub_timeVector, fourierToParabolic_symm_apply]

/-- **Transport of the high-pass identity to the standard base** `Space m`, with both convergence clauses, for the
given representative, almost everywhere for `parabolicVolume m`. -/
theorem b1loc_transport (hI : HighPassIdentityStatement) (η : 𝓢(ℝ, ℝ))
    (hη : fhp_IsFrequencyCutoff η) (m : ℕ) (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ)
    (hL : LipschitzWith L F) (hB : HasStandardParabolicBMOBound m f B)
    (hrep : RepresentsStandardHalfTimeDerivative m F f) :
    ∀ᵐ p ∂parabolicVolume m,
      Integrable (fun s : ℝ => η s * F (point p.1 (p.2.val - s))) ∧
      Integrable (fun s : ℝ => fhp_highPassKernel η s * f (point p.1 (p.2.val - s))) ∧
      F p = (∫ s : ℝ, η s * F (point p.1 (p.2.val - s))) +
        ∫ s : ℝ, fhp_highPassKernel η s * f (point p.1 (p.2.val - s)) := by
  have hG : (fun x => F (fourierToParabolic m x)) ∘ (fourierToParabolic m).symm = F := by
    funext z
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  have hg : (fun x => f (fourierToParabolic m x)) ∘ (fourierToParabolic m).symm = f := by
    funext z
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  obtain ⟨h1, h2, h3⟩ := hI m (fun x => F (fourierToParabolic m x))
    (fun x => f (fourierToParabolic m x)) ⟨L, by rw [hG]; exact hL⟩
    ⟨B, by rw [hg]; exact hB⟩ hrep η hη
  have hall : ∀ᵐ x ∂(volume : Measure (FourierSpace m)),
      Integrable (fun s : ℝ => η s * F (fourierToParabolic m (x - s • timeVector m))) ∧
      Integrable (fun s : ℝ =>
        fhp_highPassKernel η s * f (fourierToParabolic m (x - s • timeVector m))) ∧
      F (fourierToParabolic m x) - fhp_timeConvolution η (fun y => F (fourierToParabolic m y)) x =
        fhp_timeConvolution (fhp_highPassKernel η) (fun y => f (fourierToParabolic m y)) x := by
    filter_upwards [h2, h3] with x hx2 hx3
    exact ⟨h1 x, hx2, hx3⟩
  have htr := (fourierToParabolic_symm_measurePreserving m).quasiMeasurePreserving.ae hall
  filter_upwards [htr] with p hp
  obtain ⟨a1, a2, a3⟩ := hp
  have hsymm : (fourierToParabolicMeasurableEquiv m).symm p = (fourierToParabolic m).symm p :=
    rfl
  rw [hsymm] at a1 a2 a3
  simp only [b1loc_shift, fhp_timeConvolution, Homeomorph.apply_symm_apply] at a1 a2 a3
  refine ⟨a1, a2, ?_⟩
  linarith

/-- **The high-pass identity in ordinary coordinates** for the given `F`, `f` on the standard base: the identity
`G - η *_t G = K *_t g` a.e. on `FourierSpace m` for `G = F ∘ Ψ`, `g = f ∘ Ψ`, with the
low-pass integrals convergent at every point and the high-pass integrals at almost every point.
This is the form used to assemble the localization, which lives on `FourierSpace m`. -/
theorem b1loc_highPass_coordinates (hI : HighPassIdentityStatement) (η : 𝓢(ℝ, ℝ))
    (hη : fhp_IsFrequencyCutoff η) (m : ℕ) (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ)
    (hL : LipschitzWith L F) (hB : HasStandardParabolicBMOBound m f B)
    (hrep : RepresentsStandardHalfTimeDerivative m F f) :
    (∀ x : FourierSpace m,
      Integrable (fun s : ℝ => η s * F (fourierToParabolic m (x - s • timeVector m)))) ∧
    (∀ᵐ x ∂(volume : Measure (FourierSpace m)),
      Integrable (fun s : ℝ =>
        fhp_highPassKernel η s * f (fourierToParabolic m (x - s • timeVector m)))) ∧
    (fun x => F (fourierToParabolic m x) -
        fhp_timeConvolution η (fun y => F (fourierToParabolic m y)) x) =ᵐ[volume]
      fhp_timeConvolution (fhp_highPassKernel η) (fun y => f (fourierToParabolic m y)) := by
  have hG : (fun x => F (fourierToParabolic m x)) ∘ (fourierToParabolic m).symm = F := by
    funext z
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  have hg : (fun x => f (fourierToParabolic m x)) ∘ (fourierToParabolic m).symm = f := by
    funext z
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  exact hI m (fun x => F (fourierToParabolic m x)) (fun x => f (fourierToParabolic m x))
    ⟨L, by rw [hG]; exact hL⟩ ⟨B, by rw [hg]; exact hB⟩ hrep η hη

end ParabolicRectifiability.Characterization
