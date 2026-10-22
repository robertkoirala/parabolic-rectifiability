import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Prod

/-! # Time convolution of a compact smooth function with an `L¹` kernel

Proof of `FhpbcTimeConvolutionStatement` (`fhpbc_b2_timeConvolution`; an arbitrary integrable
real kernel suffices). For an integrable `k : ℝ → ℝ` and a real compact smooth `φ` on `FourierSpace m = ℝ^m × ℝ`, the
time convolution `(k *_t φ)(u,t) = ∫ k(s) φ(u, t - s) ds`

* is smooth everywhere: in coordinates it is the one-dimensional Mathlib convolution
  `k ⋆ φ(u, ·)` with the spatial variable `u` as a parameter, and
  `contDiffOn_convolution_right_with_param` moves all derivatives to the compactly supported
  smooth `φ` (`k` only needs to be locally integrable);
* is supported spatially in the spatial projection of `tsupport φ`;
* is integrable, with `∫ k *_t φ = (∫ k)(∫ φ)`: the integrand `(x,s) ↦ k(s) φ(x - s e_t)` is
  integrable on the product (Tonelli and translation invariance of the volume), then Fubini;
* has Fourier transform `𝓕(k *_t φ)(ζ) = k̂(τ) φ̂(ζ)` with `τ = (ofLp ζ).2`: Fubini for the
  integrand multiplied by the unimodular phase, and the translation
  `⟪y + s e_t, ζ⟫ = ⟪y, ζ⟫ + s τ`.

Smoothness is proved separately from the shear/Fourier transport. Helper prefix `fhpbb2c_`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform Convolution
  RealInnerProductSpace

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-- Proof-local shortcut (as in the construction of `testKernel`): the default
instance search for `ContinuousSMul ℝ (FourierSpace m)` times out. -/
local instance fhpbb2c_continuousSMul (m : ℕ) : ContinuousSMul ℝ (FourierSpace m) :=
  IsBoundedSMul.continuousSMul

/-! ## Smoothness -/

/-- In coordinates `x = (u,t)`, the time convolution is the one-dimensional Mathlib convolution
of `k` with the time slice `φ(u, ·)`, evaluated at `t`. -/
theorem fhpbb2c_timeConvolution_eq_convolution (k : ℝ → ℝ) (φ : FourierSpace m → ℝ)
    (x : FourierSpace m) :
    fhp_timeConvolution k φ x =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun t : ℝ => φ (WithLp.toLp 2 ((WithLp.ofLp x).1, t)))) (WithLp.ofLp x).2 := by
  rw [convolution_def, fhp_timeConvolution]
  congr 1
  funext s
  have hx : x - s • timeVector m =
      WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2 - s) := by
    apply WithLp.ofLp_injective 2
    rw [coordinates_sub_timeVector, WithLp.ofLp_toLp]
  rw [hx, ContinuousLinearMap.mul_apply']

/-- Smoothness everywhere: every derivative falls on the compactly supported smooth `φ`, and the
locally integrable kernel `k` is a fixed weight. -/
theorem fhpbb2c_contDiff (k : ℝ → ℝ) (hk : Integrable k) (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (fhp_timeConvolution k φ) := by
  let g : Spatial m → ℝ → ℝ := fun u t => φ (WithLp.toLp 2 (u, t))
  have hK : IsCompact (timeCoordinate m '' tsupport φ) :=
    hφc.image (continuous_timeCoordinate m)
  have hgs : ∀ u : Spatial m, ∀ t : ℝ, u ∈ (univ : Set (Spatial m)) →
      t ∉ timeCoordinate m '' tsupport φ → g u t = 0 := by
    intro u t _ ht
    by_contra h
    exact ht ⟨WithLp.toLp 2 (u, t), subset_tsupport φ h, rfl⟩
  have hgsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (↿g)
      ((univ : Set (Spatial m)) ×ˢ (univ : Set ℝ)) := by
    have hcomp : (↿g) = φ ∘ (WithLp.prodContinuousLinearEquiv 2 ℝ (Spatial m) ℝ).symm := by
      funext q
      rfl
    rw [hcomp]
    exact (hφ.comp (ContinuousLinearEquiv.contDiff _)).contDiffOn
  have hconv := contDiffOn_convolution_right_with_param (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hK hgs hk.locallyIntegrable hgsmooth
  rw [univ_prod_univ, contDiffOn_univ] at hconv
  have heq : fhp_timeConvolution k φ =
      (fun q : Spatial m × ℝ => (k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g q.1) q.2) ∘
        (WithLp.prodContinuousLinearEquiv 2 ℝ (Spatial m) ℝ) := by
    funext x
    exact fhpbb2c_timeConvolution_eq_convolution k φ x
  rw [heq]
  exact hconv.comp (ContinuousLinearEquiv.contDiff _)

/-! ## Spatial support -/

/-- The time convolution vanishes at every `(u,t)` with `u` outside the spatial projection of
`tsupport φ`, a compact set. -/
theorem fhpbb2c_spatialSupport (k : ℝ → ℝ) (φ : FourierSpace m → ℝ)
    (hφc : HasCompactSupport φ) :
    ∃ A : Set (Spatial m), IsCompact A ∧
      fhp_IsSpatiallySupportedIn (fhp_timeConvolution k φ) A := by
  refine ⟨(fun x : FourierSpace m => (WithLp.ofLp x).1) '' tsupport φ,
    hφc.image (fourierCoordinatesHomeomorph m).continuous.fst, ?_⟩
  intro x hx
  have hzero : ∀ s : ℝ, k s * φ (x - s • timeVector m) = 0 := by
    intro s
    have h0 : φ (x - s • timeVector m) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      apply hx
      refine ⟨x - s • timeVector m, hs, ?_⟩
      show (WithLp.ofLp (x - s • timeVector m)).1 = (WithLp.ofLp x).1
      rw [coordinates_sub_timeVector]
    rw [h0, mul_zero]
  rw [fhp_timeConvolution]
  simp only [hzero, integral_zero]

/-! ## The product integrand: integrability and the total integral -/

/-- The shear integrand `(x,s) ↦ k(s) φ(x - s e_t)` is integrable on the product: for each `s`
its `x`-integral of the norm is `|k(s)| ∫ |φ|` (translation invariance). -/
theorem fhpbb2c_integrable_prod (k : ℝ → ℝ) (hk : Integrable k) (φ : FourierSpace m → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : FourierSpace m × ℝ => k p.2 * φ (p.1 - p.2 • timeVector m))
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hmeas : AEStronglyMeasurable
      (fun p : FourierSpace m × ℝ => k p.2 * φ (p.1 - p.2 • timeVector m))
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) := by
    refine (hk.aestronglyMeasurable.comp_snd).mul ?_
    exact (hφ.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall fun s => ?_, ?_⟩
  · exact (hφi.comp_sub_right (s • timeVector m)).const_mul (k s)
  · have hnorm : ∀ s : ℝ, ∫ x, ‖k s * φ (x - s • timeVector m)‖ = ‖k s‖ * ∫ x, ‖φ x‖ := by
      intro s
      simp_rw [norm_mul]
      rw [integral_const_mul]
      congr 1
      exact integral_sub_right_eq_self (fun x => ‖φ x‖) (s • timeVector m)
    refine (hk.norm.mul_const (∫ x, ‖φ x‖)).congr (Eventually.of_forall fun s => ?_)
    exact (hnorm s).symm

/-- Integrability of the time convolution (the `x`-marginal of an integrable product function). -/
theorem fhpbb2c_integrable (k : ℝ → ℝ) (hk : Integrable k) (φ : FourierSpace m → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fhp_timeConvolution k φ) :=
  (fhpbb2c_integrable_prod k hk φ hφ hφc).integral_prod_left

/-- The total integral `∫ k *_t φ = (∫ k)(∫ φ)` (Fubini and translation invariance). -/
theorem fhpbb2c_integral (k : ℝ → ℝ) (hk : Integrable k) (φ : FourierSpace m → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∫ x, fhp_timeConvolution k φ x = (∫ s, k s) * ∫ x, φ x := by
  have h := fhpbb2c_integrable_prod k hk φ hφ hφc
  have hslice : ∀ s : ℝ, ∫ x, k s * φ (x - s • timeVector m) = k s * ∫ x, φ x := by
    intro s
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self φ (s • timeVector m)
  calc ∫ x, fhp_timeConvolution k φ x
      = ∫ x, ∫ s, k s * φ (x - s • timeVector m) := rfl
    _ = ∫ s, ∫ x, k s * φ (x - s • timeVector m) :=
        integral_integral_swap (f := fun (x : FourierSpace m) (s : ℝ) =>
          k s * φ (x - s • timeVector m)) h
    _ = ∫ s, k s * ∫ x, φ x := by simp_rw [hslice]
    _ = (∫ s, k s) * ∫ x, φ x := integral_mul_const _ _

/-! ## The Fourier transform -/

/-- The phase-weighted shear integrand is integrable on the product (the phase is unimodular). -/
theorem fhpbb2c_fourier_integrable_prod (k : ℝ → ℝ) (hk : Integrable k)
    (φ : FourierSpace m → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (ζ : FourierSpace m) :
    Integrable (fun p : FourierSpace m × ℝ =>
        (𝐞 (-⟪p.1, ζ⟫) : ℂ) * ((k p.2 * φ (p.1 - p.2 • timeVector m) : ℝ) : ℂ))
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) := by
  have h1 := (fhpbb2c_integrable_prod k hk φ hφ hφc).ofReal (𝕜 := ℂ)
  refine h1.bdd_mul (c := 1) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have he : Continuous 𝐞 := Real.continuous_fourierChar
    fun_prop
  · exact Eventually.of_forall fun p => (Circle.norm_coe _).le

/-- One time slice of the Fourier integral: translating `x = y + s e_t` turns the phase
`e(-⟪x, ζ⟫)` into `e(-⟪y, ζ⟫) e(-s τ)`. -/
theorem fhpbb2c_fourier_slice (k : ℝ → ℝ) (φ : FourierSpace m → ℝ) (ζ : FourierSpace m)
    (s : ℝ) :
    ∫ x, (𝐞 (-⟪x, ζ⟫) : ℂ) * ((k s * φ (x - s • timeVector m) : ℝ) : ℂ) =
      (𝐞 (-(s * (WithLp.ofLp ζ).2)) • (k s : ℂ)) * ∫ x, 𝐞 (-⟪x, ζ⟫) • (φ x : ℂ) := by
  have htr := integral_add_right_eq_self (μ := (volume : Measure (FourierSpace m)))
    (fun x => (𝐞 (-⟪x, ζ⟫) : ℂ) * ((k s * φ (x - s • timeVector m) : ℝ) : ℂ))
    (s • timeVector m)
  rw [← htr, ← integral_const_mul]
  congr 1
  funext y
  have hin : ⟪y + s • timeVector m, ζ⟫ = ⟪y, ζ⟫ + s * (WithLp.ofLp ζ).2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_comm ζ (timeVector m), inner_timeVector,
      timeCoordinate_apply]
  simp only [add_sub_cancel_right, hin, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul,
    Circle.smul_def, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The Fourier identity `𝓕(k *_t φ)(ζ) = k̂(τ) φ̂(ζ)`, `τ = (ofLp ζ).2`, with Mathlib's phase. -/
theorem fhpbb2c_fourier (k : ℝ → ℝ) (hk : Integrable k) (φ : FourierSpace m → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (ζ : FourierSpace m) :
    𝓕 (fun x : FourierSpace m => (fhp_timeConvolution k φ x : ℂ)) ζ =
      𝓕 (fun s : ℝ => (k s : ℂ)) (WithLp.ofLp ζ).2 *
        𝓕 (fun x : FourierSpace m => (φ x : ℂ)) ζ := by
  have hF := fhpbb2c_fourier_integrable_prod k hk φ hφ hφc ζ
  have e1 : 𝓕 (fun x : FourierSpace m => (fhp_timeConvolution k φ x : ℂ)) ζ =
      ∫ x, 𝐞 (-⟪x, ζ⟫) • ((fhp_timeConvolution k φ x : ℝ) : ℂ) := Real.fourier_eq _ ζ
  have e2 : 𝓕 (fun s : ℝ => (k s : ℂ)) (WithLp.ofLp ζ).2 =
      ∫ s : ℝ, 𝐞 (-(s * (WithLp.ofLp ζ).2)) • (k s : ℂ) := Real.fourier_real_eq _ _
  have e3 : 𝓕 (fun x : FourierSpace m => (φ x : ℂ)) ζ =
      ∫ x, 𝐞 (-⟪x, ζ⟫) • (φ x : ℂ) := Real.fourier_eq _ ζ
  have hL : ∀ x : FourierSpace m, 𝐞 (-⟪x, ζ⟫) • ((fhp_timeConvolution k φ x : ℝ) : ℂ) =
      ∫ s, (𝐞 (-⟪x, ζ⟫) : ℂ) * ((k s * φ (x - s • timeVector m) : ℝ) : ℂ) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, fhp_timeConvolution, ← integral_complex_ofReal,
      ← integral_const_mul]
  rw [e1, e2, e3]
  calc ∫ x, 𝐞 (-⟪x, ζ⟫) • ((fhp_timeConvolution k φ x : ℝ) : ℂ)
      = ∫ x, ∫ s, (𝐞 (-⟪x, ζ⟫) : ℂ) * ((k s * φ (x - s • timeVector m) : ℝ) : ℂ) :=
        integral_congr_ae (Eventually.of_forall fun x => hL x)
    _ = ∫ s, ∫ x, (𝐞 (-⟪x, ζ⟫) : ℂ) * ((k s * φ (x - s • timeVector m) : ℝ) : ℂ) :=
        integral_integral_swap (f := fun (x : FourierSpace m) (s : ℝ) =>
          (𝐞 (-⟪x, ζ⟫) : ℂ) * ((k s * φ (x - s • timeVector m) : ℝ) : ℂ)) hF
    _ = ∫ s, (𝐞 (-(s * (WithLp.ofLp ζ).2)) • (k s : ℂ)) *
          ∫ x, 𝐞 (-⟪x, ζ⟫) • (φ x : ℂ) :=
        integral_congr_ae (Eventually.of_forall fun s => fhpbb2c_fourier_slice k φ ζ s)
    _ = (∫ s : ℝ, 𝐞 (-(s * (WithLp.ofLp ζ).2)) • (k s : ℂ)) *
          ∫ x, 𝐞 (-⟪x, ζ⟫) • (φ x : ℂ) := integral_mul_const _ _

/-! ## The statement -/

/-- **Time convolution with an `L¹` kernel** (`fhpbc_b2_timeConvolution`, of type
`FhpbcTimeConvolutionStatement`): for every integrable real `k` and real compact smooth `φ` on
`FourierSpace m`, `k *_t φ` is smooth, supported spatially in a compact set, integrable,
`∫ k *_t φ = (∫ k)(∫ φ)`, and `𝓕(k *_t φ)(ζ) = k̂((ofLp ζ).2) φ̂(ζ)`. No hypotheses. -/
theorem fhpbc_b2_timeConvolution_proof : FhpbcTimeConvolutionStatement := by
  intro k hk m φ hφ hφc
  exact ⟨fhpbb2c_contDiff k hk φ hφ hφc, fhpbb2c_spatialSupport k φ hφc,
    fhpbb2c_integrable k hk φ hφ.continuous hφc, fhpbb2c_integral k hk φ hφ.continuous hφc,
    fun ζ => fhpbb2c_fourier k hk φ hφ.continuous hφc ζ⟩

end ParabolicRectifiability.Foundations
