import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Completion
import ParabolicRectifiability.Foundations.Proofs.CompactBridge

/-! # Invariance of the half-time BMO bound under a spatial affine function

`d1e_affine_invariance_proof` has the type `d1e_AffineInvarianceStatement`: adding a
time-independent spatial affine function `c + ℓ(u)` to a function with a half-time BMO bound
keeps that bound, with the same representative. This is an adaptation of the corresponding
statement for constants.

Route.
* **Lipschitz clause.** `p ↦ c + ℓ(p.1)` is `‖ℓ‖`-Lipschitz on `Space m`; add the existential
  constant of `H`. The public definition does not charge this constant against `B`.
* **The affine part.** For `A(u) = c + ℓ(u)` and a real compact smooth test `φ`, `Aφ` is again
  a real compact smooth test and, since the kernel shifts in time only,
  `testKernel(Aφ) = A · testKernel(φ)` pointwise. Kernel integrability
  (`integrable_testKernel_of_hasCompactSupport`) and cancellation
  (`fcond_integral_testKernel_eq_zero`) for `Aφ`, transferred to `A · |D_t|^{1/2}φ` by
  `testKernel_ae_halfTimeDeriv`, and ordered Fubini (`fcond_ordered_of_integrable`) give the
  slice, window and limit clauses with window limit `0`.
* **Addition.** The three ordered clauses are additive (good-time sets intersect, brackets add
  a.e. in time, windows add, limits add), so they hold for `A + H` with limit `0 + ∫ g φ`.
  No global absolute integrability of `H |D_t|^{1/2}φ` is used. The representative and its
  BMO bound are those of `H`.

The affine-part lemmas follow the half-time affine lemmas of the qualitative characterization
(graph source), restated here under the
prefix `d1eaffinv_` so that this file imports only Foundations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal SchwartzMap ContDiff

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

section AffineInvariance

variable {m : ℕ}

/-- The three ordered clauses of `RepresentsHomogeneousHalfTimeDerivative` for one Schwartz
test `ψ`, with limit `L`. -/
def d1eaffinv_Ordered (G : FourierSpace m → ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) (L : ℂ) : Prop :=
  (∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G ψ t)) ∧
    (∀ R : ℝ, IntegrableOn (halfTimeSpatialBracket G ψ) (Set.Icc (-R) R)) ∧
    Tendsto (halfTimeWindowPairing G ψ) atTop (𝓝 L)

/-- The ordered clauses are additive. -/
theorem d1eaffinv_ordered_add {G₁ G₂ : FourierSpace m → ℝ} {ψ : 𝓢(FourierSpace m, ℂ)}
    {L₁ L₂ : ℂ} (h₁ : d1eaffinv_Ordered G₁ ψ L₁) (h₂ : d1eaffinv_Ordered G₂ ψ L₂) :
    d1eaffinv_Ordered (fun x => G₁ x + G₂ x) ψ (L₁ + L₂) := by
  obtain ⟨a₁, i₁, t₁⟩ := h₁
  obtain ⟨a₂, i₂, t₂⟩ := h₂
  have hint : ∀ t u, halfTimeSpatialIntegrand (fun x => G₁ x + G₂ x) ψ t u =
      halfTimeSpatialIntegrand G₁ ψ t u + halfTimeSpatialIntegrand G₂ ψ t u := by
    intro t u
    simp only [halfTimeSpatialIntegrand]
    push_cast
    ring
  have hbr : ∀ᵐ t : ℝ, halfTimeSpatialBracket (fun x => G₁ x + G₂ x) ψ t =
      halfTimeSpatialBracket G₁ ψ t + halfTimeSpatialBracket G₂ ψ t := by
    filter_upwards [a₁, a₂] with t ht₁ ht₂
    simp only [halfTimeSpatialBracket, hint]
    exact integral_add ht₁ ht₂
  refine ⟨?_, fun R => ?_, ?_⟩
  · filter_upwards [a₁, a₂] with t ht₁ ht₂
    have hf : halfTimeSpatialIntegrand (fun x => G₁ x + G₂ x) ψ t =
        fun u => halfTimeSpatialIntegrand G₁ ψ t u + halfTimeSpatialIntegrand G₂ ψ t u :=
      funext (hint t)
    rw [hf]
    exact ht₁.add ht₂
  · exact (Integrable.add (i₁ R) (i₂ R)).congr
      (ae_restrict_of_ae (hbr.mono fun t ht => ht.symm))
  · have hw : ∀ R, halfTimeWindowPairing G₁ ψ R + halfTimeWindowPairing G₂ ψ R =
        halfTimeWindowPairing (fun x => G₁ x + G₂ x) ψ R := by
      intro R
      simp only [halfTimeWindowPairing]
      rw [← integral_add (i₁ R) (i₂ R)]
      exact integral_congr_ae (ae_restrict_of_ae (hbr.mono fun t ht => ht.symm))
    exact Tendsto.congr hw (t₁.add t₂)

/-- The time-independent spatial affine function `x = (u,t) ↦ c + ℓ(u)` in ordinary
coordinates. -/
def d1eaffinv_affineFn (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) (x : FourierSpace m) : ℝ :=
  c + ℓ (WithLp.ofLp x).1

theorem d1eaffinv_contDiff_affineFn (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (d1eaffinv_affineFn c ℓ) := by
  have h := (ℓ.comp (WithLp.fstL 2 ℝ (Spatial m) ℝ)).contDiff (n := ∞)
  exact contDiff_const.add h

/-- The affine function is invariant under time shifts. -/
theorem d1eaffinv_affineFn_sub_timeVector (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ)
    (x : FourierSpace m) (h : ℝ) :
    d1eaffinv_affineFn c ℓ (x - h • timeVector m) = d1eaffinv_affineFn c ℓ x := by
  simp only [d1eaffinv_affineFn, coordinates_sub_timeVector]

theorem d1eaffinv_contDiff_affine_mul (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ)
    {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun x => d1eaffinv_affineFn c ℓ x * φ x) :=
  (d1eaffinv_contDiff_affineFn c ℓ).mul hφ

theorem d1eaffinv_hasCompactSupport_affine_mul (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ)
    {φ : FourierSpace m → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => d1eaffinv_affineFn c ℓ x * φ x) :=
  hc.mul_left (f := d1eaffinv_affineFn c ℓ)

/-- `testKernel(Aφ) = A · testKernel(φ)`: the kernel shifts in time only. -/
theorem d1eaffinv_testKernel_affine_mul (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ)
    (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : FourierSpace m) :
    testKernel (realCompactTest (fun y => d1eaffinv_affineFn c ℓ y * φ y)
        (d1eaffinv_contDiff_affine_mul c ℓ hφ) (d1eaffinv_hasCompactSupport_affine_mul c ℓ hc)) x =
      (d1eaffinv_affineFn c ℓ x : ℂ) * testKernel (realCompactTest φ hφ hc) x := by
  have hint : ∀ h : ℝ,
      testKernelIntegrand (realCompactTest (fun y => d1eaffinv_affineFn c ℓ y * φ y)
          (d1eaffinv_contDiff_affine_mul c ℓ hφ)
          (d1eaffinv_hasCompactSupport_affine_mul c ℓ hc)) x h =
        (d1eaffinv_affineFn c ℓ x : ℂ) * testKernelIntegrand (realCompactTest φ hφ hc) x h := by
    intro h
    simp only [testKernelIntegrand, realCompactTest_apply, d1eaffinv_affineFn_sub_timeVector]
    push_cast
    ring
  simp only [testKernel, hint, integral_const_mul]
  ring

/-- **The affine part**: `A(u) = c + ℓ(u)` satisfies the three ordered clauses with window
limit `0`, for every real compact smooth test (no mean-zero condition used). -/
theorem d1eaffinv_affine_ordered (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    d1eaffinv_Ordered (d1eaffinv_affineFn c ℓ) (realCompactTest φ hφ hc) 0 := by
  have hcψA : HasCompactSupport (realCompactTest (fun y => d1eaffinv_affineFn c ℓ y * φ y)
      (d1eaffinv_contDiff_affine_mul c ℓ hφ) (d1eaffinv_hasCompactSupport_affine_mul c ℓ hc)) := by
    change IsCompact (tsupport _)
    rw [tsupport_realCompactTest]
    exact d1eaffinv_hasCompactSupport_affine_mul c ℓ hc
  have hae : testKernel (realCompactTest (fun y => d1eaffinv_affineFn c ℓ y * φ y)
        (d1eaffinv_contDiff_affine_mul c ℓ hφ)
        (d1eaffinv_hasCompactSupport_affine_mul c ℓ hc)) =ᵐ[volume]
      fun x => (d1eaffinv_affineFn c ℓ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x := by
    filter_upwards [testKernel_ae_halfTimeDeriv (realCompactTest φ hφ hc)] with x hx
    rw [d1eaffinv_testKernel_affine_mul c ℓ φ hφ hc x, hx]
  have hF : Integrable
      (fun x => (d1eaffinv_affineFn c ℓ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x)
      volume :=
    (integrable_testKernel_of_hasCompactSupport _ hcψA).congr hae
  have h0 : ∫ x, (d1eaffinv_affineFn c ℓ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x =
      0 := by
    rw [← integral_congr_ae hae]
    exact fcond_integral_testKernel_eq_zero _ hcψA
  obtain ⟨h1, h2, h3⟩ := fcond_ordered_of_integrable hF
  refine ⟨h1, fun R => h2.integrableOn, ?_⟩
  rw [← h0]
  exact h3

/-- The spatial affine function is Lipschitz on `Space m`. -/
theorem d1eaffinv_lipschitz_affine (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) :
    LipschitzWith ‖ℓ‖₊ (fun p : Space m => c + ℓ p.1) := by
  refine LipschitzWith.of_dist_le_mul fun p p' => ?_
  show dist (c + ℓ p.1) (c + ℓ p'.1) ≤ (‖ℓ‖₊ : ℝ) * dist p p'
  rw [coe_nnnorm, dist_eq_norm (c + ℓ p.1)]
  have h1 : ‖p.1 - p'.1‖ ≤ dist p p' := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  calc ‖c + ℓ p.1 - (c + ℓ p'.1)‖ = ‖ℓ (p.1 - p'.1)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ ‖ℓ‖ * ‖p.1 - p'.1‖ := ℓ.le_opNorm _
    _ ≤ ‖ℓ‖ * dist p p' := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

end AffineInvariance

/-- **Invariance under affine functions** (`d1e_AffineInvarianceStatement`): adding a
time-independent spatial affine function
`c + ℓ(u)` keeps the public half-time BMO bound `B`, with the same representative. -/
theorem d1e_affine_invariance_proof : d1e_AffineInvarianceStatement := by
  intro m H B c ℓ hH
  obtain ⟨⟨L, hL⟩, f, hf, hrep⟩ := hH
  refine ⟨⟨‖ℓ‖₊ + L, (d1eaffinv_lipschitz_affine c ℓ).add hL⟩, f, hf, ?_⟩
  have key : RepresentsHomogeneousHalfTimeDerivative
      (fun x => d1eaffinv_affineFn c ℓ x + H (fourierToParabolic m x))
      (fun x => f (fourierToParabolic m x)) := by
    refine ⟨hrep.1, fun φ hφ hc hmean => ?_⟩
    have h := d1eaffinv_ordered_add (d1eaffinv_affine_ordered c ℓ φ hφ hc)
      (hrep.2 φ hφ hc hmean)
    rw [zero_add] at h
    exact h
  exact key

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
