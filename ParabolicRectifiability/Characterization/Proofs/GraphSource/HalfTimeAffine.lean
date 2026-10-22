import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterStatements
import ParabolicRectifiability.Foundations.Proofs.CompactBridge

/-! # Half-time derivative of an affine-plus-combination function

Proves `HalfTimeAffineCombinationStatement` (`b2_halfTime_affine_combination_proof`): if each
`Gᵢ` has homogeneous half-time derivative represented by `gᵢ`, then
`(u,t) ↦ c + ℓ(u) + Σᵢ Mᵢ Gᵢ(u,t)` has half-time derivative represented by `Σᵢ Mᵢ gᵢ`; the
time-independent affine part contributes zero.

Proof outline:

* **Affine part (`b2aff_affine_ordered`).** For `A(u) = c + ℓ(u)` and a real
  compact smooth test `φ`, the product `Aφ` is again a real compact smooth test. Since the
  shift in `testKernel` is in time only, `testKernel(Aφ) = A · testKernel(φ)` pointwise
  (`b2aff_testKernel_affine_mul`). Compact-test kernel integrability
  (`integrable_testKernel_of_hasCompactSupport`) and total cancellation
  (`fcond_integral_testKernel_eq_zero`) applied to `Aφ` give `A · testKernel(φ) ∈ L¹` with
  total integral `0`; neither uses `∫ φ = 0`. These transfer to `A · |D_t|^{1/2}φ` through
  `testKernel_ae_halfTimeDeriv`, and ordered Fubini (`fcond_ordered_of_integrable`) gives the
  three ordered clauses with limit `0`.
* **Finite combination.** The three ordered clauses are additive and homogeneous
  (`b2aff_ordered_add`, `b2aff_ordered_const_mul`, `b2aff_ordered_finsetSum`): the a.e.-time
  clause intersects finitely many good-time sets, brackets add a.e. in time, windows add,
  limits add. No absolute integrability on the product is assumed for the general `G_i`.
  The limit `∫ (Σ M_i g_i) φ` splits since each `g_i φ` is integrable (local integrability of
  `g_i`, compact support of `φ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal SchwartzMap ContDiff

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

variable {m : ℕ}

/-! ## The three ordered clauses for one test -/

/-- The three ordered clauses of `RepresentsHomogeneousHalfTimeDerivative` for one Schwartz
test `ψ`, with limit `L`: a.e.-time inner integrability, window integrability of the
bracket, and convergence of the window pairings to `L`. -/
def b2aff_Ordered (G : FourierSpace m → ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) (L : ℂ) : Prop :=
  (∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G ψ t)) ∧
    (∀ R : ℝ, IntegrableOn (halfTimeSpatialBracket G ψ) (Set.Icc (-R) R)) ∧
    Tendsto (halfTimeWindowPairing G ψ) atTop (𝓝 L)

/-- The ordered clauses are additive (the good-time sets are intersected). -/
theorem b2aff_ordered_add {G₁ G₂ : FourierSpace m → ℝ} {ψ : 𝓢(FourierSpace m, ℂ)}
    {L₁ L₂ : ℂ} (h₁ : b2aff_Ordered G₁ ψ L₁) (h₂ : b2aff_Ordered G₂ ψ L₂) :
    b2aff_Ordered (fun x => G₁ x + G₂ x) ψ (L₁ + L₂) := by
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

/-- The ordered clauses are homogeneous. -/
theorem b2aff_ordered_const_mul (M : ℝ) {G : FourierSpace m → ℝ} {ψ : 𝓢(FourierSpace m, ℂ)}
    {L : ℂ} (h : b2aff_Ordered G ψ L) :
    b2aff_Ordered (fun x => M * G x) ψ ((M : ℂ) * L) := by
  obtain ⟨a, i, t⟩ := h
  have hint : ∀ t u, halfTimeSpatialIntegrand (fun x => M * G x) ψ t u =
      (M : ℂ) * halfTimeSpatialIntegrand G ψ t u := by
    intro t u
    simp only [halfTimeSpatialIntegrand]
    push_cast
    ring
  have hbr : ∀ t, halfTimeSpatialBracket (fun x => M * G x) ψ t =
      (M : ℂ) * halfTimeSpatialBracket G ψ t := by
    intro t
    simp only [halfTimeSpatialBracket, hint]
    exact integral_const_mul _ _
  have hw : ∀ R, halfTimeWindowPairing (fun x => M * G x) ψ R =
      (M : ℂ) * halfTimeWindowPairing G ψ R := by
    intro R
    simp only [halfTimeWindowPairing, hbr]
    exact integral_const_mul _ _
  refine ⟨a.mono fun t ht => ?_, fun R => ?_, ?_⟩
  · rw [show halfTimeSpatialIntegrand (fun x => M * G x) ψ t =
        fun u => (M : ℂ) * halfTimeSpatialIntegrand G ψ t u from funext (hint t)]
    exact ht.const_mul _
  · rw [show halfTimeSpatialBracket (fun x => M * G x) ψ =
        fun t => (M : ℂ) * halfTimeSpatialBracket G ψ t from funext hbr]
    exact Integrable.const_mul (i R) _
  · rw [show halfTimeWindowPairing (fun x => M * G x) ψ =
        fun R => (M : ℂ) * halfTimeWindowPairing G ψ R from funext hw]
    exact t.const_mul _

/-- The zero function satisfies the ordered clauses with limit `0`. -/
theorem b2aff_ordered_zero (ψ : 𝓢(FourierSpace m, ℂ)) :
    b2aff_Ordered (fun _ => (0 : ℝ)) ψ 0 := by
  have hint : ∀ t, halfTimeSpatialIntegrand (fun _ => (0 : ℝ)) ψ t = fun _ => 0 := by
    intro t
    funext u
    simp [halfTimeSpatialIntegrand]
  have hbr : halfTimeSpatialBracket (fun _ => (0 : ℝ)) ψ = fun _ => 0 := by
    funext t
    simp only [halfTimeSpatialBracket, hint, integral_zero]
  have hw : halfTimeWindowPairing (fun _ => (0 : ℝ)) ψ = fun _ => 0 := by
    funext R
    simp only [halfTimeWindowPairing, hbr, integral_zero]
  refine ⟨Eventually.of_forall fun t => ?_, fun R => ?_, ?_⟩
  · rw [hint t]
    exact integrable_zero _ _ _
  · rw [hbr]
    exact integrableOn_zero
  · rw [hw]
    exact tendsto_const_nhds

/-- Finite sums of functions satisfying the ordered clauses satisfy them, with the sum of
the limits. -/
theorem b2aff_ordered_finsetSum {ι : Type*} (s : Finset ι) (G : ι → FourierSpace m → ℝ)
    (ψ : 𝓢(FourierSpace m, ℂ)) (L : ι → ℂ) (h : ∀ i ∈ s, b2aff_Ordered (G i) ψ (L i)) :
    b2aff_Ordered (fun x => ∑ i ∈ s, G i x) ψ (∑ i ∈ s, L i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    have hfun : (fun x => ∑ i ∈ (∅ : Finset ι), G i x) = fun _ => (0 : ℝ) :=
      funext fun x => Finset.sum_empty
    rw [hfun, Finset.sum_empty]
    exact b2aff_ordered_zero ψ
  · intro a s ha ih h
    have hfun : (fun x => ∑ i ∈ insert a s, G i x) = fun x => G a x + ∑ i ∈ s, G i x :=
      funext fun x => Finset.sum_insert ha
    rw [hfun, Finset.sum_insert ha]
    exact b2aff_ordered_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The affine part -/

/-- The time-independent affine function `x = (u,t) ↦ c + ℓ(u)`. -/
def b2aff_affineFn (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) (x : FourierSpace m) : ℝ :=
  c + ℓ (WithLp.ofLp x).1

theorem b2aff_contDiff_affineFn (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (b2aff_affineFn c ℓ) := by
  have h := (ℓ.comp (WithLp.fstL 2 ℝ (Spatial m) ℝ)).contDiff (n := ∞)
  exact contDiff_const.add h

/-- The affine function is invariant under time shifts. -/
theorem b2aff_affineFn_sub_timeVector (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) (x : FourierSpace m)
    (h : ℝ) : b2aff_affineFn c ℓ (x - h • timeVector m) = b2aff_affineFn c ℓ x := by
  simp only [b2aff_affineFn, coordinates_sub_timeVector]

/-- `Aφ` is again a smooth test. -/
theorem b2aff_contDiff_affine_mul (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ)
    {φ : FourierSpace m → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun x => b2aff_affineFn c ℓ x * φ x) :=
  (b2aff_contDiff_affineFn c ℓ).mul hφ

/-- `Aφ` is again compactly supported. -/
theorem b2aff_hasCompactSupport_affine_mul (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ)
    {φ : FourierSpace m → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => b2aff_affineFn c ℓ x * φ x) :=
  hc.mul_left (f := b2aff_affineFn c ℓ)

/-- Pointwise kernel identity `testKernel(Aφ) = A · testKernel(φ)`: the shift in the kernel
is in time only and `A` does not depend on time. -/
theorem b2aff_testKernel_affine_mul (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ)
    (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x : FourierSpace m) :
    testKernel (realCompactTest (fun y => b2aff_affineFn c ℓ y * φ y)
        (b2aff_contDiff_affine_mul c ℓ hφ) (b2aff_hasCompactSupport_affine_mul c ℓ hc)) x =
      (b2aff_affineFn c ℓ x : ℂ) * testKernel (realCompactTest φ hφ hc) x := by
  have hint : ∀ h : ℝ,
      testKernelIntegrand (realCompactTest (fun y => b2aff_affineFn c ℓ y * φ y)
          (b2aff_contDiff_affine_mul c ℓ hφ) (b2aff_hasCompactSupport_affine_mul c ℓ hc)) x h =
        (b2aff_affineFn c ℓ x : ℂ) * testKernelIntegrand (realCompactTest φ hφ hc) x h := by
    intro h
    simp only [testKernelIntegrand, realCompactTest_apply, b2aff_affineFn_sub_timeVector]
    push_cast
    ring
  simp only [testKernel, hint, integral_const_mul]
  ring

/-- **The affine part.** For every real compact smooth test `φ` (no mean-zero
condition), `A(u) = c + ℓ(u)` satisfies the three ordered clauses with limit `0`. -/
theorem b2aff_affine_ordered (c : ℝ) (ℓ : Spatial m →L[ℝ] ℝ) (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    b2aff_Ordered (b2aff_affineFn c ℓ) (realCompactTest φ hφ hc) 0 := by
  have hcψA : HasCompactSupport (realCompactTest (fun y => b2aff_affineFn c ℓ y * φ y)
      (b2aff_contDiff_affine_mul c ℓ hφ) (b2aff_hasCompactSupport_affine_mul c ℓ hc)) := by
    change IsCompact (tsupport _)
    rw [tsupport_realCompactTest]
    exact b2aff_hasCompactSupport_affine_mul c ℓ hc
  have hae : testKernel (realCompactTest (fun y => b2aff_affineFn c ℓ y * φ y)
        (b2aff_contDiff_affine_mul c ℓ hφ) (b2aff_hasCompactSupport_affine_mul c ℓ hc)) =ᵐ[volume]
      fun x => (b2aff_affineFn c ℓ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x := by
    filter_upwards [testKernel_ae_halfTimeDeriv (realCompactTest φ hφ hc)] with x hx
    rw [b2aff_testKernel_affine_mul c ℓ φ hφ hc x, hx]
  have hF : Integrable
      (fun x => (b2aff_affineFn c ℓ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x)
      volume :=
    (integrable_testKernel_of_hasCompactSupport _ hcψA).congr hae
  have h0 : ∫ x, (b2aff_affineFn c ℓ x : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x =
      0 := by
    rw [← integral_congr_ae hae]
    exact fcond_integral_testKernel_eq_zero _ hcψA
  obtain ⟨h1, h2, h3⟩ := fcond_ordered_of_integrable hF
  refine ⟨h1, fun R => h2.integrableOn, ?_⟩
  rw [← h0]
  exact h3

/-! ## Assembly -/

/-- **Half-time derivative of affine-plus-combination functions**
(`HalfTimeAffineCombinationStatement`). -/
theorem b2_halfTime_affine_combination_proof : HalfTimeAffineCombinationStatement := by
  intro m d G g hG c ℓ M
  refine ⟨locallyIntegrable_finsetSum _ fun i _ => (hG i).1.smul (M i), ?_⟩
  intro φ hφ hc hmean
  have hint : ∀ i, Integrable (fun x => (g i x : ℂ) * (φ x : ℂ)) volume := fun i =>
    integrable_local_mul_test (locallyIntegrableOn_univ.mpr (hG i).1)
      (Complex.continuous_ofReal.comp hφ.continuous)
      (hc.comp_left Complex.ofReal_zero) (subset_univ _)
  have hcomb : b2aff_Ordered (fun x => ∑ i, M i * G i x) (realCompactTest φ hφ hc)
      (∑ i, (M i : ℂ) * ∫ x, (g i x : ℂ) * (φ x : ℂ)) :=
    b2aff_ordered_finsetSum Finset.univ (fun i x => M i * G i x) (realCompactTest φ hφ hc)
      (fun i => (M i : ℂ) * ∫ x, (g i x : ℂ) * (φ x : ℂ))
      fun i _ => b2aff_ordered_const_mul (M i) ((hG i).2 φ hφ hc hmean)
  have htot := b2aff_ordered_add (b2aff_affine_ordered c ℓ φ hφ hc) hcomb
  have hval : (0 : ℂ) + ∑ i, (M i : ℂ) * ∫ x, (g i x : ℂ) * (φ x : ℂ) =
      ∫ x, ((∑ i, M i * g i x : ℝ) : ℂ) * (φ x : ℂ) := by
    rw [zero_add]
    have hpt : ∀ x, ((∑ i, M i * g i x : ℝ) : ℂ) * (φ x : ℂ) =
        ∑ i, (M i : ℂ) * ((g i x : ℂ) * (φ x : ℂ)) := by
      intro x
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  rw [hval] at htot
  exact htot

end ParabolicRectifiability.Characterization
