import ParabolicRectifiability.Examples.Proofs.Reductions.ReductionStatements
import ParabolicRectifiability.Foundations.Proofs.CompactBridge

/-! # Time-independent functions have zero half-time derivative

Proof of `E2TimeIndependentHalfTimeStatement` (`e2_timeIndependent_halfTime_proof`).

Route:

* **Weighted cancellation** (`e2_geb_weighted`). For a continuous `a : ℝ^m → ℝ` and a
  compactly supported Schwartz test `ψ`, `a(u) K_ψ(u,t) ∈ L¹` with integral `0`, where
  `K_ψ = testKernel ψ`. The kernel and the difference integrand vanish off `K × ℝ`, with
  `K = spatialTestSupport ψ` compact, so `a` may be replaced by the cutoff `1_K a`. The cutoff is
  bounded, measurable and invariant under time translation. Integrability is
  `integrable_bounded_mul_testKernel`. For cancellation, the cutoff times the integrable
  difference integrand (`fcond_integrable_testKernelIntegrand_prod`) is integrable on the
  product; Fubini and translation invariance of `x ↦ 1_K a(x) ψ(x)` give zero on every shift
  fibre. Total mean zero of `K_ψ` alone is not used.
* **Transfer and ordered Fubini** (`e2_geb_ordered`). `testKernel_ae_halfTimeDeriv` moves both
  facts to `a · |D_t|^{1/2}φ`, and `fcond_ordered_of_integrable` gives the three ordered clauses
  with limit `0`. This follows the model argument `b2aff_affine_ordered`.
* **Assembly.** Each normal component of `(u,t) ↦ h(u)` is `x ↦ a_i((x).1)` with `a_i` continuous
  (Lipschitz `h`); each normal component of `0` is `0`, and `∫ 0 · φ = 0`. The zero function has
  parabolic BMO bound `0`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology SchwartzMap ContDiff NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations ParabolicRectifiability.HalfTimeDerivative

section WeightedCancellation

variable {m : ℕ}

/-- The spatial cutoff `x ↦ 1_K(u) a(u)`, `x = (u,t)`, `K = spatialTestSupport ψ`. -/
private def e2_geb_cut (ψ : 𝓢(FourierSpace m, ℂ)) (a : Spatial m → ℝ) (x : FourierSpace m) :
    ℂ :=
  (spatialTestSupport ψ).indicator (fun u => (a u : ℂ)) (WithLp.ofLp x).1

private theorem e2_geb_fst_sub_timeVector (x : FourierSpace m) (h : ℝ) :
    (WithLp.ofLp (x - h • timeVector m)).1 = (WithLp.ofLp x).1 := by
  rw [coordinates_sub_timeVector]

/-- The cutoff does not depend on time. -/
private theorem e2_geb_cut_sub_timeVector (ψ : 𝓢(FourierSpace m, ℂ)) (a : Spatial m → ℝ)
    (x : FourierSpace m) (h : ℝ) :
    e2_geb_cut ψ a (x - h • timeVector m) = e2_geb_cut ψ a x := by
  simp only [e2_geb_cut, e2_geb_fst_sub_timeVector]

private theorem e2_geb_measurable_cut (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    {a : Spatial m → ℝ} (ha : Continuous a) : Measurable (e2_geb_cut ψ a) :=
  ((Complex.continuous_ofReal.comp ha).measurable.indicator
      (isCompact_spatialTestSupport ψ hc).measurableSet).comp
    (fourierCoordinatesMeasurableEquiv m).measurable.fst

/-- The cutoff is bounded. -/
private theorem e2_geb_cut_bound (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    {a : Spatial m → ℝ} (ha : Continuous a) : ∃ C : ℝ, ∀ x, ‖e2_geb_cut ψ a x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_spatialTestSupport ψ hc).exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp ha).continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : (WithLp.ofLp x).1 ∈ spatialTestSupport ψ
  · rw [e2_geb_cut, indicator_of_mem hx]
    exact (hC _ hx).trans (le_max_left _ _)
  · rw [e2_geb_cut, indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

/-- Off `K × ℝ` the kernel vanishes, so the weight `a` may be replaced by the cutoff. -/
private theorem e2_geb_weight_mul_testKernel (ψ : 𝓢(FourierSpace m, ℂ)) (a : Spatial m → ℝ)
    (x : FourierSpace m) :
    (a (WithLp.ofLp x).1 : ℂ) * testKernel ψ x = e2_geb_cut ψ a x * testKernel ψ x := by
  by_cases hx : (WithLp.ofLp x).1 ∈ spatialTestSupport ψ
  · rw [e2_geb_cut, indicator_of_mem hx]
  · have h0 : testKernel ψ x = 0 := by
      have := testKernel_eq_zero_of_notMem_spatialTestSupport ψ hx (WithLp.ofLp x).2
      rwa [Prod.mk.eta, WithLp.toLp_ofLp] at this
    rw [h0, mul_zero, mul_zero]

/-- On every shift fibre, the cutoff times the difference integrand has integral `0`. -/
private theorem e2_geb_fiber_integral (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    {a : Spatial m → ℝ} (ha : Continuous a) (h : ℝ) :
    ∫ x, e2_geb_cut ψ a x * testKernelIntegrand ψ x h = 0 := by
  obtain ⟨C, hC⟩ := e2_geb_cut_bound ψ hc ha
  have hF : Integrable (fun x => e2_geb_cut ψ a x * ψ x) volume :=
    ψ.integrable.bdd_mul (e2_geb_measurable_cut ψ hc ha).aestronglyMeasurable
      (Eventually.of_forall hC)
  have hpt : ∀ x, e2_geb_cut ψ a x * testKernelIntegrand ψ x h =
      ((|h| ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * (e2_geb_cut ψ a x * ψ x -
        e2_geb_cut ψ a (x - h • timeVector m) * ψ (x - h • timeVector m)) := by
    intro x
    rw [e2_geb_cut_sub_timeVector, testKernelIntegrand]
    ring
  have htr : ∫ x, e2_geb_cut ψ a (x - h • timeVector m) * ψ (x - h • timeVector m) =
      ∫ x, e2_geb_cut ψ a x * ψ x :=
    integral_sub_right_eq_self (fun x => e2_geb_cut ψ a x * ψ x) (h • timeVector m)
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub hF (hF.comp_sub_right (h • timeVector m)), htr, sub_self,
    mul_zero]

/-- **Weighted cancellation**: for continuous `a` and a compact Schwartz test,
`a(u) K_ψ(u,t)` is integrable with integral `0`. -/
private theorem e2_geb_weighted (ψ : 𝓢(FourierSpace m, ℂ)) (hc : HasCompactSupport ψ)
    {a : Spatial m → ℝ} (ha : Continuous a) :
    Integrable (fun x => (a (WithLp.ofLp x).1 : ℂ) * testKernel ψ x) volume ∧
      ∫ x, (a (WithLp.ofLp x).1 : ℂ) * testKernel ψ x = 0 := by
  obtain ⟨C, hC⟩ := e2_geb_cut_bound ψ hc ha
  have hm := e2_geb_measurable_cut ψ hc ha
  simp_rw [e2_geb_weight_mul_testKernel ψ a]
  refine ⟨integrable_bounded_mul_testKernel ψ hc hm.aestronglyMeasurable
    (Eventually.of_forall hC), ?_⟩
  have hprod : Integrable
      (Function.uncurry fun x h => e2_geb_cut ψ a x * testKernelIntegrand ψ x h)
      ((volume : Measure (FourierSpace m)).prod (volume : Measure ℝ)) :=
    (fcond_integrable_testKernelIntegrand_prod ψ hc).bdd_mul
      (f := fun p : FourierSpace m × ℝ => e2_geb_cut ψ a p.1)
      (hm.comp measurable_fst).aestronglyMeasurable (Eventually.of_forall fun p => hC p.1)
  have hk : ∀ x, e2_geb_cut ψ a x * testKernel ψ x =
      (ParabolicRectifiability.FractionalKernel.kappa : ℂ) *
        ∫ h, e2_geb_cut ψ a x * testKernelIntegrand ψ x h := by
    intro x
    rw [testKernel, integral_const_mul]
    ring
  simp_rw [hk]
  rw [integral_const_mul, integral_integral_swap hprod]
  simp only [e2_geb_fiber_integral ψ hc ha, integral_zero, mul_zero]

/-- **Transfer and ordered Fubini.** A time-independent continuous weight satisfies the three
ordered clauses for every real compact smooth test, with limit `0` (no mean-zero condition on
the test is used). -/
private theorem e2_geb_ordered {a : Spatial m → ℝ} (ha : Continuous a)
    (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand (fun x => a (WithLp.ofLp x).1)
      (realCompactTest φ hφ hc) t)) ∧
    (∀ R : ℝ, IntegrableOn (halfTimeSpatialBracket (fun x => a (WithLp.ofLp x).1)
      (realCompactTest φ hφ hc)) (Icc (-R) R)) ∧
    Tendsto (halfTimeWindowPairing (fun x => a (WithLp.ofLp x).1) (realCompactTest φ hφ hc))
      atTop (𝓝 0) := by
  have hcψ : HasCompactSupport (realCompactTest φ hφ hc) := by
    change IsCompact (tsupport (realCompactTest φ hφ hc))
    rw [tsupport_realCompactTest]
    exact hc
  obtain ⟨hI, h0⟩ := e2_geb_weighted (realCompactTest φ hφ hc) hcψ ha
  have hae : (fun x => (a (WithLp.ofLp x).1 : ℂ) * testKernel (realCompactTest φ hφ hc) x)
      =ᵐ[volume] fun x => (a (WithLp.ofLp x).1 : ℂ) *
        halfTimeDeriv m (realCompactTest φ hφ hc) x := by
    filter_upwards [testKernel_ae_halfTimeDeriv (realCompactTest φ hφ hc)] with x hx
    rw [hx]
  have hF : Integrable (fun x => (a (WithLp.ofLp x).1 : ℂ) *
      halfTimeDeriv m (realCompactTest φ hφ hc) x) volume := hI.congr hae
  have h0' : ∫ x, (a (WithLp.ofLp x).1 : ℂ) * halfTimeDeriv m (realCompactTest φ hφ hc) x =
      0 := by
    rw [← integral_congr_ae hae]
    exact h0
  obtain ⟨h1, h2, h3⟩ := fcond_ordered_of_integrable hF
  refine ⟨h1, fun R => h2.integrableOn, ?_⟩
  rw [← h0']
  exact h3

end WeightedCancellation

/-- Time-independent functions have zero half-time derivative
(`E2TimeIndependentHalfTimeStatement`). -/
theorem e2_timeIndependent_halfTime_proof : E2TimeIndependentHalfTimeStatement := by
  intro n W h K hK
  refine ⟨?_, ?_⟩
  · intro i
    have ha : Continuous fun u : Spatial (Module.finrank ℝ W) =>
        normalCoordinates W (h ((subspaceCoordinates W).symm u)) i :=
      (EuclideanSpace.proj i).continuous.comp
        ((normalCoordinates W).continuous.comp
          (hK.continuous.comp (subspaceCoordinates W).symm.continuous))
    have hG : normalFourierComponent W (fun q : SubspaceSpace W => h q.1) i =
        fun x => normalCoordinates W (h ((subspaceCoordinates W).symm (WithLp.ofLp x).1)) i :=
      rfl
    have h0 : normalFourierComponent W (fun _ : SubspaceSpace W => (0 : W.orthogonal)) i =
        fun _ => 0 := by
      funext x
      simp [normalFourierComponent]
    rw [hG, h0]
    refine ⟨locallyIntegrable_zero, ?_⟩
    intro φ hφ hc _
    obtain ⟨h1, h2, h3⟩ := e2_geb_ordered ha φ hφ hc
    refine ⟨h1, h2, ?_⟩
    simpa using h3
  · refine ⟨le_rfl, locallyIntegrable_zero, fun p r _ => ?_⟩
    simp [parabolicBallAverage]

end ParabolicRectifiability.Examples
