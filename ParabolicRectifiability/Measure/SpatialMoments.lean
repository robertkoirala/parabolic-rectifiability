import ParabolicRectifiability.Metric.ProperSpace
import ParabolicRectifiability.Geometry.ModelDistance
import ParabolicRectifiability.Geometry.ProjectionComparison
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Finite spatial moments of a bounded parabolic source

The source record contains only a finite measure and its supporting ball.
Covariance is unnormalized: it is the Bochner integral of rank-one operators.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped RealInnerProductSpace

/-- A finite Borel source carried by one positive-radius closed parabolic ball. -/
structure SpatialSource (n : ℕ) where
  measure : Measure (Space n)
  finite : IsFiniteMeasure measure
  center : Space n
  radius : ℝ
  radius_pos : 0 < radius
  carried : ∀ᵐ z ∂measure, z ∈ Metric.closedBall center radius

attribute [instance] SpatialSource.finite

namespace SpatialSource

variable {n : ℕ}

/-- Restrict a source finite on compact sets; no global finiteness is needed. -/
def restrictClosedBall (mu : Measure (Space n)) [IsFiniteMeasureOnCompacts mu]
    (z : Space n) (r : ℝ) (hr : 0 < r) : SpatialSource n where
  measure := mu.restrict (Metric.closedBall z r)
  finite := isFiniteMeasure_restrict.mpr (isCompact_closedBall z r).measure_ne_top
  center := z
  radius := r
  radius_pos := hr
  carried := ae_restrict_mem measurableSet_closedBall

theorem carried_iff_compl_null (nu : Measure (Space n)) (z : Space n) (r : ℝ) :
    (∀ᵐ w ∂nu, w ∈ Metric.closedBall z r) ↔ nu (Metric.closedBall z r)ᶜ = 0 :=
  mem_ae_iff

/-- The real total mass, with finiteness supplied by the source. -/
def mass (S : SpatialSource n) : ℝ := S.measure.real univ

theorem mass_nonneg (S : SpatialSource n) : 0 ≤ S.mass := ENNReal.toReal_nonneg

theorem mass_eq_zero_iff (S : SpatialSource n) : S.mass = 0 ↔ S.measure = 0 := by
  rw [mass, measureReal_eq_zero_iff, Measure.measure_univ_eq_zero]

/-- Every continuous finite-dimensional integrand is integrable on the source. -/
theorem integrable (S : SpatialSource n) {E : Type*} [NormedAddCommGroup E]
    {f : Space n → E} (hf : Continuous f) : Integrable f S.measure := by
  have h := hf.continuousOn.integrableOn_compact (μ := S.measure)
    (isCompact_closedBall S.center S.radius)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem S.carried] at h

/-- The actual barycenter. The inverse-zero convention gives zero at zero mass;
`mass_eq_zero_iff` first identifies that case with the zero measure. -/
def barycenter (S : SpatialSource n) : Spatial n :=
  S.mass⁻¹ • ∫ z, z.1 ∂S.measure

theorem barycenter_eq_zero_of_mass_eq_zero (S : SpatialSource n) (h : S.mass = 0) :
    S.barycenter = 0 := by
  have hz := S.mass_eq_zero_iff.mp h
  simp [barycenter, hz]

def centered (S : SpatialSource n) (z : Space n) : Spatial n := z.1 - S.barycenter

@[fun_prop] theorem continuous_centered (S : SpatialSource n) : Continuous S.centered := by
  exact continuous_fst.sub continuous_const

theorem integrable_spatial (S : SpatialSource n) : Integrable (fun z => z.1) S.measure :=
  S.integrable continuous_fst

theorem integrable_centered (S : SpatialSource n) : Integrable S.centered S.measure :=
  S.integrable S.continuous_centered

theorem mass_smul_barycenter (S : SpatialSource n) :
    S.mass • S.barycenter = ∫ z, z.1 ∂S.measure := by
  by_cases h : S.mass = 0
  · have hz := S.mass_eq_zero_iff.mp h
    simp [hz, mass]
  · simp [barycenter, smul_smul, h]

theorem integral_centered (S : SpatialSource n) : ∫ z, S.centered z ∂S.measure = 0 := by
  unfold centered
  rw [integral_sub S.integrable_spatial (integrable_const _), integral_const]
  exact sub_eq_zero.mpr S.mass_smul_barycenter.symm

theorem spatial_bound (S : SpatialSource n) :
    ∀ᵐ z ∂S.measure, ‖z.1 - S.center.1‖ ≤ S.radius := by
  filter_upwards [S.carried] with z hz
  exact (show ‖z.1 - S.center.1‖ ≤ dist z S.center from by
    change dist z.1 S.center.1 ≤ max (dist z.1 S.center.1) (dist z.2 S.center.2)
    exact le_max_left _ _).trans (Metric.mem_closedBall.mp hz)

theorem barycenter_mem_ball (S : SpatialSource n) (hM : 0 < S.mass) :
    ‖S.barycenter - S.center.1‖ ≤ S.radius := by
  have heq : S.mass • (S.barycenter - S.center.1) =
      ∫ z, z.1 - S.center.1 ∂S.measure := by
    rw [smul_sub, S.mass_smul_barycenter, integral_sub S.integrable_spatial
      (integrable_const _), integral_const]
    rfl
  have hb := norm_integral_le_of_norm_le_const S.spatial_bound
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos hM] at hb
  exact (mul_le_mul_iff_right₀ hM).mp (by simpa only [mul_comm, mass] using hb)

/-- The unnormalized, centered covariance as a genuine operator-valued integral. -/
def covariance (S : SpatialSource n) : Spatial n →L[ℝ] Spatial n :=
  ∫ z, InnerProductSpace.rankOne ℝ (S.centered z) (S.centered z) ∂S.measure

theorem continuous_covariance_integrand (S : SpatialSource n) :
    Continuous (fun z => InnerProductSpace.rankOne ℝ (S.centered z) (S.centered z)) := by
  exact ((InnerProductSpace.rankOne ℝ).continuous.comp S.continuous_centered).clm_apply
    S.continuous_centered

theorem integrable_covariance (S : SpatialSource n) :
    Integrable (fun z => InnerProductSpace.rankOne ℝ (S.centered z) (S.centered z))
      S.measure := S.integrable S.continuous_covariance_integrand

theorem covariance_eq_zero_of_mass_eq_zero (S : SpatialSource n) (h : S.mass = 0) :
    S.covariance = 0 := by
  simp [covariance, S.mass_eq_zero_iff.mp h]

theorem covariance_apply (S : SpatialSource n) (w : Spatial n) :
    S.covariance w = ∫ z, ⟪S.centered z, w⟫ • S.centered z ∂S.measure := by
  rw [covariance, ContinuousLinearMap.integral_apply S.integrable_covariance]
  rfl

theorem inner_covariance (S : SpatialSource n) (v w : Spatial n) :
    ⟪v, S.covariance w⟫ = ∫ z, ⟪S.centered z, v⟫ * ⟪S.centered z, w⟫ ∂S.measure := by
  rw [S.covariance_apply, ← integral_inner (S.integrable (by fun_prop))]
  simp only [inner_smul_right, real_inner_comm v, mul_comm]

theorem covariance_isSymmetric (S : SpatialSource n) : S.covariance.IsSymmetric := by
  intro v w
  change ⟪S.covariance v, w⟫ = ⟪v, S.covariance w⟫
  rw [show ⟪S.covariance v, w⟫ = ⟪w, S.covariance v⟫ from real_inner_comm _ _,
    S.inner_covariance, S.inner_covariance]
  simp only [mul_comm]

theorem covariance_isPositive (S : SpatialSource n) : S.covariance.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff _).mpr ⟨S.covariance_isSymmetric, fun v => ?_⟩
  rw [real_inner_comm, S.inner_covariance]
  exact integral_nonneg fun z => mul_self_nonneg _

theorem covariance_isSelfAdjoint (S : SpatialSource n) : IsSelfAdjoint S.covariance :=
  S.covariance_isPositive.isSelfAdjoint

/-- Evaluation of a linear functional on covariance, including its trace. -/
theorem trace_mul_covariance (S : SpatialSource n) (A : Spatial n →L[ℝ] Spatial n) :
    spatialTrace (A * S.covariance) = ∫ z, ⟪S.centered z, A (S.centered z)⟫ ∂S.measure := by
  let T : (Spatial n →L[ℝ] Spatial n) →ₗ[ℝ] ℝ :=
    { toFun := fun B => spatialTrace (A * B)
      map_add' := fun B C => by simp [mul_add]
      map_smul' := fun c B => by
        have h : A * (c • B) = c • (A * B) := by ext x; simp
        simp [h] }
  have ht := T.toContinuousLinearMap.integral_comp_comm S.integrable_covariance
  change (∫ z, spatialTrace (A * InnerProductSpace.rankOne ℝ (S.centered z)
    (S.centered z)) ∂S.measure) = spatialTrace (A * S.covariance) at ht
  rw [← ht]
  congr 1
  funext z
  change LinearMap.trace ℝ (Spatial n)
    (A * InnerProductSpace.rankOne ℝ (S.centered z) (S.centered z)).toLinearMap = _
  rw [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
    InnerProductSpace.trace_rankOne]

theorem trace_covariance (S : SpatialSource n) :
    spatialTrace S.covariance = ∫ z, ‖S.centered z‖ ^ 2 ∂S.measure := by
  simpa using S.trace_mul_covariance 1

theorem integral_centered_affine_sq (S : SpatialSource n)
    (A : Spatial n →L[ℝ] Spatial n) (b : Spatial n) :
    (∫ z, ‖A (S.centered z) + b‖ ^ 2 ∂S.measure) =
      (∫ z, ‖A (S.centered z)‖ ^ 2 ∂S.measure) + S.mass * ‖b‖ ^ 2 := by
  have hc : (∫ z, ⟪A (S.centered z), b⟫ ∂S.measure) = 0 := by
    have hfun : (fun z => ⟪A (S.centered z), b⟫) =
        (fun z => ⟪b, A (S.centered z)⟫) := funext fun z => real_inner_comm _ _
    rw [hfun, integral_inner (𝕜 := ℝ) (S.integrable (by fun_prop : Continuous (fun z => A (S.centered z)))),
      A.integral_comp_comm S.integrable_centered, S.integral_centered, map_zero, inner_zero_right]
  simp_rw [norm_add_sq_real]
  rw [integral_add (S.integrable (by fun_prop)) (integrable_const _),
    integral_add (S.integrable (by fun_prop)) (S.integrable (by fun_prop)),
    integral_const_mul, hc, integral_const]
  simp [mass]

/-- Centered spatial variance about any prescribed point. -/
theorem variance_about (S : SpatialSource n) (a : Spatial n) :
    (∫ z, ‖z.1 - a‖ ^ 2 ∂S.measure) =
      spatialTrace S.covariance + S.mass * ‖S.barycenter - a‖ ^ 2 := by
  rw [S.trace_covariance]
  have h := S.integral_centered_affine_sq 1 (S.barycenter - a)
  simpa [centered, sub_add_sub_cancel] using h

theorem trace_covariance_eq_variance (S : SpatialSource n) :
    spatialTrace S.covariance = (∫ z, ‖z.1 - S.center.1‖ ^ 2 ∂S.measure) -
      S.mass * ‖S.barycenter - S.center.1‖ ^ 2 := by
  linarith [S.variance_about S.center.1]

theorem trace_covariance_le (S : SpatialSource n) :
    spatialTrace S.covariance ≤ S.mass * S.radius ^ 2 := by
  have hi : (∫ z, ‖z.1 - S.center.1‖ ^ 2 ∂S.measure) ≤ S.mass * S.radius ^ 2 := by
    calc
      _ ≤ ∫ _ : Space n, S.radius ^ 2 ∂S.measure := by
        apply integral_mono_ae (S.integrable (by fun_prop)) (integrable_const _)
        filter_upwards [S.spatial_bound] with z hz
        exact pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = _ := by simp [mass]
  rw [S.trace_covariance_eq_variance]
  exact (sub_le_self _ (mul_nonneg S.mass_nonneg (sq_nonneg _))).trans hi

end SpatialSource
end ParabolicRectifiability
