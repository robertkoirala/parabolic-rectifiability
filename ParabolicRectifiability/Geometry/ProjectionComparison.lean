import ParabolicRectifiability.Geometry.AffinePlane
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Projection algebra and affine anchors

All operator norms below are the `ContinuousLinearMap` operator norm on the
Euclidean space `Spatial n`. The Hilbert--Schmidt square is a finite sum
over its canonical orthonormal basis, and the trace is `LinearMap.trace`.
No matrix norm or positive-product inference is used.
-/

noncomputable section

namespace ParabolicRectifiability

open scoped RealInnerProductSpace
open ContinuousLinearMap

variable {n : ℕ}

/-- The canonical finite-dimensional trace of a spatial endomorphism. -/
def spatialTrace (A : Spatial n →L[ℝ] Spatial n) : ℝ :=
  LinearMap.trace ℝ (Spatial n) A.toLinearMap

@[simp] theorem spatialTrace_zero : spatialTrace (0 : Spatial n →L[ℝ] Spatial n) = 0 := by
  simp [spatialTrace]

@[simp] theorem spatialTrace_add (A B : Spatial n →L[ℝ] Spatial n) :
    spatialTrace (A + B) = spatialTrace A + spatialTrace B := by
  simp [spatialTrace]

@[simp] theorem spatialTrace_sub (A B : Spatial n →L[ℝ] Spatial n) :
    spatialTrace (A - B) = spatialTrace A - spatialTrace B := by
  simp [spatialTrace]

@[simp] theorem spatialTrace_smul (c : ℝ) (A : Spatial n →L[ℝ] Spatial n) :
    spatialTrace (c • A) = c * spatialTrace A := by
  simp [spatialTrace]

@[simp] theorem spatialTrace_one :
    spatialTrace (1 : Spatial n →L[ℝ] Spatial n) = n := by
  simp [spatialTrace, LinearMap.trace_one]

/-- Cyclic trace, with multiplication meaning composition in the displayed order. -/
theorem spatialTrace_mul_comm (A B : Spatial n →L[ℝ] Spatial n) :
    spatialTrace (A * B) = spatialTrace (B * A) :=
  LinearMap.trace_mul_comm ℝ A.toLinearMap B.toLinearMap

/-- The squared Hilbert--Schmidt norm, including the empty sum when `n = 0`. -/
def hilbertSchmidtSquared (A : Spatial n →L[ℝ] Spatial n) : ℝ :=
  ∑ i : Fin n, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2

theorem hilbertSchmidtSquared_nonneg (A : Spatial n →L[ℝ] Spatial n) :
    0 ≤ hilbertSchmidtSquared A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Identification with the canonical trace of `A* A`. -/
theorem hilbertSchmidtSquared_eq_trace_adjoint_mul (A : Spatial n →L[ℝ] Spatial n) :
    hilbertSchmidtSquared A = spatialTrace (A.adjoint * A) := by
  rw [spatialTrace, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [hilbertSchmidtSquared, ContinuousLinearMap.adjoint_inner_right]

theorem hilbertSchmidtSquared_eq_trace_sq (A : Spatial n →L[ℝ] Spatial n)
    (hA : IsSelfAdjoint A) : hilbertSchmidtSquared A = spatialTrace (A ^ 2) := by
  rw [hilbertSchmidtSquared_eq_trace_adjoint_mul, isSelfAdjoint_iff'.mp hA, pow_two]

/-- Cauchy--Schwarz on a basis expansion; no nonempty unit sphere is needed. -/
theorem operatorNorm_sq_le_hilbertSchmidtSquared (A : Spatial n →L[ℝ] Spatial n) :
    ‖A‖ ^ 2 ≤ hilbertSchmidtSquared A := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hnorm : ‖A‖ ≤ Real.sqrt (hilbertSchmidtSquared A) := by
    apply A.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    calc
      ‖A x‖ = ‖∑ i : Fin n, ⟪b i, x⟫ • A (b i)‖ := by
        conv_lhs => rw [← b.sum_repr' x]
        simp only [map_sum, map_smul]
      _ ≤ ∑ i : Fin n, ‖⟪b i, x⟫‖ * ‖A (b i)‖ := by
        simpa only [norm_smul] using
          (norm_sum_le Finset.univ (fun i : Fin n => ⟪b i, x⟫ • A (b i)))
      _ ≤ Real.sqrt (∑ i : Fin n, ‖⟪b i, x⟫‖ ^ 2) *
          Real.sqrt (∑ i : Fin n, ‖A (b i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt (hilbertSchmidtSquared A) * ‖x‖ := by
        rw [b.sum_sq_norm_inner_right, Real.sqrt_sq (norm_nonneg x)]
        exact mul_comm _ _
  have hs := Real.sq_sqrt (hilbertSchmidtSquared_nonneg A)
  nlinarith [norm_nonneg A, Real.sqrt_nonneg (hilbertSchmidtSquared A)]

/-- Idempotence alone gives trace equal to the dimension of the actual range. -/
theorem spatialTrace_eq_finrank_range (P : Spatial n →L[ℝ] Spatial n)
    (hP : IsIdempotentElem P) :
    spatialTrace P = (Module.finrank ℝ P.range : ℝ) :=
  (LinearMap.IsIdempotentElem.isProj_range P.toLinearMap hP.toLinearMap).trace

/-- The exact equal-rank trace identity for self-adjoint idempotents. -/
theorem hilbertSchmidtSquared_sub_projections
    (P P' : Spatial n →L[ℝ] Spatial n)
    (hP : IsStarProjection P) (hP' : IsStarProjection P')
    (hrank : Module.finrank ℝ P.range = Module.finrank ℝ P'.range) :
    hilbertSchmidtSquared (P - P') = 2 * spatialTrace ((1 - P) * P') := by
  have ht : spatialTrace P = spatialTrace P' := by
    rw [spatialTrace_eq_finrank_range P hP.isIdempotentElem,
      spatialTrace_eq_finrank_range P' hP'.isIdempotentElem, hrank]
  have hself : IsSelfAdjoint (P - P') := by
    apply isSelfAdjoint_iff'.mpr
    rw [map_sub, isSelfAdjoint_iff'.mp hP.isSelfAdjoint,
      isSelfAdjoint_iff'.mp hP'.isSelfAdjoint]
  rw [hilbertSchmidtSquared_eq_trace_sq _ hself]
  have hexpand : (P - P') ^ 2 = P + P' - P * P' - P' * P := by
    rw [pow_two, sub_mul, mul_sub, mul_sub,
      hP.isIdempotentElem.eq, hP'.isIdempotentElem.eq]
    abel
  rw [hexpand, sub_mul, one_mul]
  simp only [spatialTrace_add, spatialTrace_sub]
  rw [spatialTrace_mul_comm P' P, ht]
  ring

/-- Both parts of the projection comparison, retaining actual equal range rank. -/
theorem projection_comparison (P P' : Spatial n →L[ℝ] Spatial n)
    (hP : IsStarProjection P) (hP' : IsStarProjection P')
    (hrank : Module.finrank ℝ P.range = Module.finrank ℝ P'.range) :
    ‖P - P'‖ ^ 2 ≤ hilbertSchmidtSquared (P - P') ∧
      hilbertSchmidtSquared (P - P') = 2 * spatialTrace ((1 - P) * P') :=
  ⟨operatorNorm_sq_le_hilbertSchmidtSquared _,
    hilbertSchmidtSquared_sub_projections P P' hP hP' hrank⟩

/-- A positive compression has the same trace as the product with a projection.
The product itself is not claimed to be positive. -/
theorem spatialTrace_complement_mul_nonneg
    (P R : Spatial n →L[ℝ] Spatial n) (hP : IsStarProjection P)
    (hR : R.IsPositive) : 0 ≤ spatialTrace ((1 - P) * R) := by
  have hc : ((1 - P) * R * (1 - P)).IsPositive := by
    have h := hR.conj_adjoint (1 - P)
    rw [isSelfAdjoint_iff'.mp hP.one_sub.isSelfAdjoint] at h
    exact h
  have ht : spatialTrace ((1 - P) * R * (1 - P)) =
      spatialTrace ((1 - P) * R) := by
    rw [spatialTrace_mul_comm ((1 - P) * R) (1 - P), ← mul_assoc,
      hP.one_sub.isIdempotentElem.eq]
  rw [← ht]
  exact hc.toLinearMap.trace_nonneg

/-- Projection comparison under a positive-semidefinite lower bound, without
any commutation hypothesis on `Q`. -/
theorem projection_comparison_of_positive
    (P P' Q : Spatial n →L[ℝ] Spatial n)
    (hP : IsStarProjection P) (hP' : IsStarProjection P')
    (hrank : Module.finrank ℝ P.range = Module.finrank ℝ P'.range)
    (_hQ : IsSelfAdjoint Q) (lambda : ℝ) (hlambda : 0 < lambda)
    (hLower : (Q - lambda • P').IsPositive) :
    ‖P - P'‖ ^ 2 ≤ (2 / lambda) * spatialTrace ((1 - P) * Q) := by
  have htrace := spatialTrace_complement_mul_nonneg P (Q - lambda • P') hP hLower
  have hmul : (1 - P) * (lambda • P') = lambda • ((1 - P) * P') := by
    ext x
    simp
  rw [mul_sub, hmul, spatialTrace_sub, spatialTrace_smul] at htrace
  have hcomp := operatorNorm_sq_le_hilbertSchmidtSquared (P - P')
  rw [hilbertSchmidtSquared_sub_projections P P' hP hP' hrank] at hcomp
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlambda).mpr
  nlinarith

namespace AffineSpatialPlane

variable {m : ℕ}

theorem linearProjection_isStarProjection (L : AffineSpatialPlane n m) :
    IsStarProjection L.linearProjection :=
  isStarProjection_starProjection

theorem linearProjection_rank (L : AffineSpatialPlane n m) :
    Module.finrank ℝ L.linearProjection.range = m := by
  change Module.finrank ℝ L.direction.starProjection.range = m
  rw [Submodule.range_starProjection]
  exact L.rank_eq

theorem projection_comparison (L L' : AffineSpatialPlane n m) :
    ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤
        hilbertSchmidtSquared (L.linearProjection - L'.linearProjection) ∧
      hilbertSchmidtSquared (L.linearProjection - L'.linearProjection) =
        2 * spatialTrace ((1 - L.linearProjection) * L'.linearProjection) :=
  ParabolicRectifiability.projection_comparison _ _ L.linearProjection_isStarProjection
    L'.linearProjection_isStarProjection (L.linearProjection_rank.trans L'.linearProjection_rank.symm)

theorem projection_comparison_of_positive (L L' : AffineSpatialPlane n m)
    (Q : Spatial n →L[ℝ] Spatial n) (hQ : IsSelfAdjoint Q)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hLower : (Q - lambda • L'.linearProjection).IsPositive) :
    ‖L.linearProjection - L'.linearProjection‖ ^ 2 ≤
      (2 / lambda) * spatialTrace ((1 - L.linearProjection) * Q) :=
  ParabolicRectifiability.projection_comparison_of_positive _ _ _
    L.linearProjection_isStarProjection L'.linearProjection_isStarProjection
    (L.linearProjection_rank.trans L'.linearProjection_rank.symm) hQ lambda hlambda hLower

/-- Changing the test point changes the affine projection difference by its
linear part applied to the displacement. Canonical anchors are retained. -/
theorem projection_sub_projection_eq (L L' : AffineSpatialPlane n m) (x y : Spatial n) :
    L.projection y - L'.projection y = L.projection x - L'.projection x +
      (L.linearProjection - L'.linearProjection) (y - x) := by
  simp only [projection, sub_apply, map_sub]
  abel

theorem affine_anchor_inequality (L L' : AffineSpatialPlane n m) (x y : Spatial n) :
    ‖L.projection y - L'.projection y‖ ≤ ‖L.projection x - L'.projection x‖ +
      ‖L.linearProjection - L'.linearProjection‖ * ‖y - x‖ := by
  rw [L.projection_sub_projection_eq L' x y]
  exact (norm_add_le _ _).trans (add_le_add_right
    ((L.linearProjection - L'.linearProjection).le_opNorm (y - x)) _)

end AffineSpatialPlane
end ParabolicRectifiability
