import ParabolicRectifiability.Geometry.AffinePlane

/-!
# Finite weighted affine projections

The time argument is an ordinary real parameter. The weights are genuine
functions; their derivatives below are the ordinary Fréchet derivative and
real derivative. Smooth partitions with these bounds are constructed separately.
The full activity predicate includes the value, both spatial derivatives,
and the time derivative. The main result is `one_step`: displacement,
derivative and quadratic-distortion bounds for the weighted projection `sigma`.
-/

noncomputable section

namespace ParabolicRectifiability.CoherentProjection

open scoped RealInnerProductSpace
open Finset ContinuousLinearMap

variable {ι : Type*} {n m : ℕ}

def sigma (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ) : Spatial n :=
  x + ∑ a ∈ s, θ a x t • ((L a).projection x - x)

def dx (θ : ι → Spatial n → ℝ → ℝ) (a : ι) (x : Spatial n) (t : ℝ) :
    Spatial n →L[ℝ] ℝ := fderiv ℝ (fun y => θ a y t) x

def dt (θ : ι → Spatial n → ℝ → ℝ) (a : ι) (x : Spatial n) (t : ℝ) : ℝ :=
  deriv (θ a x) t

/-- Nonzero as a map for both spatial derivative orders. -/
def Active (θ : ι → Spatial n → ℝ → ℝ) (a : ι) (x : Spatial n) (t : ℝ) : Prop :=
  θ a x t ≠ 0 ∨ dx θ a x t ≠ 0 ∨
    fderiv ℝ (fun y => dx θ a y t) x ≠ 0 ∨ dt θ a x t ≠ 0

def spatialDerivative (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ) :
    Spatial n →L[ℝ] Spatial n :=
  ContinuousLinearMap.id ℝ (Spatial n) + ∑ a ∈ s,
    (θ a x t • ((L a).linearProjection - ContinuousLinearMap.id ℝ (Spatial n)) +
      (dx θ a x t).smulRight ((L a).projection x - x))

def timeDerivative (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ) : Spatial n :=
  ∑ a ∈ s, dt θ a x t • ((L a).projection x - x)

theorem hasFDerivAt_sigma (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x) :
    HasFDerivAt (fun y => sigma s L θ y t) (spatialDerivative s L θ x t) x := by
  apply (hasFDerivAt_id x).add
  apply HasFDerivAt.fun_sum
  intro a ha
  exact (hθ a ha).hasFDerivAt.smul
    (((L a).linearProjection.hasFDerivAt.const_add (L a).anchor).sub (hasFDerivAt_id x))

theorem hasDerivAt_sigma (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (θ a x) t) :
    HasDerivAt (sigma s L θ x) (timeDerivative s L θ x t) t := by
  unfold sigma timeDerivative dt
  exact (HasDerivAt.fun_sum fun a ha => (hθ a ha).hasDerivAt.smul_const
      ((L a).projection x - x)).const_add x

theorem fderiv_sigma (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x) :
    fderiv ℝ (fun y => sigma s L θ y t) x = spatialDerivative s L θ x t :=
  (hasFDerivAt_sigma s L θ x t hθ).fderiv

theorem deriv_sigma (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (hθ : ∀ a ∈ s, DifferentiableAt ℝ (θ a x) t) :
    deriv (sigma s L θ x) t = timeDerivative s L θ x t :=
  (hasDerivAt_sigma s L θ x t hθ).deriv

/-- The purely projection part of the error on a tangent vector. -/
def w₁ (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ) (v : Spatial n) : Spatial n :=
  ∑ a ∈ s, θ a x t • ((L a).linearProjection v - v)

/-- The part coming from differentiating the weights. -/
def w₂ (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ) (v : Spatial n) : Spatial n :=
  ∑ a ∈ s, dx θ a x t v • ((L a).projection x - x)

theorem spatialDerivative_apply (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x v : Spatial n) (t : ℝ) :
    spatialDerivative s L θ x t v = v + w₁ s L θ x t v + w₂ s L θ x t v := by
  simp [spatialDerivative, w₁, w₂, sum_add_distrib, add_assoc]

theorem convex_part (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x v : Spatial n) (t : ℝ) :
    v + w₁ s L θ x t v =
      (1 - ∑ a ∈ s, θ a x t) • v + ∑ a ∈ s, θ a x t • (L a).linearProjection v := by
  simp only [w₁, smul_sub, sum_sub_distrib, sub_smul, one_smul, sum_smul]
  abel

/-- Finite triangle inequality retaining only indices with nonzero coefficients. -/
theorem norm_sum_smul_le (s : Finset ι) (c : ι → ℝ) (u : ι → Spatial n) (B : ℝ)
    (hu : ∀ a ∈ s, c a ≠ 0 → ‖u a‖ ≤ B) :
    ‖∑ a ∈ s, c a • u a‖ ≤ (∑ a ∈ s, |c a|) * B := by
  calc
    _ ≤ ∑ a ∈ s, ‖c a • u a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ s, |c a| * B := by
      apply sum_le_sum
      intro a ha
      by_cases hc : c a = 0
      · simp [hc]
      · simpa only [norm_smul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (hu a ha hc) (abs_nonneg (c a))
    _ = _ := (sum_mul ..).symm

/-- Quantitative hypotheses on weights, without any geometric conclusion. -/
structure WeightBounds (s : Finset ι) (θ : ι → Spatial n → ℝ → ℝ)
    (x : Spatial n) (t C₀ r : ℝ) : Prop where
  nonneg : ∀ a ∈ s, 0 ≤ θ a x t
  sum_le : ∑ a ∈ s, θ a x t ≤ 1
  spatial : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r
  time : ∑ a ∈ s, |dt θ a x t| ≤ C₀ / r ^ 2

variable (s : Finset ι) (L : ι → AffineSpatialPlane n m)
  (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t C₀ H r α : ℝ)

theorem displacement_le (hr : 0 < r) (hH : 0 ≤ H)
    (hb : WeightBounds s θ x t C₀ r)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r) :
    ‖sigma s L θ x t - x‖ ≤ H * r := by
  have h := norm_sum_smul_le s (fun a => θ a x t)
    (fun a => (L a).projection x - x) (H * r)
    (fun a ha h => he a ha (Or.inl h))
  have ha : (∑ a ∈ s, |θ a x t|) = ∑ a ∈ s, θ a x t := by
    apply sum_congr rfl
    intro a ha
    exact abs_of_nonneg (hb.nonneg a ha)
  rw [ha] at h
  simpa only [sigma, add_sub_cancel_left] using
    h.trans ((mul_le_mul_of_nonneg_right hb.sum_le (mul_nonneg hH hr.le)).trans_eq (one_mul _))

theorem norm_w₂_le (hr : 0 < r) (hH : 0 ≤ H)
    (hb : WeightBounds s θ x t C₀ r)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (v : Spatial n) : ‖w₂ s L θ x t v‖ ≤ C₀ * H * ‖v‖ := by
  have hd : (∑ a ∈ s, |dx θ a x t v|) ≤ (C₀ / r) * ‖v‖ := by
    calc
      _ ≤ ∑ a ∈ s, ‖dx θ a x t‖ * ‖v‖ :=
        sum_le_sum fun a _ => (dx θ a x t).le_opNorm v
      _ = (∑ a ∈ s, ‖dx θ a x t‖) * ‖v‖ := (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hb.spatial (norm_nonneg v)
  calc
    _ ≤ (∑ a ∈ s, |dx θ a x t v|) * (H * r) := by
      apply norm_sum_smul_le
      intro a ha hv
      apply he a ha
      exact Or.inr (Or.inl (fun h => hv (by simp [h])))
    _ ≤ ((C₀ / r) * ‖v‖) * (H * r) :=
      mul_le_mul_of_nonneg_right hd (mul_nonneg hH hr.le)
    _ = _ := by field_simp

theorem norm_convex_part_le (hb : WeightBounds s θ x t C₀ r) (v : Spatial n) :
    ‖v + w₁ s L θ x t v‖ ≤ ‖v‖ := by
  rw [convex_part]
  have hs : 0 ≤ 1 - ∑ a ∈ s, θ a x t := sub_nonneg.mpr hb.sum_le
  calc
    _ ≤ ‖(1 - ∑ a ∈ s, θ a x t) • v‖ + ‖∑ a ∈ s, θ a x t • (L a).linearProjection v‖ := norm_add_le _ _
    _ ≤ (1 - ∑ a ∈ s, θ a x t) * ‖v‖ + (∑ a ∈ s, θ a x t) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
      apply add_le_add le_rfl
      have h := norm_sum_smul_le s (fun a => θ a x t)
        (fun a => (L a).linearProjection v) ‖v‖
        (fun a _ _ => (L a).direction.norm_starProjection_apply_le v)
      have ha : (∑ a ∈ s, |θ a x t|) = ∑ a ∈ s, θ a x t :=
        sum_congr rfl (fun a ha => abs_of_nonneg (hb.nonneg a ha))
      rwa [ha] at h
    _ = _ := by ring

theorem spatialDerivative_norm_le (hr : 0 < r) (hC : 0 ≤ C₀) (hH : 0 ≤ H)
    (hb : WeightBounds s θ x t C₀ r)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r) :
    ‖spatialDerivative s L θ x t‖ ≤ 1 + C₀ * H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [spatialDerivative_apply]
  calc
    _ ≤ ‖v + w₁ s L θ x t v‖ + ‖w₂ s L θ x t v‖ := norm_add_le _ _
    _ ≤ ‖v‖ + C₀ * H * ‖v‖ := add_le_add
      (norm_convex_part_le s L θ x t C₀ r hb v) (norm_w₂_le s L θ x t C₀ H r hr hH hb he v)
    _ = _ := by ring

theorem timeDerivative_norm_le (hr : 0 < r) (hH : 0 ≤ H)
    (hb : WeightBounds s θ x t C₀ r)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r) :
    ‖timeDerivative s L θ x t‖ ≤ C₀ * H / r := by
  calc
    _ ≤ (∑ a ∈ s, |dt θ a x t|) * (H * r) :=
      norm_sum_smul_le s _ _ _ (fun a ha h => he a ha (Or.inr (Or.inr (Or.inr h))))
    _ ≤ (C₀ / r ^ 2) * (H * r) := mul_le_mul_of_nonneg_right hb.time (mul_nonneg hH hr.le)
    _ = _ := by field_simp

/-- Comparison with the actual tangent projection, used only on tangent vectors. -/
theorem tangent_residual_le (T : Submodule ℝ (Spatial n)) (K : AffineSpatialPlane n m)
    (hc : ‖T.starProjection - K.linearProjection‖ ≤ α)
    (v : Spatial n) (hv : v ∈ T) : ‖v - K.linearProjection v‖ ≤ α * ‖v‖ := by
  have hid : (T.starProjection - K.linearProjection) v = v - K.linearProjection v := by
    simp [T.starProjection_eq_self_iff.mpr hv]
  rw [← hid]
  exact ((T.starProjection - K.linearProjection).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg v))

/-- The signed orthogonality identity which prevents a linear angle loss. -/
theorem inner_projection_error (K : AffineSpatialPlane n m) (v : Spatial n) :
    ⟪v, K.linearProjection v - v⟫ = -‖v - K.linearProjection v‖ ^ 2 := by
  have ho : ⟪K.linearProjection v, v - K.linearProjection v⟫ = 0 :=
    K.direction.sub_starProjection_mem_orthogonal v _ (K.direction.starProjection_apply_mem v)
  calc
    _ = -⟪v, v - K.linearProjection v⟫ := by rw [← inner_neg_right]; congr 1; abel
    _ = -⟪v - K.linearProjection v, v - K.linearProjection v⟫ := by
      rw [inner_sub_left, ho, sub_zero]
    _ = _ := by rw [real_inner_self_eq_norm_sq]

/-- The affine residual is also normal to the direction, despite the translation. -/
theorem inner_affine_residual (K : AffineSpatialPlane n m) (x v : Spatial n) :
    ⟪v, K.projection x - x⟫ = ⟪v - K.linearProjection v, K.projection x - x⟫ := by
  have he : K.projection x - x ∈ K.directionᗮ := by
    simpa only [neg_sub] using K.directionᗮ.neg_mem (K.residual_orthogonal x)
  have ho : ⟪K.linearProjection v, K.projection x - x⟫ = 0 :=
    he _ (K.direction.starProjection_apply_mem v)
  rw [inner_sub_left, ho, sub_zero]

theorem inner_w₁ (v : Spatial n) :
    ⟪v, w₁ s L θ x t v⟫ = -∑ a ∈ s, θ a x t * ‖v - (L a).linearProjection v‖ ^ 2 := by
  simp [w₁, inner_sum, inner_smul_right, inner_projection_error, mul_neg, sum_neg_distrib]

theorem norm_w₁_le (hα : 0 ≤ α) (hb : WeightBounds s θ x t C₀ r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v : Spatial n) (hv : v ∈ T) : ‖w₁ s L θ x t v‖ ≤ α * ‖v‖ := by
  have h := norm_sum_smul_le s (fun a => θ a x t)
    (fun a => (L a).linearProjection v - v) (α * ‖v‖) (by
      intro a ha hn
      rw [norm_sub_rev]
      exact tangent_residual_le α T (L a) (hc a ha (Or.inl hn)) v hv)
  have ha : (∑ a ∈ s, |θ a x t|) = ∑ a ∈ s, θ a x t :=
    sum_congr rfl (fun a ha => abs_of_nonneg (hb.nonneg a ha))
  rw [ha] at h
  exact h.trans ((mul_le_mul_of_nonneg_right hb.sum_le (mul_nonneg hα (norm_nonneg v))).trans_eq (one_mul _))

theorem abs_inner_w₁_le (_hα : 0 ≤ α) (hb : WeightBounds s θ x t C₀ r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v : Spatial n) (hv : v ∈ T) :
    |⟪v, w₁ s L θ x t v⟫| ≤ α ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_w₁, abs_neg, abs_of_nonneg
    (sum_nonneg (fun a ha => mul_nonneg (hb.nonneg a ha) (sq_nonneg _)))]
  calc
    _ ≤ ∑ a ∈ s, θ a x t * (α ^ 2 * ‖v‖ ^ 2) := by
      apply sum_le_sum
      intro a ha
      by_cases hn : θ a x t = 0
      · simp [hn]
      · apply mul_le_mul_of_nonneg_left _ (hb.nonneg a ha)
        have h := tangent_residual_le α T (L a) (hc a ha (Or.inl hn)) v hv
        nlinarith [norm_nonneg (v - (L a).linearProjection v), mul_nonneg _hα (norm_nonneg v)]
    _ = (∑ a ∈ s, θ a x t) * (α ^ 2 * ‖v‖ ^ 2) := (sum_mul ..).symm
    _ ≤ α ^ 2 * ‖v‖ ^ 2 := by
      simpa using mul_le_mul_of_nonneg_right hb.sum_le (mul_nonneg (sq_nonneg α) (sq_nonneg ‖v‖))

theorem abs_inner_w₂_le (hr : 0 < r) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hb : WeightBounds s θ x t C₀ r)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v : Spatial n) (hv : v ∈ T) :
    |⟪v, w₂ s L θ x t v⟫| ≤ C₀ * α * H * ‖v‖ ^ 2 := by
  simp only [w₂, inner_sum, inner_smul_right]
  calc
    _ ≤ ∑ a ∈ s, |dx θ a x t v * ⟪v, (L a).projection x - x⟫| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ s, ‖dx θ a x t‖ * ‖v‖ * (α * ‖v‖ * (H * r)) := by
      apply sum_le_sum
      intro a ha
      by_cases hd : dx θ a x t = 0
      · simp [hd]
      · have ha' : Active θ a x t := Or.inr (Or.inl hd)
        rw [abs_mul, inner_affine_residual]
        apply mul_le_mul ((dx θ a x t).le_opNorm v) _ (abs_nonneg _) (by positivity)
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (tangent_residual_le α T (L a) (hc a ha ha') v hv)
            (he a ha ha') (norm_nonneg _) (mul_nonneg hα (norm_nonneg v)))
    _ = (∑ a ∈ s, ‖dx θ a x t‖) * (‖v‖ * (α * ‖v‖ * (H * r))) := by
      simp only [mul_assoc, sum_mul]
    _ ≤ (C₀ / r) * (‖v‖ * (α * ‖v‖ * (H * r))) :=
      mul_le_mul_of_nonneg_right hb.spatial (by positivity)
    _ = _ := by field_simp

/-- A scalar estimate used after the two orthogonality bounds. -/
theorem quadratic_constant (C a h : ℝ) (hC : 0 ≤ C) :
    2 * (a ^ 2 + C * a * h) + (a + C * h) ^ 2 ≤
      10 * (1 + C) ^ 2 * (a ^ 2 + h ^ 2) := by
  have hcross : 2 * a * h ≤ a ^ 2 + h ^ 2 := by nlinarith [sq_nonneg (a - h)]
  have hm := mul_le_mul_of_nonneg_left hcross (by positivity : 0 ≤ 2 * C)
  have hn : 0 ≤ (7 + 18 * C + 10 * C ^ 2) * a ^ 2 := by positivity
  have hn' : 0 ≤ (10 + 18 * C + 9 * C ^ 2) * h ^ 2 := by positivity
  nlinarith

theorem quadratic_distortion (hr : 0 < r) (hC : 0 ≤ C₀) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hb : WeightBounds s θ x t C₀ r)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v : Spatial n) (hv : v ∈ T) :
    |‖spatialDerivative s L θ x t v‖ ^ 2 - ‖v‖ ^ 2| ≤
      10 * (1 + C₀) ^ 2 * (α ^ 2 + H ^ 2) * ‖v‖ ^ 2 := by
  have hi₁ := abs_inner_w₁_le s L θ x t C₀ r α hα hb T hc v hv
  have hi₂ := abs_inner_w₂_le s L θ x t C₀ H r α hr hH hα hb he T hc v hv
  have hn₁ := norm_w₁_le s L θ x t C₀ r α hα hb T hc v hv
  have hn₂ := norm_w₂_le s L θ x t C₀ H r hr hH hb he v
  have hn : ‖w₁ s L θ x t v + w₂ s L θ x t v‖ ≤ (α + C₀ * H) * ‖v‖ := by
    calc
      _ ≤ ‖w₁ s L θ x t v‖ + ‖w₂ s L θ x t v‖ := norm_add_le _ _
      _ ≤ α * ‖v‖ + C₀ * H * ‖v‖ := add_le_add hn₁ hn₂
      _ = _ := by ring
  have hs : ‖w₁ s L θ x t v + w₂ s L θ x t v‖ ^ 2 ≤
      (α + C₀ * H) ^ 2 * ‖v‖ ^ 2 := by
    nlinarith [norm_nonneg (w₁ s L θ x t v + w₂ s L θ x t v),
      mul_nonneg (add_nonneg hα (mul_nonneg hC hH)) (norm_nonneg v)]
  rw [spatialDerivative_apply, add_assoc, norm_add_sq_real, inner_add_right]
  calc
    _ = |2 * (⟪v, w₁ s L θ x t v⟫ + ⟪v, w₂ s L θ x t v⟫) +
        ‖w₁ s L θ x t v + w₂ s L θ x t v‖ ^ 2| := by congr 1; ring
    _ ≤ 2 * (|⟪v, w₁ s L θ x t v⟫| + |⟪v, w₂ s L θ x t v⟫|) +
        ‖w₁ s L θ x t v + w₂ s L θ x t v‖ ^ 2 := by
      calc
        _ ≤ |2 * (⟪v, w₁ s L θ x t v⟫ + ⟪v, w₂ s L θ x t v⟫)| +
            |‖w₁ s L θ x t v + w₂ s L θ x t v‖ ^ 2| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg ‖w₁ s L θ x t v + w₂ s L θ x t v‖)]
          exact add_le_add (mul_le_mul_of_nonneg_left (abs_add_le _ _)
            (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ ≤ (2 * (α ^ 2 + C₀ * α * H) + (α + C₀ * H) ^ 2) * ‖v‖ ^ 2 := by
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (quadratic_constant C₀ α H hC) (sq_nonneg _)

/-- One-step estimate for the weighted projection `sigma`: displacement at most `H r`,
spatial derivative at most `1 + C₀ H`, time derivative at most `C₀ H / r`, and
quadratic distortion on `T` of order `(α² + H²)`. These bounds concern the actual
derivatives, not bounds postulated on a jet. -/
theorem one_step (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t C₀ H r α : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C₀) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hx : ∀ a ∈ s, DifferentiableAt ℝ (fun y => θ a y t) x)
    (ht : ∀ a ∈ s, DifferentiableAt ℝ (θ a x) t)
    (hb : WeightBounds s θ x t C₀ r)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α) :
    ‖sigma s L θ x t - x‖ ≤ H * r ∧
    ‖fderiv ℝ (fun y => sigma s L θ y t) x‖ ≤ 1 + C₀ * H ∧
    ‖deriv (sigma s L θ x) t‖ ≤ C₀ * H / r ∧
    ∀ v ∈ T, |‖fderiv ℝ (fun y => sigma s L θ y t) x v‖ ^ 2 - ‖v‖ ^ 2| ≤
      10 * (1 + C₀) ^ 2 * (α ^ 2 + H ^ 2) * ‖v‖ ^ 2 := by
  rw [fderiv_sigma s L θ x t hx, deriv_sigma s L θ x t ht]
  exact ⟨displacement_le s L θ x t C₀ H r hr hH hb he,
    spatialDerivative_norm_le s L θ x t C₀ H r hr hC hH hb he,
    timeDerivative_norm_le s L θ x t C₀ H r hr hH hb he,
    quadratic_distortion s L θ x t C₀ H r α hr hC hH hα hb he T hc⟩

end ParabolicRectifiability.CoherentProjection
