import ParabolicRectifiability.Geometry.CoherentProjection

/-!
# The spatial Hessian of a finite weighted projection

This derives the second derivative of the actual `sigma` at fixed real time.
The two mixed terms come from differentiating the affine residual as well as
the weight. The activity predicate is the one of `one_step`. Smooth
partitions with these quantitative bounds are constructed separately.
-/

noncomputable section

namespace ParabolicRectifiability.CoherentProjection

open Finset ContinuousLinearMap
open scoped Topology

variable {ι : Type*} {n m : ℕ}

/-- The actual second spatial derivative of a weight, as a curried bilinear map. -/
def dxx (θ : ι → Spatial n → ℝ → ℝ) (a : ι) (x : Spatial n) (t : ℝ) :
    Spatial n →L[ℝ] Spatial n →L[ℝ] ℝ :=
  fderiv ℝ (fun y => dx θ a y t) x

theorem contDiffAt_sigma (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (hθ : ∀ a ∈ s, ContDiffAt ℝ 2 (fun y => θ a y t) x) :
    ContDiffAt ℝ 2 (fun y => sigma s L θ y t) x := by
  apply contDiffAt_id.add
  apply ContDiffAt.sum
  intro a ha
  have hp : ContDiffAt ℝ 2 (fun y => (L a).projection y) x :=
    contDiffAt_const.add (L a).linearProjection.contDiff.contDiffAt
  exact (hθ a ha).smul (hp.sub contDiffAt_id)

theorem differentiableAt_dx (θ : ι → Spatial n → ℝ → ℝ) (a : ι)
    (x : Spatial n) (t : ℝ) (hθ : ContDiffAt ℝ 2 (fun y => θ a y t) x) :
    DifferentiableAt ℝ (fun y => dx θ a y t) x := by
  exact (hθ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one

/-- Product rules for the actual map give both mixed terms and the Hessian term. -/
theorem fderiv_fderiv_sigma (s : Finset ι) (L : ι → AffineSpatialPlane n m)
    (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t : ℝ)
    (hθ : ∀ a ∈ s, ContDiffAt ℝ 2 (fun y => θ a y t) x) (v w : Spatial n) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => sigma s L θ z t) y) x v w =
      (∑ a ∈ s, dx θ a x t v • ((L a).linearProjection w - w)) +
      (∑ a ∈ s, dx θ a x t w • ((L a).linearProjection v - v)) +
      ∑ a ∈ s, dxx θ a x t v w • ((L a).projection x - x) := by
  let g : Spatial n → Spatial n := fun y => w + ∑ a ∈ s,
    (θ a y t • ((L a).linearProjection w - w) +
      dx θ a y t w • ((L a).projection y - y))
  let q : Spatial n →L[ℝ] Spatial n := ∑ a ∈ s,
    ((dx θ a x t).smulRight ((L a).linearProjection w - w) +
      (dx θ a x t w • ((L a).linearProjection - ContinuousLinearMap.id ℝ (Spatial n)) +
        ((dxx θ a x t).flip w).smulRight ((L a).projection x - x)))
  have hg : HasFDerivAt g q x := by
    dsimp only [g, q]
    refine (HasFDerivAt.fun_sum ?_).const_add w
    intro a ha
    have hd : HasFDerivAt (fun y => dx θ a y t w) ((dxx θ a x t).flip w) x := by
      simpa [dxx] using
        (differentiableAt_dx θ a x t (hθ a ha)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
    exact ((hθ a ha).differentiableAt (by norm_num)).hasFDerivAt.smul_const
      ((L a).linearProjection w - w) |>.add
        (hd.smul (((L a).linearProjection.hasFDerivAt.const_add (L a).anchor).sub (hasFDerivAt_id x)))
  have hnear : ∀ᶠ y in 𝓝 x, ∀ a ∈ s, DifferentiableAt ℝ (fun z => θ a z t) y := by
    rw [Finset.eventually_all]
    intro a ha
    exact ((hθ a ha).eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => sigma s L θ z t) y w) =ᶠ[𝓝 x] g := by
    filter_upwards [hnear] with y hy
    rw [fderiv_sigma s L θ y t hy]
    simp [spatialDerivative, g]
  have hf : HasFDerivAt (fun y => fderiv ℝ (fun z => sigma s L θ z t) y w) q x :=
    heq.hasFDerivAt_iff.mpr hg
  have hσ : DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => sigma s L θ z t) y) x :=
    ((contDiffAt_sigma s L θ x t hθ).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have h := congrArg (fun A : Spatial n →L[ℝ] Spatial n => A v) hf.fderiv
  rw [fderiv_clm_apply hσ (differentiableAt_const w)] at h
  simpa [q, sum_add_distrib, add_assoc] using h

variable (s : Finset ι) (L : ι → AffineSpatialPlane n m)
  (θ : ι → Spatial n → ℝ → ℝ) (x : Spatial n) (t C₀ H r α : ℝ)

/-- Each mixed term has one derivative of a weight and one tangent projection error. -/
theorem hessian_mixed_term_le (hα : 0 ≤ α)
    (hd : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v w : Spatial n) (hw : w ∈ T) :
    ‖∑ a ∈ s, dx θ a x t v • ((L a).linearProjection w - w)‖ ≤
      (C₀ * α / r) * ‖v‖ * ‖w‖ := by
  have hs : (∑ a ∈ s, |dx θ a x t v|) ≤ (C₀ / r) * ‖v‖ := by
    calc
      _ ≤ ∑ a ∈ s, ‖dx θ a x t‖ * ‖v‖ := sum_le_sum fun a _ => (dx θ a x t).le_opNorm v
      _ = (∑ a ∈ s, ‖dx θ a x t‖) * ‖v‖ := (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hd (norm_nonneg v)
  calc
    _ ≤ (∑ a ∈ s, |dx θ a x t v|) * (α * ‖w‖) := by
      apply norm_sum_smul_le
      intro a ha hn
      have ha' : Active θ a x t := Or.inr (Or.inl (fun hz => hn (by simp [hz])))
      rw [norm_sub_rev]
      exact tangent_residual_le α T (L a) (hc a ha ha') w hw
    _ ≤ ((C₀ / r) * ‖v‖) * (α * ‖w‖) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg hα (norm_nonneg w))
    _ = _ := by ring

/-- Second-derivative-only active indices also need the affine height bound. -/
theorem hessian_residual_term_le (hr : 0 < r) (hH : 0 ≤ H)
    (hdd : ∑ a ∈ s, ‖dxx θ a x t‖ ≤ C₀ / r ^ 2)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (v w : Spatial n) :
    ‖∑ a ∈ s, dxx θ a x t v w • ((L a).projection x - x)‖ ≤
      (C₀ * H / r) * ‖v‖ * ‖w‖ := by
  have hs : (∑ a ∈ s, |dxx θ a x t v w|) ≤ (C₀ / r ^ 2) * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ∑ a ∈ s, ‖dxx θ a x t‖ * ‖v‖ * ‖w‖ := by
        apply sum_le_sum
        intro a _
        exact ((dxx θ a x t v).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right ((dxx θ a x t).le_opNorm v) (norm_nonneg w))
      _ = (∑ a ∈ s, ‖dxx θ a x t‖) * ‖v‖ * ‖w‖ := by rw [sum_mul, sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdd (norm_nonneg v)) (norm_nonneg w)
  calc
    _ ≤ (∑ a ∈ s, |dxx θ a x t v w|) * (H * r) := by
      apply norm_sum_smul_le
      intro a ha hn
      apply he a ha
      exact Or.inr (Or.inr (Or.inl (fun hz => hn (by change dxx θ a x t = 0 at hz; simp [hz]))))
    _ ≤ ((C₀ / r ^ 2) * ‖v‖ * ‖w‖) * (H * r) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg hH hr.le)
    _ = _ := by field_simp

/-- A sharper intermediate bound, before enlarging to the constant `10 (1 + C₀)²`. -/
theorem hessian_norm_le_sharp (hr : 0 < r) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hθ : ∀ a ∈ s, ContDiffAt ℝ 2 (fun y => θ a y t) x)
    (hd : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r)
    (hdd : ∑ a ∈ s, ‖dxx θ a x t‖ ≤ C₀ / r ^ 2)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v w : Spatial n) (hv : v ∈ T) (hw : w ∈ T) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => sigma s L θ z t) y) x v w‖ ≤
      (C₀ * (2 * α + H) / r) * ‖v‖ * ‖w‖ := by
  rw [fderiv_fderiv_sigma s L θ x t hθ v w]
  have h₁ := hessian_mixed_term_le s L θ x t C₀ r α hα hd T hc v w hw
  have h₂ := hessian_mixed_term_le s L θ x t C₀ r α hα hd T hc w v hv
  have h₃ := hessian_residual_term_le s L θ x t C₀ H r hr hH hdd he v w
  calc
    _ ≤ (‖∑ a ∈ s, dx θ a x t v • ((L a).linearProjection w - w)‖ +
        ‖∑ a ∈ s, dx θ a x t w • ((L a).linearProjection v - v)‖) +
        ‖∑ a ∈ s, dxx θ a x t v w • ((L a).projection x - x)‖ := norm_add₃_le
    _ ≤ ((C₀ * α / r) * ‖v‖ * ‖w‖ + (C₀ * α / r) * ‖w‖ * ‖v‖) +
        (C₀ * H / r) * ‖v‖ * ‖w‖ := add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

/-- Hessian bound complementing `one_step`: on tangent vectors the second spatial
derivative of `sigma` is at most `10 (1 + C₀)² (α + H) / r`.
No equality or lower bound on the sum of the weights is needed. -/
theorem hessian_norm_le (hr : 0 < r) (hC : 0 ≤ C₀) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (hθ : ∀ a ∈ s, ContDiffAt ℝ 2 (fun y => θ a y t) x)
    (hd : ∑ a ∈ s, ‖dx θ a x t‖ ≤ C₀ / r)
    (hdd : ∑ a ∈ s, ‖dxx θ a x t‖ ≤ C₀ / r ^ 2)
    (he : ∀ a ∈ s, Active θ a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ s, Active θ a x t → ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v w : Spatial n) (hv : v ∈ T) (hw : w ∈ T) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => sigma s L θ z t) y) x v w‖ ≤
      (10 * (1 + C₀) ^ 2 * (α + H) / r) * ‖v‖ * ‖w‖ := by
  have hb : 2 * C₀ ≤ 10 * (1 + C₀) ^ 2 := by nlinarith [sq_nonneg C₀]
  have hcst : C₀ * (2 * α + H) ≤ 10 * (1 + C₀) ^ 2 * (α + H) := by
    nlinarith [mul_le_mul_of_nonneg_right hb (add_nonneg hα hH), mul_nonneg hC hH]
  exact (hessian_norm_le_sharp s L θ x t C₀ H r α hr hH hα hθ hd hdd he T hc v w hv hw).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcst hr.le) (norm_nonneg v)) (norm_nonneg w))

end ParabolicRectifiability.CoherentProjection
