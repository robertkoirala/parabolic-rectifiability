import ParabolicRectifiability.Geometry.SmoothPartition
import ParabolicRectifiability.Geometry.CoherentProjection

/-!
# From the smooth parabolic partition to the projection weight hypotheses

A smooth parabolic partition (`IsSmoothParabolicPartition`) has weights `θ_a` on
ordinary coordinates `Spatial n × ℝ`, with the bound on `∂_t θ_a` only inside the
combined estimate `∑ (‖D_x² θ_a‖ + |∂_t θ_a|) ≤ C₀ / r²`. `CoherentProjection.one_step`
uses *curried* weights `θ a x t`, and its `WeightBounds` hypothesis asks for the time
bound separately: `∑ |∂_t θ_a| ≤ C₀ / r²`.

This file does the translation, adding no assumption and weakening nothing:

* `curriedWeight θ a x t = θ a (x, t)`;
* `weightBounds_curriedWeight`: any `IsSmoothParabolicPartition` with constant
  `C₀` satisfies `CoherentProjection.WeightBounds` with the same `C₀` and `r` at
  every point. The separate time bound follows from the combined one because
  `‖D_x² θ_a‖ ≥ 0`;
* differentiability of the curried weights in `x` and in `t` at every point,
  from joint smoothness;
* the specializations to the actual weights `parabolicWeight` with
  `C₀ = partitionConstant n σ`;
* `one_step_parabolicWeight`: the actual weights fed into
  `CoherentProjection.one_step`. The geometric inputs of `one_step` (the active
  plane height bound `H r` and the tangent projection comparison `α`) remain
  genuine hypotheses; no weight bound is assumed.
-/

noncomputable section

open Set
open scoped ContDiff

namespace ParabolicRectifiability

open CoherentProjection

variable {n m : ℕ} {ι : Type*}

/-- The curried form `θ a x t = θ a (x, t)` of weights on ordinary coordinates. -/
def curriedWeight (θ : ι → Coordinates n → ℝ) (a : ι) (x : Spatial n) (t : ℝ) : ℝ :=
  θ a (x, t)

@[simp]
theorem curriedWeight_apply (θ : ι → Coordinates n → ℝ) (a : ι) (x : Spatial n) (t : ℝ) :
    curriedWeight θ a x t = θ a (x, t) :=
  rfl

/-- Jointly smooth weights are differentiable in the spatial variable. -/
theorem differentiableAt_curriedWeight_spatial {θ : ι → Coordinates n → ℝ} {a : ι}
    (h : ContDiff ℝ ∞ (θ a)) (x : Spatial n) (t : ℝ) :
    DifferentiableAt ℝ (fun y => curriedWeight θ a y t) x :=
  DifferentiableAt.comp (𝕜 := ℝ) x (h.differentiable (by simp) (x, t))
    (differentiableAt_id.prodMk (differentiableAt_const t))

/-- Jointly smooth weights are differentiable in time. -/
theorem differentiableAt_curriedWeight_time {θ : ι → Coordinates n → ℝ} {a : ι}
    (h : ContDiff ℝ ∞ (θ a)) (x : Spatial n) (t : ℝ) :
    DifferentiableAt ℝ (curriedWeight θ a x) t :=
  DifferentiableAt.comp (𝕜 := ℝ) t (h.differentiable (by simp) (x, t))
    ((differentiableAt_const x).prodMk differentiableAt_id)

/-- **The weight hypotheses of `CoherentProjection`.** A smooth parabolic
partition with constant `C₀` at radius `r` satisfies `WeightBounds` with the same
constant at every point `(x, t)`: nonnegativity, sum at most one, the spatial
derivative bound `C₀ / r` and the separate time-derivative bound `C₀ / r²`. -/
theorem weightBounds_curriedWeight {I : Finset ι} {z : ι → Space n} {r C₀ : ℝ}
    {θ : ι → Coordinates n → ℝ} (hP : IsSmoothParabolicPartition n I z r C₀ θ)
    (x : Spatial n) (t : ℝ) :
    WeightBounds I (curriedWeight θ) x t C₀ r where
  nonneg a _ := hP.nonneg a (x, t)
  sum_le := hP.sum_le_one (x, t)
  spatial := hP.first x t
  time := by
    refine le_trans (Finset.sum_le_sum fun a _ => ?_) (hP.second x t)
    exact le_add_of_nonneg_left (by positivity)

/-- The actual weights satisfy the `WeightBounds` hypotheses with `C₀ = partitionConstant n σ`. -/
theorem weightBounds_parabolicWeight {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n)
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (x : Spatial n) (t : ℝ) :
    WeightBounds I (curriedWeight (parabolicWeight r I z)) x t (partitionConstant n σ) r :=
  weightBounds_curriedWeight (isSmoothParabolicPartition_parabolicWeight hσ hr I z hdisj) x t

/-- The actual weights are differentiable in `x` at every point. -/
theorem differentiableAt_parabolicWeight_spatial (r : ℝ) (I : Finset ι) (z : ι → Space n)
    (a : ι) (x : Spatial n) (t : ℝ) :
    DifferentiableAt ℝ (fun y => curriedWeight (parabolicWeight r I z) a y t) x :=
  differentiableAt_curriedWeight_spatial (contDiff_parabolicWeight r I z a) x t

/-- The actual weights are differentiable in `t` at every point. -/
theorem differentiableAt_parabolicWeight_time (r : ℝ) (I : Finset ι) (z : ι → Space n)
    (a : ι) (x : Spatial n) (t : ℝ) :
    DifferentiableAt ℝ (curriedWeight (parabolicWeight r I z) a x) t :=
  differentiableAt_curriedWeight_time (contDiff_parabolicWeight r I z a) x t

/-- **Application.** The actual smooth partition weights, fed into the finite weighted
projection `CoherentProjection.sigma`, satisfy the conclusions of
`CoherentProjection.one_step` with `C₀ = partitionConstant n σ`. The weight hypotheses of
`one_step` are all discharged; the active-plane height bound `he` and the tangent
projection comparison `hc` are the geometric inputs of `one_step`, unchanged. -/
theorem one_step_parabolicWeight {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n)
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (L : ι → AffineSpatialPlane n m) (x : Spatial n) (t H α : ℝ) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (he : ∀ a ∈ I, Active (curriedWeight (parabolicWeight r I z)) a x t →
      ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ I, Active (curriedWeight (parabolicWeight r I z)) a x t →
      ‖T.starProjection - (L a).linearProjection‖ ≤ α) :
    ‖sigma I L (curriedWeight (parabolicWeight r I z)) x t - x‖ ≤ H * r ∧
    ‖fderiv ℝ (fun y => sigma I L (curriedWeight (parabolicWeight r I z)) y t) x‖ ≤
      1 + partitionConstant n σ * H ∧
    ‖deriv (sigma I L (curriedWeight (parabolicWeight r I z)) x) t‖ ≤
      partitionConstant n σ * H / r ∧
    ∀ v ∈ T, |‖fderiv ℝ (fun y => sigma I L (curriedWeight (parabolicWeight r I z)) y t) x v‖ ^ 2 -
        ‖v‖ ^ 2| ≤ 10 * (1 + partitionConstant n σ) ^ 2 * (α ^ 2 + H ^ 2) * ‖v‖ ^ 2 :=
  one_step I L (curriedWeight (parabolicWeight r I z)) x t (partitionConstant n σ) H r α hr
    (zero_le_one.trans (one_le_partitionConstant n hσ)) hH hα
    (fun a _ => differentiableAt_parabolicWeight_spatial r I z a x t)
    (fun a _ => differentiableAt_parabolicWeight_time r I z a x t)
    (weightBounds_parabolicWeight hσ hr I z hdisj x t) he T hc

end ParabolicRectifiability
