import ParabolicRectifiability.Geometry.PartitionAdapter
import ParabolicRectifiability.Geometry.CoherentProjectionHessian

/-!
# From the smooth parabolic partition to the Hessian weight hypotheses

`CoherentProjectionHessian.hessian_norm_le` asks, at a point `(x, t)` and for a finite
index set `s`, for `C²` regularity of each weight in the spatial variable and the two
quantitative bounds `∑ ‖dx θ a x t‖ ≤ C₀ / r` and `∑ ‖dxx θ a x t‖ ≤ C₀ / r ^ 2`.
The smooth parabolic partition (`IsSmoothParabolicPartition`) gives exactly these:
the first bound is its field `first` and the second follows from its combined field
`second` because the discarded time-derivative terms are nonnegative.

This file only extracts these facts for the curried weights; the geometric hypotheses
(`he`, `hc`) of the Hessian estimate stay hypotheses of the final corollaries.
-/

noncomputable section

open Set
open scoped ContDiff

namespace ParabolicRectifiability

open CoherentProjection

variable {n m : ℕ} {ι : Type*}

/-- Jointly smooth weights are `C²` in the spatial variable at fixed time. -/
theorem contDiffAt_curriedWeight_spatial {θ : ι → Coordinates n → ℝ} {a : ι}
    (h : ContDiff ℝ ∞ (θ a)) (x : Spatial n) (t : ℝ) :
    ContDiffAt ℝ 2 (fun y => curriedWeight θ a y t) x := by
  have hle : (2 : WithTop ℕ∞) ≤ ∞ := by simp
  have h2 : ContDiff ℝ 2 (θ a) := h.of_le hle
  exact (h2.comp (contDiff_id.prodMk contDiff_const)).contDiffAt

/-- Item 1: every weight of a smooth parabolic partition is `C²` in `x` at every point. -/
theorem contDiffAt_curriedWeight_of_partition {I : Finset ι} {z : ι → Space n} {r C₀ : ℝ}
    {θ : ι → Coordinates n → ℝ} (hP : IsSmoothParabolicPartition n I z r C₀ θ)
    (s : Finset ι) (x : Spatial n) (t : ℝ) :
    ∀ a ∈ s, ContDiffAt ℝ 2 (fun y => curriedWeight θ a y t) x :=
  fun a _ => contDiffAt_curriedWeight_spatial (hP.contDiff a) x t

/-- Item 2: the first-derivative bound `C₀ / r` for the actual `dx`, on any `s ⊆ I`. -/
theorem sum_norm_dx_curriedWeight_le {I : Finset ι} {z : ι → Space n} {r C₀ : ℝ}
    {θ : ι → Coordinates n → ℝ} (hP : IsSmoothParabolicPartition n I z r C₀ θ)
    {s : Finset ι} (hs : s ⊆ I) (x : Spatial n) (t : ℝ) :
    ∑ a ∈ s, ‖dx (curriedWeight θ) a x t‖ ≤ C₀ / r :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ => norm_nonneg _) (hP.first x t)

/-- Item 3: the second-derivative bound `C₀ / r ^ 2` for the actual `dxx`, on any `s ⊆ I`.
The combined estimate `second` also controls the time derivatives, which are dropped. -/
theorem sum_norm_dxx_curriedWeight_le {I : Finset ι} {z : ι → Space n} {r C₀ : ℝ}
    {θ : ι → Coordinates n → ℝ} (hP : IsSmoothParabolicPartition n I z r C₀ θ)
    {s : Finset ι} (hs : s ⊆ I) (x : Spatial n) (t : ℝ) :
    ∑ a ∈ s, ‖dxx (curriedWeight θ) a x t‖ ≤ C₀ / r ^ 2 := by
  calc ∑ a ∈ s, ‖dxx (curriedWeight θ) a x t‖
      ≤ ∑ a ∈ I, ‖dxx (curriedWeight θ) a x t‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (f := fun a => ‖dxx (curriedWeight θ) a x t‖) hs
          (fun a _ _ => norm_nonneg (dxx (curriedWeight θ) a x t))
    _ ≤ ∑ a ∈ I, (‖fderiv ℝ (fderiv ℝ fun y => θ a (y, t)) x‖ +
        |deriv (fun u => θ a (x, u)) t|) :=
        Finset.sum_le_sum fun a _ => le_add_of_nonneg_right (abs_nonneg _)
    _ ≤ C₀ / r ^ 2 := hP.second x t

/-- **The Hessian estimate for the weights of any smooth parabolic partition.** The
weight hypotheses of `hessian_norm_le` are discharged by the partition; the active-plane
height bound `he` and the tangent projection comparison `hc` remain hypotheses. -/
theorem hessian_norm_le_of_partition {I : Finset ι} {z : ι → Space n} {r C₀ : ℝ}
    {θ : ι → Coordinates n → ℝ} (hP : IsSmoothParabolicPartition n I z r C₀ θ)
    (hr : 0 < r) (hC : 0 ≤ C₀) (L : ι → AffineSpatialPlane n m) (x : Spatial n) (t H α : ℝ)
    (hH : 0 ≤ H) (hα : 0 ≤ α)
    (he : ∀ a ∈ I, Active (curriedWeight θ) a x t → ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ I, Active (curriedWeight θ) a x t →
      ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v w : Spatial n) (hv : v ∈ T) (hw : w ∈ T) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun u => sigma I L (curriedWeight θ) u t) y) x v w‖ ≤
      (10 * (1 + C₀) ^ 2 * (α + H) / r) * ‖v‖ * ‖w‖ :=
  hessian_norm_le I L (curriedWeight θ) x t C₀ H r α hr hC hH hα
    (contDiffAt_curriedWeight_of_partition hP I x t)
    (sum_norm_dx_curriedWeight_le hP subset_rfl x t)
    (sum_norm_dxx_curriedWeight_le hP subset_rfl x t) he T hc v w hv hw

/-- Item 1 for the actual weights. -/
theorem contDiffAt_parabolicWeight_spatial (r : ℝ) (I : Finset ι) (z : ι → Space n)
    (s : Finset ι) (x : Spatial n) (t : ℝ) :
    ∀ a ∈ s, ContDiffAt ℝ 2 (fun y => curriedWeight (parabolicWeight r I z) a y t) x :=
  fun a _ => contDiffAt_curriedWeight_spatial (contDiff_parabolicWeight r I z a) x t

/-- Item 2 for the actual weights, with `C₀ = partitionConstant n σ`. -/
theorem sum_norm_dx_parabolicWeight_le {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n)
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    {s : Finset ι} (hs : s ⊆ I) (x : Spatial n) (t : ℝ) :
    ∑ a ∈ s, ‖dx (curriedWeight (parabolicWeight r I z)) a x t‖ ≤ partitionConstant n σ / r :=
  sum_norm_dx_curriedWeight_le (isSmoothParabolicPartition_parabolicWeight hσ hr I z hdisj) hs x t

/-- Item 3 for the actual weights, with `C₀ = partitionConstant n σ`. -/
theorem sum_norm_dxx_parabolicWeight_le {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n)
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    {s : Finset ι} (hs : s ⊆ I) (x : Spatial n) (t : ℝ) :
    ∑ a ∈ s, ‖dxx (curriedWeight (parabolicWeight r I z)) a x t‖ ≤
      partitionConstant n σ / r ^ 2 :=
  sum_norm_dxx_curriedWeight_le (isSmoothParabolicPartition_parabolicWeight hσ hr I z hdisj) hs x t

/-- **Application.** The Hessian estimate `hessian_norm_le` for the actual smooth partition
weights `parabolicWeight` with constant `C₀ = partitionConstant n σ`. The weight
hypotheses of `hessian_norm_le` are all discharged; `he` and `hc` are the geometric
inputs, unchanged. -/
theorem hessian_norm_le_parabolicWeight {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (I : Finset ι)
    (z : ι → Space n)
    (hdisj : (I : Set ι).PairwiseDisjoint fun a => Metric.ball (z a) (σ * r / 3))
    (L : ι → AffineSpatialPlane n m) (x : Spatial n) (t H α : ℝ) (hH : 0 ≤ H) (hα : 0 ≤ α)
    (he : ∀ a ∈ I, Active (curriedWeight (parabolicWeight r I z)) a x t →
      ‖(L a).projection x - x‖ ≤ H * r)
    (T : Submodule ℝ (Spatial n))
    (hc : ∀ a ∈ I, Active (curriedWeight (parabolicWeight r I z)) a x t →
      ‖T.starProjection - (L a).linearProjection‖ ≤ α)
    (v w : Spatial n) (hv : v ∈ T) (hw : w ∈ T) :
    ‖fderiv ℝ (fun y => fderiv ℝ
        (fun u => sigma I L (curriedWeight (parabolicWeight r I z)) u t) y) x v w‖ ≤
      (10 * (1 + partitionConstant n σ) ^ 2 * (α + H) / r) * ‖v‖ * ‖w‖ :=
  hessian_norm_le_of_partition (isSmoothParabolicPartition_parabolicWeight hσ hr I z hdisj) hr
    (zero_le_one.trans (one_le_partitionConstant n hσ)) L x t H α hH hα he T hc v w hv hw

end ParabolicRectifiability
