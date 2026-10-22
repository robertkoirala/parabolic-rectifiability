import ParabolicRectifiability.Geometry.AdmissibleModels
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Exact model distances and fixed-model convexity

The cost is defined from the actual parabolic `infEDist`. The affine spatial
projection, with the prescribed time (horizontal) or unchanged time (vertical),
realizes that infimum. Convexity uses only ordinary space-time coordinates.
-/

noncomputable section
namespace ParabolicRectifiability

open scoped ENNReal

/-- Squared distance to the represented set in the parabolic metric. -/
def modelCost {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n) : ℝ≥0∞ :=
  (Metric.infEDist z (modelSet L)) ^ 2

private theorem max_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (max a b) ^ 2 = max (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith : a ^ 2 ≤ b ^ 2)]
  · rw [max_eq_left h, max_eq_left (by nlinarith : b ^ 2 ≤ a ^ 2)]

namespace AffineSpatialPlane
variable {n m : ℕ}

/-- Spatial squared residual on ordinary space-time coordinates. -/
def spatialCost (L : AffineSpatialPlane n m) (y : Coordinates n) : ℝ :=
  ‖y.1 - L.direction.starProjection y.1 - L.anchor‖ ^ 2

theorem spatialCost_nonneg (L : AffineSpatialPlane n m) (y : Coordinates n) :
    0 ≤ L.spatialCost y := sq_nonneg _

/-- Squared norm of the affine residual is convex, including rank zero. -/
theorem convexOn_spatialCost (L : AffineSpatialPlane n m) :
    ConvexOn ℝ Set.univ L.spatialCost := by
  let f : Coordinates n →ᵃ[ℝ] Spatial n :=
    (LinearMap.fst ℝ (Spatial n) ℝ -
      L.linearProjection.toLinearMap.comp (LinearMap.fst ℝ (Spatial n) ℝ)).toAffineMap -
        AffineMap.const ℝ (Coordinates n) L.anchor
  have h := ((convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : Spatial n → ℝ)).pow
    (fun _ _ => norm_nonneg _) 2).comp_affineMap f
  simpa [f, spatialCost, AffineSpatialPlane.linearProjection, Function.comp_def] using! h

end AffineSpatialPlane

namespace HorizontalModel
variable {n k : ℕ}

/-- Real nonnegative squared cost, proved below to equal the geometric cost. -/
def realCost (L : HorizontalModel n k) (z : Space n) : ℝ :=
  max (L.spatial.spatialCost (coordinatesHomeomorph n z)) |z.2.val - L.time|

theorem realCost_nonneg (L : HorizontalModel n k) (z : Space n) : 0 ≤ L.realCost z :=
  le_trans (L.spatial.spatialCost_nonneg _) (le_max_left _ _)

theorem nearest (L : HorizontalModel n k) (z : Space n) {w : Space n}
    (hw : w ∈ L.toSet) : dist z (L.projection z) ≤ dist z w := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases w with ⟨y, ⟨s⟩⟩
  change y ∈ L.spatial.toSet ∧ s = L.time at hw
  change dist (point x t) (point (L.spatial.projection x) L.time) ≤
    dist (point x t) (point y s)
  rw [dist_point, dist_point, hw.2]
  exact max_le_max (L.spatial.nearest x hw.1) le_rfl

/-- The explicit projection realizes the actual extended metric infimum. -/
theorem infEDist_eq_projection (L : HorizontalModel n k) (z : Space n) :
    Metric.infEDist z L.toSet = edist z (L.projection z) := by
  apply le_antisymm (Metric.infEDist_le_edist_of_mem (L.projection_mem z))
  apply Metric.le_infEDist.mpr
  intro w hw
  rw [edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal (L.nearest z hw)

theorem dist_projection_sq (L : HorizontalModel n k) (x : Spatial n) (t : ℝ) :
    dist (point x t) (L.projection (point x t)) ^ 2 =
      max (‖x - L.spatial.direction.starProjection x - L.spatial.anchor‖ ^ 2)
        |t - L.time| := by
  change dist (point x t) (point (L.spatial.projection x) L.time) ^ 2 = _
  rw [dist_point, L.spatial.residual, max_sq_of_nonneg (norm_nonneg _) (Real.sqrt_nonneg _),
    Real.sq_sqrt (abs_nonneg _)]

/-- Exact formula for squared distance to every horizontal model. -/
theorem modelCost_point (L : HorizontalModel n k) (x : Spatial n) (t : ℝ) :
    modelCost (T := .horizontal) L (point x t) =
      ENNReal.ofReal (max (‖x - L.spatial.direction.starProjection x - L.spatial.anchor‖ ^ 2)
        |t - L.time|) := by
  change (Metric.infEDist (point x t) L.toSet) ^ 2 = _
  rw [L.infEDist_eq_projection, edist_dist,
    ← ENNReal.ofReal_pow dist_nonneg, L.dist_projection_sq]

theorem modelCost_eq_ofReal (L : HorizontalModel n k) (z : Space n) :
    modelCost (T := .horizontal) L z = ENNReal.ofReal (L.realCost z) := by
  rcases z with ⟨x, ⟨t⟩⟩
  exact L.modelCost_point x t

/-- Fixed-model convexity after the ordinary coordinate inverse. -/
theorem convexOn_realCost (L : HorizontalModel n k) :
    ConvexOn ℝ Set.univ (fun y : Coordinates n =>
      L.realCost ((coordinatesHomeomorph n).symm y)) := by
  let f : Coordinates n →ᵃ[ℝ] ℝ :=
    (AffineMap.snd : Coordinates n →ᵃ[ℝ] ℝ) - AffineMap.const ℝ (Coordinates n) L.time
  have ht : ConvexOn ℝ Set.univ (fun y : Coordinates n => |y.2 - L.time|) := by
    simpa [f, Function.comp_def, Real.norm_eq_abs] using!
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ)).comp_affineMap f
  exact L.spatial.convexOn_spatialCost.sup ht

end HorizontalModel

namespace VerticalModel
variable {n k : ℕ}

/-- Real nonnegative squared cost, proved below to equal the geometric cost. -/
def realCost (L : VerticalModel n k) (z : Space n) : ℝ :=
  L.spatial.spatialCost (coordinatesHomeomorph n z)

theorem realCost_nonneg (L : VerticalModel n k) (z : Space n) : 0 ≤ L.realCost z :=
  L.spatial.spatialCost_nonneg _

theorem nearest (L : VerticalModel n k) (z : Space n) {w : Space n}
    (hw : w ∈ L.toSet) : dist z (L.projection z) ≤ dist z w := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases w with ⟨y, ⟨s⟩⟩
  change y ∈ L.spatial.toSet at hw
  change dist (point x t) (point (L.spatial.projection x) t) ≤
    dist (point x t) (point y s)
  rw [dist_point, dist_point]
  simp only [sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)]
  exact (L.spatial.nearest x hw).trans (le_max_left _ _)

theorem infEDist_eq_projection (L : VerticalModel n k) (z : Space n) :
    Metric.infEDist z L.toSet = edist z (L.projection z) := by
  apply le_antisymm (Metric.infEDist_le_edist_of_mem (L.projection_mem z))
  apply Metric.le_infEDist.mpr
  intro w hw
  rw [edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal (L.nearest z hw)

theorem dist_projection_sq (L : VerticalModel n k) (x : Spatial n) (t : ℝ) :
    dist (point x t) (L.projection (point x t)) ^ 2 =
      ‖x - L.spatial.direction.starProjection x - L.spatial.anchor‖ ^ 2 := by
  change dist (point x t) (point (L.spatial.projection x) t) ^ 2 = _
  rw [dist_point, L.spatial.residual]
  simp only [sub_self, abs_zero, Real.sqrt_zero, max_eq_left (norm_nonneg _)]

/-- Exact formula for squared distance to every vertical model. -/
theorem modelCost_point (L : VerticalModel n k) (x : Spatial n) (t : ℝ) :
    modelCost (T := .vertical) L (point x t) =
      ENNReal.ofReal (‖x - L.spatial.direction.starProjection x - L.spatial.anchor‖ ^ 2) := by
  change (Metric.infEDist (point x t) L.toSet) ^ 2 = _
  rw [L.infEDist_eq_projection, edist_dist,
    ← ENNReal.ofReal_pow dist_nonneg, L.dist_projection_sq]

theorem modelCost_eq_ofReal (L : VerticalModel n k) (z : Space n) :
    modelCost (T := .vertical) L z = ENNReal.ofReal (L.realCost z) := by
  rcases z with ⟨x, ⟨t⟩⟩
  exact L.modelCost_point x t

/-- Fixed-model convexity after the ordinary coordinate inverse. -/
theorem convexOn_realCost (L : VerticalModel n k) :
    ConvexOn ℝ Set.univ (fun y : Coordinates n =>
      L.realCost ((coordinatesHomeomorph n).symm y)) :=
  L.spatial.convexOn_spatialCost

end VerticalModel

/-- Real squared cost, uniformly across the three family choices. -/
def modelRealCost {n k : ℕ} {T : FamilyKind} : Models n k T → Space n → ℝ :=
  match T with
  | .horizontal => HorizontalModel.realCost
  | .vertical => VerticalModel.realCost
  | .mixed => fun L => match L with
    | .inl L => L.realCost
    | .inr L => L.realCost

theorem modelRealCost_nonneg {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n) :
    0 ≤ modelRealCost L z := by
  cases T with
  | horizontal => exact L.realCost_nonneg z
  | vertical => exact L.realCost_nonneg z
  | mixed => cases L with
    | inl L => exact L.realCost_nonneg z
    | inr L => exact L.realCost_nonneg z

theorem modelCost_eq_ofReal {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n) :
    modelCost L z = ENNReal.ofReal (modelRealCost L z) := by
  cases T with
  | horizontal => exact L.modelCost_eq_ofReal z
  | vertical => exact L.modelCost_eq_ofReal z
  | mixed => cases L with
    | inl L => exact L.modelCost_eq_ofReal z
    | inr L => exact L.modelCost_eq_ofReal z

/-- Conversion to real is justified by the exact finite squared-cost formula. -/
theorem modelCost_toReal {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n) :
    (modelCost L z).toReal = modelRealCost L z := by
  rw [modelCost_eq_ofReal, ENNReal.toReal_ofReal (modelRealCost_nonneg L z)]

theorem modelCost_ne_top {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n) :
    modelCost L z ≠ ⊤ := by
  rw [modelCost_eq_ofReal]
  exact ENNReal.ofReal_ne_top

theorem modelCost_lt_top {n k : ℕ} {T : FamilyKind} (L : Models n k T) (z : Space n) :
    modelCost L z < ⊤ := (modelCost_ne_top L z).lt_top

theorem convexOn_modelRealCost {n k : ℕ} {T : FamilyKind} (L : Models n k T) :
    ConvexOn ℝ Set.univ (fun y : Coordinates n =>
      modelRealCost L ((coordinatesHomeomorph n).symm y)) := by
  cases T with
  | horizontal => exact L.convexOn_realCost
  | vertical => exact L.convexOn_realCost
  | mixed => cases L with
    | inl L => exact L.convexOn_realCost
    | inr L => exact L.convexOn_realCost

/-- Convexity of the actual finite geometric squared cost in ordinary coordinates. -/
theorem convexOn_modelCost_toReal {n k : ℕ} {T : FamilyKind} (L : Models n k T) :
    ConvexOn ℝ Set.univ (fun y : Coordinates n =>
      (modelCost L ((coordinatesHomeomorph n).symm y)).toReal) := by
  simp only [modelCost_toReal]
  exact convexOn_modelRealCost L

@[simp] theorem ambient_modelCost {n : ℕ} (L : AdmissibleModel n (n + 2)) (z : Space n) :
    modelCost (T := .mixed) L z = 0 := by
  change (Metric.infEDist z L.toSet) ^ 2 = 0
  rw [L.ambient_toSet, Metric.infEDist_zero_of_mem (Set.mem_univ z)]
  norm_num

end ParabolicRectifiability
