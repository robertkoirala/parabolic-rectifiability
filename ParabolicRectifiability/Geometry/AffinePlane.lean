import ParabolicRectifiability.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Affine spatial planes with canonical anchors

Finite-dimensional spatial submodules are complete and closed, so their
orthogonal projections require no extra fields or hypotheses on plane data.
-/

noncomputable section

namespace ParabolicRectifiability

open Module

/-- An affine spatial plane, anchored at its point closest to the origin. -/
structure AffineSpatialPlane (n m : ℕ) where
  direction : Submodule ℝ (Spatial n)
  rank_eq : finrank ℝ direction = m
  anchor : Spatial n
  anchor_orthogonal : anchor ∈ directionᗮ

namespace AffineSpatialPlane

variable {n m : ℕ}

/-- The represented affine set. -/
def toSet (L : AffineSpatialPlane n m) : Set (Spatial n) :=
  {x | x - L.anchor ∈ L.direction}

/-- Linear orthogonal projection onto the direction. -/
def linearProjection (L : AffineSpatialPlane n m) : Spatial n →L[ℝ] Spatial n :=
  L.direction.starProjection

/-- The nearest-point affine projection. -/
def projection (L : AffineSpatialPlane n m) (x : Spatial n) : Spatial n :=
  L.anchor + L.linearProjection x

@[simp] theorem mem_toSet (L : AffineSpatialPlane n m) (x : Spatial n) :
    x ∈ L.toSet ↔ x - L.anchor ∈ L.direction := Iff.rfl

@[simp] theorem anchor_mem (L : AffineSpatialPlane n m) : L.anchor ∈ L.toSet := by
  simp [toSet]

theorem nonempty (L : AffineSpatialPlane n m) : L.toSet.Nonempty :=
  ⟨L.anchor, L.anchor_mem⟩

theorem isClosed (L : AffineSpatialPlane n m) : IsClosed L.toSet :=
  L.direction.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)

@[simp] theorem linearProjection_anchor (L : AffineSpatialPlane n m) :
    L.linearProjection L.anchor = 0 := by
  change (L.direction.orthogonalProjectionOnto L.anchor : Spatial n) = 0
  rw [L.direction.orthogonalProjectionOnto_apply_of_mem_orthogonal L.anchor_orthogonal]
  rfl

@[simp] theorem projection_mem (L : AffineSpatialPlane n m) (x : Spatial n) :
    L.projection x ∈ L.toSet := by
  simp [toSet, projection, linearProjection]

theorem residual (L : AffineSpatialPlane n m) (x : Spatial n) :
    x - L.projection x = x - L.direction.starProjection x - L.anchor := by
  dsimp [projection, linearProjection]
  abel

theorem residual_orthogonal (L : AffineSpatialPlane n m) (x : Spatial n) :
    x - L.projection x ∈ L.directionᗮ := by
  rw [L.residual]
  exact L.directionᗮ.sub_mem (L.direction.sub_starProjection_mem_orthogonal x)
    L.anchor_orthogonal

theorem nearest (L : AffineSpatialPlane n m) (x : Spatial n)
    {y : Spatial n} (hy : y ∈ L.toSet) :
    ‖x - L.projection x‖ ≤ ‖x - y‖ := by
  have h := Metric.infDist_le_dist_of_mem (s := (L.direction : Set (Spatial n)))
    (x := x - L.anchor) hy
  rw [← L.direction.dist_starProjection_eq_infDist, dist_eq_norm, dist_eq_norm] at h
  have hp : L.direction.starProjection (x - L.anchor) = L.direction.starProjection x := by
    have ha : L.direction.starProjection L.anchor = 0 := L.linearProjection_anchor
    simp only [map_sub, ha, sub_zero]
  rw [hp] at h
  have h₁ : x - L.anchor - L.direction.starProjection x = x - L.projection x := by
    dsimp [projection, linearProjection]
    abel
  have h₂ : x - L.anchor - (y - L.anchor) = x - y := by abel
  rwa [h₁, h₂] at h

/-- Canonical anchoring of an arbitrary translate `b + U`. -/
def ofTranslate (U : Submodule ℝ (Spatial n)) (hU : finrank ℝ U = m)
    (b : Spatial n) : AffineSpatialPlane n m where
  direction := U
  rank_eq := hU
  anchor := b - U.starProjection b
  anchor_orthogonal := U.sub_starProjection_mem_orthogonal b

@[simp] theorem ofTranslate_toSet (U : Submodule ℝ (Spatial n))
    (hU : finrank ℝ U = m) (b : Spatial n) :
    (ofTranslate U hU b).toSet = {x | x - b ∈ U} := by
  ext x
  change x - (b - U.starProjection b) ∈ U ↔ x - b ∈ U
  have hid : x - (b - U.starProjection b) = (x - b) + U.starProjection b := by abel
  rw [hid]
  exact U.add_mem_iff_left (U.starProjection_apply_mem b)

/-- Every point can serve as a translate of an available spatial direction. -/
theorem exists_mem_of_nonempty [Nonempty (AffineSpatialPlane n m)] (x : Spatial n) :
    ∃ L : AffineSpatialPlane n m, x ∈ L.toSet := by
  let L := Classical.choice (inferInstance : Nonempty (AffineSpatialPlane n m))
  exact ⟨ofTranslate L.direction L.rank_eq x, by simp⟩

theorem nonempty_iff : Nonempty (AffineSpatialPlane n m) ↔ m ≤ n := by
  constructor
  · rintro ⟨L⟩
    simpa [L.rank_eq] using L.direction.finrank_le
  · intro h
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank
      (R := ℝ) (M := Spatial n) (n := m) (by simpa using h)
    exact ⟨ofTranslate (Submodule.span ℝ (Set.range f))
      (by simpa using finrank_span_eq_card hf) 0⟩

/-- The rank-zero plane at any prescribed spatial point. -/
def singleton (x : Spatial n) : AffineSpatialPlane n 0 :=
  ofTranslate ⊥ (by simp) x

@[simp] theorem singleton_toSet (x : Spatial n) : (singleton x).toSet = {x} := by
  ext y
  simp [singleton, sub_eq_zero]

/-- The unique represented full-rank affine plane. -/
def full (n : ℕ) : AffineSpatialPlane n n :=
  ofTranslate ⊤ (by simp) 0

theorem direction_eq_top (L : AffineSpatialPlane n n) : L.direction = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by simpa using L.rank_eq)

@[simp] theorem fullRank_toSet (L : AffineSpatialPlane n n) : L.toSet = Set.univ := by
  ext x
  simp [toSet, L.direction_eq_top]

end AffineSpatialPlane
end ParabolicRectifiability
