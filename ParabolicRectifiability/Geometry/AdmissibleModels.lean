import ParabolicRectifiability.Geometry.AffinePlane
import ParabolicRectifiability.Metric.Space

/-!
# Horizontal, vertical and mixed affine models

Horizontal models are affine spatial `k`-planes at one fixed time, available
exactly when `1 ≤ k ≤ n`. Vertical models are affine spatial planes of rank
`k - 2` times the whole time axis, available exactly when `2 ≤ k ≤ n + 2`.
The explicit rank equation prevents truncated natural subtraction from
creating a vertical model at `k = 1`.

`Models n k T` selects a single family or their tagged union. The `toSet`
and `modelSet` maps give the represented subsets; their fitting costs are
`modelCost`. At `k = n + 2` every admissible model represents
the whole space. Rank-zero vertical models at `k = 2` remain included.
-/

noncomputable section

namespace ParabolicRectifiability

/-- An affine spatial `k`-plane at the recorded fixed time, with `k ≥ 1`.
The affine-plane rank condition also forces `k ≤ n`. -/
structure HorizontalModel (n k : ℕ) where
  positive : 1 ≤ k
  spatial : AffineSpatialPlane n k
  time : ℝ

/-- An affine spatial plane times all time, with parabolic dimension `k`.
Its spatial rank is recorded with `spatialRank + 2 = k` and the guard `2 ≤ k`. -/
structure VerticalModel (n k : ℕ) where
  spatialRank : ℕ
  two_le : 2 ≤ k
  rank_eq : spatialRank + 2 = k
  spatial : AffineSpatialPlane n spatialRank

/-- Tagged union of horizontal and vertical models of the same parabolic dimension. -/
abbrev AdmissibleModel (n k : ℕ) := HorizontalModel n k ⊕ VerticalModel n k

/-- Choice of horizontal, vertical or mixed planes in a fitting problem. -/
inductive FamilyKind where
  | horizontal | vertical | mixed
  deriving DecidableEq

/-- The actual type of fitting models for the selected family; unavailable
dimensions give an empty type rather than a fictitious zero-rank model. -/
def Models (n k : ℕ) : FamilyKind → Type
  | .horizontal => HorizontalModel n k
  | .vertical => VerticalModel n k
  | .mixed => AdmissibleModel n k

namespace HorizontalModel
variable {n k : ℕ}

def toSet (L : HorizontalModel n k) : Set (Space n) :=
  {z | z.1 ∈ L.spatial.toSet ∧ z.2.val = L.time}

@[simp] theorem mem_toSet_point (L : HorizontalModel n k) (x : Spatial n) (t : ℝ) :
    point x t ∈ L.toSet ↔ x ∈ L.spatial.toSet ∧ t = L.time := Iff.rfl

def projection (L : HorizontalModel n k) (z : Space n) : Space n :=
  point (L.spatial.projection z.1) L.time

@[simp] theorem projection_mem (L : HorizontalModel n k) (z : Space n) :
    L.projection z ∈ L.toSet :=
  ⟨L.spatial.projection_mem z.1, rfl⟩

theorem nonempty (L : HorizontalModel n k) : L.toSet.Nonempty :=
  ⟨L.projection (point 0 0), L.projection_mem _⟩

theorem isClosed (L : HorizontalModel n k) : IsClosed L.toSet :=
  (L.spatial.isClosed.preimage continuous_fst).inter
    (isClosed_eq continuous_time continuous_const)

theorem nonempty_iff : Nonempty (HorizontalModel n k) ↔ 1 ≤ k ∧ k ≤ n := by
  constructor
  · rintro ⟨L⟩
    exact ⟨L.positive, AffineSpatialPlane.nonempty_iff.mp ⟨L.spatial⟩⟩
  · rintro ⟨hk, hn⟩
    obtain ⟨L⟩ := AffineSpatialPlane.nonempty_iff.mpr hn
    exact ⟨⟨hk, L, 0⟩⟩

theorem exists_mem_of_nonempty (h : Nonempty (HorizontalModel n k)) (z : Space n) :
    ∃ L : HorizontalModel n k, z ∈ L.toSet := by
  obtain ⟨L⟩ := h
  let L' := AffineSpatialPlane.ofTranslate L.spatial.direction L.spatial.rank_eq z.1
  exact ⟨⟨L.positive, L', z.2.val⟩, by simp [toSet, L']⟩

theorem isEmpty_of_not_available (h : ¬ (1 ≤ k ∧ k ≤ n)) :
    IsEmpty (HorizontalModel n k) :=
  ⟨fun L => h (nonempty_iff.mp ⟨L⟩)⟩

instance ambient_isEmpty : IsEmpty (HorizontalModel n (n + 2)) :=
  isEmpty_of_not_available (by omega)

end HorizontalModel

namespace VerticalModel
variable {n k : ℕ}

def toSet (L : VerticalModel n k) : Set (Space n) :=
  {z | z.1 ∈ L.spatial.toSet}

@[simp] theorem mem_toSet_point (L : VerticalModel n k) (x : Spatial n) (t : ℝ) :
    point x t ∈ L.toSet ↔ x ∈ L.spatial.toSet := Iff.rfl

def projection (L : VerticalModel n k) (z : Space n) : Space n :=
  point (L.spatial.projection z.1) z.2.val

@[simp] theorem projection_mem (L : VerticalModel n k) (z : Space n) :
    L.projection z ∈ L.toSet := L.spatial.projection_mem z.1

theorem nonempty (L : VerticalModel n k) : L.toSet.Nonempty :=
  ⟨L.projection (point 0 0), L.projection_mem _⟩

theorem isClosed (L : VerticalModel n k) : IsClosed L.toSet :=
  L.spatial.isClosed.preimage continuous_fst

theorem nonempty_iff : Nonempty (VerticalModel n k) ↔ 2 ≤ k ∧ k ≤ n + 2 := by
  constructor
  · rintro ⟨L⟩
    have hr := AffineSpatialPlane.nonempty_iff.mp (Nonempty.intro L.spatial)
    have he := L.rank_eq
    exact ⟨L.two_le, by omega⟩
  · rintro ⟨hk, hn⟩
    obtain ⟨L⟩ := AffineSpatialPlane.nonempty_iff.mpr (show k - 2 ≤ n by omega)
    exact ⟨⟨k - 2, hk, by omega, L⟩⟩

theorem exists_mem_of_nonempty (h : Nonempty (VerticalModel n k)) (z : Space n) :
    ∃ L : VerticalModel n k, z ∈ L.toSet := by
  obtain ⟨L⟩ := h
  let L' := AffineSpatialPlane.ofTranslate L.spatial.direction L.spatial.rank_eq z.1
  exact ⟨⟨L.spatialRank, L.two_le, L.rank_eq, L'⟩, by simp [toSet, L']⟩

theorem isEmpty_of_not_available (h : ¬ (2 ≤ k ∧ k ≤ n + 2)) :
    IsEmpty (VerticalModel n k) :=
  ⟨fun L => h (nonempty_iff.mp ⟨L⟩)⟩

instance one_isEmpty : IsEmpty (VerticalModel n 1) :=
  isEmpty_of_not_available (by omega)

@[simp] theorem ambient_toSet (L : VerticalModel n (n + 2)) : L.toSet = Set.univ := by
  have hr : L.spatialRank = n := by have := L.rank_eq; omega
  have htop : L.spatial.direction = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simp [L.spatial.rank_eq, hr])
  ext z
  simp [toSet, AffineSpatialPlane.toSet, htop]

end VerticalModel

namespace AdmissibleModel
variable {n k : ℕ}

def toSet : AdmissibleModel n k → Set (Space n)
  | .inl L => L.toSet
  | .inr L => L.toSet

theorem nonempty (L : AdmissibleModel n k) : L.toSet.Nonempty := by
  cases L with
  | inl L => exact L.nonempty
  | inr L => exact L.nonempty

theorem isClosed (L : AdmissibleModel n k) : IsClosed L.toSet := by
  cases L with
  | inl L => exact L.isClosed
  | inr L => exact L.isClosed

theorem nonempty_iff : Nonempty (AdmissibleModel n k) ↔
    (1 ≤ k ∧ k ≤ n) ∨ (2 ≤ k ∧ k ≤ n + 2) := by
  simp only [AdmissibleModel, nonempty_sum, HorizontalModel.nonempty_iff, VerticalModel.nonempty_iff]

theorem nonempty_of_range (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) :
    Nonempty (AdmissibleModel n k) :=
  nonempty_iff.mpr (by omega)

theorem exists_mem_of_nonempty (h : Nonempty (AdmissibleModel n k)) (z : Space n) :
    ∃ L : AdmissibleModel n k, z ∈ L.toSet := by
  obtain ⟨L⟩ := h
  cases L with
  | inl L =>
    obtain ⟨Q, hQ⟩ := HorizontalModel.exists_mem_of_nonempty ⟨L⟩ z
    exact ⟨.inl Q, hQ⟩
  | inr L =>
    obtain ⟨Q, hQ⟩ := VerticalModel.exists_mem_of_nonempty ⟨L⟩ z
    exact ⟨.inr Q, hQ⟩

@[simp] theorem ambient_toSet (L : AdmissibleModel n (n + 2)) : L.toSet = Set.univ := by
  cases L with
  | inl L => exact isEmptyElim L
  | inr L => exact L.ambient_toSet

end AdmissibleModel

/-- The represented set, uniformly across the three family choices. -/
def modelSet {n k : ℕ} {T : FamilyKind} : Models n k T → Set (Space n) :=
  match T with
  | .horizontal => HorizontalModel.toSet
  | .vertical => VerticalModel.toSet
  | .mixed => AdmissibleModel.toSet

theorem modelSet_nonempty {n k : ℕ} {T : FamilyKind} (L : Models n k T) :
    (modelSet L).Nonempty := by
  cases T with
  | horizontal => exact L.nonempty
  | vertical => exact L.nonempty
  | mixed => exact L.nonempty

theorem modelSet_isClosed {n k : ℕ} {T : FamilyKind} (L : Models n k T) :
    IsClosed (modelSet L) := by
  cases T with
  | horizontal => exact L.isClosed
  | vertical => exact L.isClosed
  | mixed => exact L.isClosed

theorem exists_model_mem {n k : ℕ} {T : FamilyKind}
    (h : Nonempty (Models n k T)) (z : Space n) :
    ∃ L : Models n k T, z ∈ modelSet L := by
  cases T with
  | horizontal => exact HorizontalModel.exists_mem_of_nonempty h z
  | vertical => exact VerticalModel.exists_mem_of_nonempty h z
  | mixed => exact AdmissibleModel.exists_mem_of_nonempty h z

end ParabolicRectifiability
