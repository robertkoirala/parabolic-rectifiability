import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Plateau.Whitney
import ParabolicRectifiability.QuantitativeCharacterization.Statements.WhitneyPlateau

/-! # The Whitney plateau completion

Proves `b2_whitney_plateau_completion_proof : WhitneyPlateauCompletionStatement`.

Construction, on the standard dyadic grid (origin `0`, scale `1`):
* the Whitney cubes are the maximal qualifying cubes, indexed through a fixed
  injection `ℤ × ℤ^k → ℕ`;
* anchors `a_Q ∈ D` realize `dist(Q, D)` exactly (compactness of `Q` and `D`);
* faces: first-cube assignment `face i = Q_i \ ⋃_{j < i} Q_j`;
* plateau height: `T = τ(a_Q)` on the face of `Q`, and `T = τ` on `D`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- A fixed injection of the dyadic labels into `ℕ`. -/
def b2plat_enc (k : ℕ) : ℤ × (Fin k → ℤ) → ℕ :=
  (Countable.exists_injective_nat (ℤ × (Fin k → ℤ))).choose

theorem b2plat_enc_injective (k : ℕ) : Function.Injective (b2plat_enc k) :=
  (Countable.exists_injective_nat (ℤ × (Fin k → ℤ))).choose_spec

/-- The left inverse of `b2plat_enc`. -/
def b2plat_dec (k : ℕ) (i : ℕ) : ℤ × (Fin k → ℤ) :=
  Function.invFun (b2plat_enc k) i

theorem b2plat_dec_enc {k : ℕ} (p : ℤ × (Fin k → ℤ)) : b2plat_dec k (b2plat_enc k p) = p :=
  Function.leftInverse_invFun (b2plat_enc_injective k) p

variable {k : ℕ}

/-- The index set: codes of the maximal qualifying cubes. -/
def b2plat_index (D : Set (Spatial k)) : Set ℕ :=
  b2plat_enc k '' {p | b2plat_maximal D p}

theorem b2plat_enc_dec {D : Set (Spatial k)} (i : b2plat_index D) :
    b2plat_enc k (b2plat_dec k i) = i := by
  obtain ⟨p, -, hp⟩ := i.2
  exact Function.invFun_eq ⟨p, hp⟩

theorem b2plat_dec_maximal {D : Set (Spatial k)} (i : b2plat_index D) :
    b2plat_maximal D (b2plat_dec k i) := by
  obtain ⟨p, hp, he⟩ := i.2
  rw [← he, b2plat_dec_enc]
  exact hp

theorem b2plat_index_eq {D : Set (Spatial k)} {i j : b2plat_index D}
    (h : b2plat_dec k i = b2plat_dec k j) : i = j := by
  apply Subtype.ext
  rw [← b2plat_enc_dec i, ← b2plat_enc_dec j, h]

/-- The Whitney cube with index `i`. -/
def b2plat_Q (D : Set (Spatial k)) (i : b2plat_index D) : Set (Spatial k) :=
  b2plat_cube (b2plat_dec k i).1 (b2plat_dec k i).2

theorem b2plat_Q_subset_compl {D : Set (Spatial k)} (hk : 1 ≤ k) (i : b2plat_index D) :
    b2plat_Q D i ⊆ Dᶜ :=
  b2plat_qual_subset_compl hk (b2plat_dec_maximal i).1

theorem b2plat_Q_interior_disjoint {D : Set (Spatial k)} (i j : b2plat_index D) (hij : i ≠ j) :
    Disjoint (interior (b2plat_Q D i)) (interior (b2plat_Q D j)) := by
  refine Set.disjoint_left.2 fun x hxi hxj => hij (b2plat_index_eq ?_)
  exact b2plat_eq_of_mem_interior (b2plat_dec_maximal i) (b2plat_dec_maximal j) hxi
    (interior_subset hxj)

theorem b2plat_Q_cover {D : Set (Spatial k)} (hk : 1 ≤ k) (hD : IsClosed D) (hDne : D.Nonempty) :
    (⋃ i, b2plat_Q D i) = Dᶜ := by
  apply Subset.antisymm
  · exact iUnion_subset fun i => b2plat_Q_subset_compl hk i
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := b2plat_exists_maximal hk hD hDne hx
    refine mem_iUnion.2 ⟨⟨b2plat_enc k p, p, hp, rfl⟩, ?_⟩
    show x ∈ b2plat_cube (b2plat_dec k (b2plat_enc k p)).1 (b2plat_dec k (b2plat_enc k p)).2
    rw [b2plat_dec_enc]
    exact hxp

/-! ### Anchors -/

theorem b2plat_exists_anchor {D Q : Set (Spatial k)} (hD : IsCompact D) (hDne : D.Nonempty)
    (hQ : IsCompact Q) (hQne : Q.Nonempty) :
    ∃ a ∈ D, ∃ x ∈ Q, dist x a = setDist Q D := by
  obtain ⟨x, hxQ, hmin⟩ := hQ.exists_isMinOn hQne (Metric.continuous_infDist_pt D).continuousOn
  obtain ⟨a, haD, ha⟩ := hD.exists_infDist_eq_dist hDne x
  refine ⟨a, haD, x, hxQ, ?_⟩
  rw [← ha]
  exact le_antisymm (b2plat_le_setDist hQne fun y hy => isMinOn_iff.1 hmin y hy)
    (b2plat_setDist_le hxQ)

open scoped Classical in
/-- A nearest anchor of `Q` in `D` (any point of `D` realizing `dist(Q, D)`). -/
def b2plat_anchor (D Q : Set (Spatial k)) : Spatial k :=
  if h : ∃ a ∈ D, ∃ x ∈ Q, dist x a = setDist Q D then h.choose else 0

theorem b2plat_anchor_spec {D Q : Set (Spatial k)} (hD : IsCompact D) (hDne : D.Nonempty)
    (hQ : IsCompact Q) (hQne : Q.Nonempty) :
    b2plat_anchor D Q ∈ D ∧ ∃ x ∈ Q, dist x (b2plat_anchor D Q) = setDist Q D := by
  have h := b2plat_exists_anchor hD hDne hQ hQne
  rw [b2plat_anchor, dite_eq_left h]
  exact h.choose_spec

theorem b2plat_Q_anchor_spec {D : Set (Spatial k)} (hD : IsCompact D) (hDne : D.Nonempty)
    (i : b2plat_index D) :
    b2plat_anchor D (b2plat_Q D i) ∈ D ∧
      ∃ x ∈ b2plat_Q D i, dist x (b2plat_anchor D (b2plat_Q D i)) = setDist (b2plat_Q D i) D :=
  b2plat_anchor_spec hD hDne (b2plat_isCompact _ _) (b2plat_cube_nonempty _ _)

/-! ### Faces -/

/-- First-cube face assignment: `face i = Q_i \ ⋃_{j < i} Q_j`. -/
def b2plat_face (D : Set (Spatial k)) (i : b2plat_index D) : Set (Spatial k) :=
  b2plat_Q D i \ ⋃ (j : b2plat_index D) (_ : (j : ℕ) < i), b2plat_Q D j

theorem b2plat_face_subset {D : Set (Spatial k)} (i : b2plat_index D) :
    b2plat_face D i ⊆ b2plat_Q D i :=
  sdiff_subset

theorem b2plat_face_measurable {D : Set (Spatial k)} (i : b2plat_index D) :
    MeasurableSet (b2plat_face D i) :=
  (b2plat_isClosed _ _).measurableSet.diff
    (MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => (b2plat_isClosed _ _).measurableSet)

theorem b2plat_interior_subset_face {D : Set (Spatial k)} (i : b2plat_index D) :
    interior (b2plat_Q D i) ⊆ b2plat_face D i := by
  intro x hx
  refine ⟨interior_subset hx, fun hmem => ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
  obtain ⟨hlt, hxj⟩ := mem_iUnion.1 hj
  have := b2plat_index_eq
    (b2plat_eq_of_mem_interior (b2plat_dec_maximal i) (b2plat_dec_maximal j) hx hxj)
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem b2plat_face_disjoint {D : Set (Spatial k)} (i j : b2plat_index D) (hij : i ≠ j) :
    Disjoint (b2plat_face D i) (b2plat_face D j) := by
  refine Set.disjoint_left.2 fun x hxi hxj => ?_
  have hne : (i : ℕ) ≠ j := fun h => hij (Subtype.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact hxj.2 (mem_iUnion₂.2 ⟨i, h, hxi.1⟩)
  · exact hxi.2 (mem_iUnion₂.2 ⟨j, h, hxj.1⟩)

theorem b2plat_faces_cover {D : Set (Spatial k)} (hk : 1 ≤ k) (hD : IsClosed D)
    (hDne : D.Nonempty) : (⋃ i, b2plat_face D i) = Dᶜ := by
  apply Subset.antisymm
  · exact iUnion_subset fun i => (b2plat_face_subset i).trans (b2plat_Q_subset_compl hk i)
  · intro x hx
    rw [← b2plat_Q_cover hk hD hDne] at hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
    let S : Set ℕ := {n | ∃ h : n ∈ b2plat_index D, x ∈ b2plat_Q D ⟨n, h⟩}
    have hS : S.Nonempty := ⟨i, i.2, hxi⟩
    obtain ⟨h0, hx0⟩ := Nat.sInf_mem hS
    refine mem_iUnion.2 ⟨⟨sInf S, h0⟩, hx0, fun hmem => ?_⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
    obtain ⟨hlt, hxj⟩ := mem_iUnion.1 hj
    exact Nat.notMem_of_lt_sInf hlt ⟨j.2, hxj⟩

/-! ### Plateau height -/

open scoped Classical in
/-- The plateau function: `τ(a_Q)` on the face of `Q`, and `τ` elsewhere (in particular on
`D`). -/
def b2plat_height (D : Set (Spatial k)) (τ : Spatial k → ℝ) (x : Spatial k) : ℝ :=
  if h : ∃ i, x ∈ b2plat_face D i then τ (b2plat_anchor D (b2plat_Q D h.choose)) else τ x

theorem b2plat_height_of_mem {D : Set (Spatial k)} (hk : 1 ≤ k) (τ : Spatial k → ℝ)
    {u : Spatial k} (hu : u ∈ D) : b2plat_height D τ u = τ u := by
  have h : ¬ ∃ i, u ∈ b2plat_face D i := by
    rintro ⟨i, hi⟩
    exact b2plat_Q_subset_compl hk i (b2plat_face_subset i hi) hu
  rw [b2plat_height, dite_eq_right h]

theorem b2plat_height_face {D : Set (Spatial k)} (τ : Spatial k → ℝ) {i : b2plat_index D}
    {x : Spatial k} (hx : x ∈ b2plat_face D i) :
    b2plat_height D τ x = τ (b2plat_anchor D (b2plat_Q D i)) := by
  have h : ∃ i, x ∈ b2plat_face D i := ⟨i, hx⟩
  rw [b2plat_height, dite_eq_left h]
  have hc : h.choose = i := by
    by_contra hne
    exact Set.disjoint_left.1 (b2plat_face_disjoint _ _ hne) h.choose_spec hx
  rw [hc]

/-! ### Assembly -/

/-- **Whitney plateau completion.** -/
theorem b2_whitney_plateau_completion_proof : WhitneyPlateauCompletionStatement := by
  intro n k hk hkn L F hF D hDne hDc τ hτ
  have hDcl : IsClosed D := hDc.isClosed
  refine ⟨
    { available := ⟨hk, hkn⟩
      spatialMap := F
      spatialMap_bilipschitz := hF
      domain := D
      domain_nonempty := hDne
      domain_compact := hDc
      height := b2plat_height D τ
      height_trace := fun u hu v hv => by
        rw [b2plat_height_of_mem hk τ hu, b2plat_height_of_mem hk τ hv]
        exact hτ u hu v hv
      gridOrigin := 0
      gridScale := 1
      gridScale_pos := one_pos
      cubeIndex := b2plat_index D
      cube := b2plat_Q D
      cubeLevel := fun i => (b2plat_dec k i).1
      cubeCorner := fun i => (b2plat_dec k i).2
      cube_eq := fun _ => rfl
      cube_interior_disjoint := b2plat_Q_interior_disjoint
      cubes_cover := b2plat_Q_cover hk hDcl hDne
      whitney_lower := fun i => (b2plat_dec_maximal i).1
      whitney_upper := fun i => b2plat_upper (b2plat_dec_maximal i)
      anchor := fun i => b2plat_anchor D (b2plat_Q D i)
      anchor_mem := fun i => (b2plat_Q_anchor_spec hDc hDne i).1
      anchor_nearest := fun i => (b2plat_Q_anchor_spec hDc hDne i).2
      face := b2plat_face D
      face_measurable := b2plat_face_measurable
      interior_subset_face := b2plat_interior_subset_face
      face_subset_cube := b2plat_face_subset
      face_disjoint := b2plat_face_disjoint
      faces_cover := b2plat_faces_cover hk hDcl hDne
      height_plateau := fun i x hx => by
        rw [b2plat_height_face τ hx,
          b2plat_height_of_mem hk τ (b2plat_Q_anchor_spec hDc hDne i).1] },
    rfl, rfl, fun u hu => b2plat_height_of_mem hk τ hu⟩

end ParabolicRectifiability.QuantitativeCharacterization
