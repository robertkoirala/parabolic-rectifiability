import ParabolicRectifiability.Metric.Similarity
import ParabolicRectifiability.Geometry.ModelDistance

/-! # Similarities of canonical affine models -/
noncomputable section
open Set
open scoped ENNReal
namespace ParabolicRectifiability

namespace AffineSpatialPlane
variable {n m : ℕ}

theorem eq_of_direction_anchor {L K : AffineSpatialPlane n m}
    (hd : L.direction = K.direction) (hb : L.anchor = K.anchor) : L = K := by
  cases L
  cases K
  cases hd
  cases hb
  rfl

/-- Canonical representative of the image under `x ↦ (x-q)/a`. -/
def similarity (q : Spatial n) (a : ℝ) (L : AffineSpatialPlane n m) :
    AffineSpatialPlane n m :=
  ofTranslate L.direction L.rank_eq (a⁻¹ • (L.anchor - q))

def inverseSimilarity (q : Spatial n) (a : ℝ) (L : AffineSpatialPlane n m) :
    AffineSpatialPlane n m := ofTranslate L.direction L.rank_eq (a • L.anchor + q)

@[simp] theorem similarity_direction (q : Spatial n) (a : ℝ) (L : AffineSpatialPlane n m) :
    (similarity q a L).direction = L.direction := rfl

@[simp] theorem inverseSimilarity_direction (q : Spatial n) (a : ℝ) (L : AffineSpatialPlane n m) :
    (inverseSimilarity q a L).direction = L.direction := rfl

theorem similarity_anchor (q : Spatial n) (a : ℝ) (L : AffineSpatialPlane n m) :
    (similarity q a L).anchor = a⁻¹ • (L.anchor - (q - L.direction.starProjection q)) := by
  have hp : L.direction.starProjection L.anchor = 0 := L.linearProjection_anchor
  simp only [similarity, ofTranslate, map_smul, map_sub, hp]
  module

theorem inverseSimilarity_anchor (q : Spatial n) (a : ℝ) (L : AffineSpatialPlane n m) :
    (inverseSimilarity q a L).anchor = a • L.anchor + (q - L.direction.starProjection q) := by
  have hp : L.direction.starProjection L.anchor = 0 := L.linearProjection_anchor
  simp only [inverseSimilarity, ofTranslate, map_add, map_smul, hp]
  module

/-- A bijection on the existing records, including rank zero and full rank. -/
def similarityEquiv (q : Spatial n) (a : ℝ) (ha : 0 < a) :
    AffineSpatialPlane n m ≃ AffineSpatialPlane n m where
  toFun := similarity q a
  invFun := inverseSimilarity q a
  left_inv L := by
    apply eq_of_direction_anchor
    · rfl
    · rw [inverseSimilarity_anchor, similarity_anchor, similarity_direction]
      simp [smul_smul, ha.ne']
  right_inv L := by
    apply eq_of_direction_anchor
    · rfl
    · rw [similarity_anchor, inverseSimilarity_anchor, inverseSimilarity_direction]
      simp [smul_smul, ha.ne']

theorem mem_similarity (q : Spatial n) (a : ℝ) (ha : 0 < a)
    (L : AffineSpatialPlane n m) (x : Spatial n) :
    a⁻¹ • (x - q) ∈ (similarityEquiv q a ha L).toSet ↔ x ∈ L.toSet := by
  change a⁻¹ • (x - q) ∈ (ofTranslate L.direction L.rank_eq (a⁻¹ • (L.anchor - q))).toSet ↔ _
  rw [ofTranslate_toSet]
  change a⁻¹ • (x - q) - a⁻¹ • (L.anchor - q) ∈ L.direction ↔ x - L.anchor ∈ L.direction
  rw [← smul_sub, sub_sub_sub_cancel_right]
  exact L.direction.smul_mem_iff (inv_ne_zero ha.ne')

end AffineSpatialPlane

namespace HorizontalModel
variable {n k : ℕ}

theorem eq_of_spatial_time {L K : HorizontalModel n k}
    (hs : L.spatial = K.spatial) (ht : L.time = K.time) : L = K := by
  cases L
  cases K
  cases hs
  cases ht
  rfl

def similarityEquiv (q : Space n) (a : ℝ) (ha : 0 < a) : HorizontalModel n k ≃ HorizontalModel n k where
  toFun L := ⟨L.positive, AffineSpatialPlane.similarityEquiv q.1 a ha L.spatial,
    a⁻¹ ^ 2 * (L.time - q.2.val)⟩
  invFun L := ⟨L.positive, (AffineSpatialPlane.similarityEquiv q.1 a ha).symm L.spatial,
    a ^ 2 * L.time + q.2.val⟩
  left_inv L := by
    apply eq_of_spatial_time (Equiv.symm_apply_apply _ _)
    dsimp
    field_simp [ha.ne']; ring
  right_inv L := by
    apply eq_of_spatial_time (Equiv.apply_symm_apply _ _)
    dsimp
    field_simp [ha.ne']; ring

theorem mem_similarity (q : Space n) (a : ℝ) (ha : 0 < a) (L : HorizontalModel n k)
    (z : Space n) : similarity q a ha z ∈ (similarityEquiv q a ha L).toSet ↔ z ∈ L.toSet := by
  change (a⁻¹ • (z.1 - q.1) ∈ (AffineSpatialPlane.similarityEquiv q.1 a ha L.spatial).toSet ∧
    a⁻¹ ^ 2 * (z.2.val - q.2.val) = a⁻¹ ^ 2 * (L.time - q.2.val)) ↔ _
  rw [AffineSpatialPlane.mem_similarity]
  simp only [mul_right_inj' (pow_ne_zero 2 (inv_ne_zero ha.ne')), sub_left_inj]
  rfl

end HorizontalModel

namespace VerticalModel
variable {n k : ℕ}

def similarityEquiv (q : Space n) (a : ℝ) (ha : 0 < a) : VerticalModel n k ≃ VerticalModel n k where
  toFun L := ⟨L.spatialRank, L.two_le, L.rank_eq, AffineSpatialPlane.similarityEquiv q.1 a ha L.spatial⟩
  invFun L := ⟨L.spatialRank, L.two_le, L.rank_eq,
    (AffineSpatialPlane.similarityEquiv q.1 a ha).symm L.spatial⟩
  left_inv L := by
    cases L
    simp only [Equiv.symm_apply_apply]
  right_inv L := by
    cases L
    simp only [Equiv.apply_symm_apply]

theorem mem_similarity (q : Space n) (a : ℝ) (ha : 0 < a) (L : VerticalModel n k)
    (z : Space n) : similarity q a ha z ∈ (similarityEquiv q a ha L).toSet ↔ z ∈ L.toSet :=
  AffineSpatialPlane.mem_similarity q.1 a ha L.spatial z.1

end VerticalModel

/-- Each family is transported within its own type; the mixed family retains its sum tag. -/
def modelSimilarity {n k : ℕ} (T : FamilyKind) (q : Space n) (a : ℝ) (ha : 0 < a) :
    Models n k T ≃ Models n k T :=
  match T with
  | .horizontal => HorizontalModel.similarityEquiv q a ha
  | .vertical => VerticalModel.similarityEquiv q a ha
  | .mixed => Equiv.sumCongr (HorizontalModel.similarityEquiv q a ha) (VerticalModel.similarityEquiv q a ha)

theorem mem_modelSimilarity {n k : ℕ} {T : FamilyKind} (q : Space n) (a : ℝ) (ha : 0 < a)
    (L : Models n k T) (z : Space n) :
    similarity q a ha z ∈ modelSet (modelSimilarity T q a ha L) ↔ z ∈ modelSet L := by
  cases T with
  | horizontal => exact HorizontalModel.mem_similarity q a ha L z
  | vertical => exact VerticalModel.mem_similarity q a ha L z
  | mixed =>
    cases L with
    | inl L => exact HorizontalModel.mem_similarity q a ha L z
    | inr L => exact VerticalModel.mem_similarity q a ha L z

theorem modelSet_modelSimilarity {n k : ℕ} {T : FamilyKind} (q : Space n) (a : ℝ) (ha : 0 < a)
    (L : Models n k T) : modelSet (modelSimilarity T q a ha L) = similarity q a ha '' modelSet L := by
  ext w
  obtain ⟨z, rfl⟩ := (similarity q a ha).surjective w
  rw [mem_modelSimilarity, (similarity q a ha).injective.mem_set_image]

/-- Cost scaling follows from the image of the represented set and the actual metric infimum. -/
theorem modelCost_modelSimilarity {n k : ℕ} {T : FamilyKind} (q : Space n) (a : ℝ) (ha : 0 < a)
    (L : Models n k T) (z : Space n) :
    modelCost (modelSimilarity T q a ha L) (similarity q a ha z) =
      (ENNReal.ofReal a)⁻¹ ^ 2 * modelCost L z := by
  have h0 : (ENNReal.ofReal a)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have ht : (ENNReal.ofReal a)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ha).ne'
  simp only [modelCost, modelSet_modelSimilarity, Metric.infEDist, iInf_image, edist_similarity,
    ← ENNReal.mul_iInf_of_ne h0 ht, mul_pow]

end ParabolicRectifiability
