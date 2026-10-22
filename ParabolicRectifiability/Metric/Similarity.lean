import ParabolicRectifiability.Metric.Measure

/-! # Translated parabolic similarities

Translation takes place in ordinary space-time coordinates. The scale part
uses the parabolic dilation `dilate`; snowflaked time is never treated as a
normed vector space.
-/
noncomputable section
open Set
open scoped ENNReal
namespace ParabolicRectifiability

/-- Subtract a space-time center through ordinary coordinates. -/
def translationHomeomorph {n : ℕ} (q : Space n) : Space n ≃ₜ Space n :=
  ((coordinatesHomeomorph n).trans
    ((Homeomorph.subRight q.1).prodCongr (Homeomorph.subRight q.2.val))).trans
      (coordinatesHomeomorph n).symm

@[simp] theorem translationHomeomorph_apply {n : ℕ} (q z : Space n) :
    translationHomeomorph q z = point (z.1 - q.1) (z.2.val - q.2.val) := rfl

@[simp] theorem translationHomeomorph_symm_apply {n : ℕ} (q z : Space n) :
    (translationHomeomorph q).symm z = point (z.1 + q.1) (z.2.val + q.2.val) := rfl

theorem dist_translationHomeomorph {n : ℕ} (q z w : Space n) :
    dist (translationHomeomorph q z) (translationHomeomorph q w) = dist z w := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases w with ⟨y, ⟨u⟩⟩
  change dist (point (x - q.1) (t - q.2.val)) (point (y - q.1) (u - q.2.val)) =
    dist (point x t) (point y u)
  simp only [dist_point, sub_sub_sub_cancel_right]

/-- `T(q,a)(x,t) = ((x-qₓ)/a,(t-qₜ)/a²)` for a positive real scale. -/
def similarity {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) : Space n ≃ₜ Space n :=
  (translationHomeomorph q).trans (dilationHomeomorph n a⁻¹ (inv_pos.mpr ha))

def similarityMeasurableEquiv {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) :
    Space n ≃ᵐ Space n := (similarity q a ha).toMeasurableEquiv

@[simp] theorem similarity_apply {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a)
    (z : Space n) :
    similarity q a ha z = point (a⁻¹ • (z.1 - q.1)) (a⁻¹ ^ 2 * (z.2.val - q.2.val)) := rfl

@[simp] theorem similarity_symm_apply {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a)
    (z : Space n) :
    (similarity q a ha).symm z = point (a • z.1 + q.1) (a ^ 2 * z.2.val + q.2.val) := by
  apply (similarity q a ha).injective
  rw [Homeomorph.apply_symm_apply, similarity_apply]
  rcases z with ⟨x, ⟨t⟩⟩
  change point x t = point (a⁻¹ • (a • x + q.1 - q.1))
    (a⁻¹ ^ 2 * (a ^ 2 * t + q.2.val - q.2.val))
  simp only [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  congr 1
  field_simp [ha.ne']

theorem dist_similarity {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) (z w : Space n) :
    dist (similarity q a ha z) (similarity q a ha w) = a⁻¹ * dist z w := by
  change dist (dilate a⁻¹ (translationHomeomorph q z))
    (dilate a⁻¹ (translationHomeomorph q w)) = _
  rw [dist_dilate _ (inv_pos.mpr ha).le, dist_translationHomeomorph]

theorem edist_similarity {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a) (z w : Space n) :
    edist (similarity q a ha z) (similarity q a ha w) =
      (ENNReal.ofReal a)⁻¹ * edist z w := by
  simp only [edist_dist, dist_similarity, ENNReal.ofReal_mul (inv_pos.mpr ha).le,
    ENNReal.ofReal_inv_of_pos ha]

theorem preimage_similarity_ball {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a)
    (z : Space n) (r : ℝ) :
    similarity q a ha ⁻¹' Metric.ball (similarity q a ha z) r = Metric.ball z (a * r) := by
  ext w
  simp only [mem_preimage, Metric.mem_ball, dist_similarity]
  rw [inv_mul_lt_iff₀ ha]

theorem image_similarity_ball {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a)
    (z : Space n) (r : ℝ) :
    similarity q a ha '' Metric.ball z r = Metric.ball (similarity q a ha z) (r / a) := by
  apply (similarity q a ha).surjective.preimage_injective
  rw [preimage_image_eq _ (similarity q a ha).injective, preimage_similarity_ball]
  congr 1
  field_simp

theorem image_similarity_symm_ball {n : ℕ} (q : Space n) (a : ℝ) (ha : 0 < a)
    (z : Space n) (r : ℝ) :
    (similarity q a ha).symm '' Metric.ball (similarity q a ha z) r = Metric.ball z (a * r) := by
  rw [Homeomorph.image_symm, preimage_similarity_ball]

@[simp] theorem similarity_zero_one {n : ℕ} (z : Space n) :
    similarity (point (0 : Spatial n) 0) 1 zero_lt_one z = z := by
  rcases z with ⟨x, ⟨t⟩⟩
  simp [similarity_apply, point]
  change t - 0 = t
  exact sub_zero t

end ParabolicRectifiability
