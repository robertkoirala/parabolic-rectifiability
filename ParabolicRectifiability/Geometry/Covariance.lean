import ParabolicRectifiability.Measure.SpatialMoments
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spatial variance and minimizing affine planes

All moments come from `SpatialSource.covariance`. The sorted spectral basis is
chosen by the finite-dimensional spectral theorem; no uniqueness is asserted.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace ParabolicRectifiability
open MeasureTheory Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The diagonal of an orthogonal projection is its squared projected norm. -/
theorem inner_projection_eq_norm_sq (P : Spatial n →L[ℝ] Spatial n)
    (hP : IsStarProjection P) (v : Spatial n) : ⟪v, P v⟫ = ‖P v‖ ^ 2 := by
  have hs := hP.isSelfAdjoint.isSymmetric v (P v)
  have hi : P (P v) = P v := congrArg (fun A : Spatial n →L[ℝ] Spatial n => A v)
    hP.isIdempotentElem.eq
  change ⟪P v, P v⟫ = ⟪v, P (P v)⟫ at hs
  rw [hi, real_inner_self_eq_norm_sq] at hs
  exact hs.symm

namespace AffineSpatialPlane
variable {l : ℕ}

theorem spatial_infDist_eq (L : AffineSpatialPlane n l) (x : Spatial n) :
    Metric.infDist x L.toSet = ‖x - L.projection x‖ := by
  apply le_antisymm
  · simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (L.projection_mem x)
  · apply (Metric.le_infDist ⟨L.projection x, L.projection_mem x⟩).mpr
    intro y hy
    simpa [dist_eq_norm] using L.nearest x hy

@[fun_prop] theorem continuous_projection (L : AffineSpatialPlane n l) :
    Continuous L.projection := continuous_const.add L.linearProjection.continuous

end AffineSpatialPlane

namespace SpatialSource
variable (S : SpatialSource n)

/-- Actual squared-distance fitting error of an affine plane. -/
def fittingError {l : ℕ} (L : AffineSpatialPlane n l) : ℝ :=
  ∫ z, ‖z.1 - L.projection z.1‖ ^ 2 ∂S.measure

theorem integrable_fittingError {l : ℕ} (L : AffineSpatialPlane n l) :
    Integrable (fun z : Space n => ‖z.1 - L.projection z.1‖ ^ 2) S.measure :=
  S.integrable (by fun_prop)

theorem fittingError_nonneg {l : ℕ} (L : AffineSpatialPlane n l) :
    0 ≤ S.fittingError L := integral_nonneg fun _ => sq_nonneg _

theorem fittingError_eq_spatialCost {l : ℕ} (L : AffineSpatialPlane n l) :
    S.fittingError L = ∫ z, L.spatialCost (coordinatesHomeomorph n z) ∂S.measure := by
  simp only [fittingError, L.residual, AffineSpatialPlane.spatialCost]
  rfl

theorem fittingError_eq_infDist {l : ℕ} (L : AffineSpatialPlane n l) :
    S.fittingError L = ∫ z, (Metric.infDist z.1 L.toSet) ^ 2 ∂S.measure := by
  simp_rw [L.spatial_infDist_eq]
  rfl

/-- Variance about every affine plane, with its canonical orthogonal anchor. -/
theorem fittingError_variance {l : ℕ} (L : AffineSpatialPlane n l) :
    S.fittingError L = spatialTrace ((1 - L.linearProjection) * S.covariance) +
      S.mass * ‖S.barycenter - L.projection S.barycenter‖ ^ 2 := by
  have h := S.integral_centered_affine_sq (1 - L.linearProjection)
    (S.barycenter - L.projection S.barycenter)
  have hid (z : Space n) : (1 - L.linearProjection) (S.centered z) +
      (S.barycenter - L.projection S.barycenter) = z.1 - L.projection z.1 := by
    simp only [centered, sub_apply, one_apply_eq_self,
      map_sub, AffineSpatialPlane.projection]
    abel
  simp_rw [hid] at h
  rw [S.trace_mul_covariance]
  simpa only [fittingError, inner_projection_eq_norm_sq _ L.linearProjection_isStarProjection.one_sub]
    using h

theorem fittingError_rank_zero (L : AffineSpatialPlane n 0) :
    S.fittingError L = spatialTrace S.covariance +
      S.mass * ‖S.barycenter - L.anchor‖ ^ 2 := by
  have hd : L.direction = ⊥ := Submodule.finrank_eq_zero.mp L.rank_eq
  rw [S.fittingError_variance]
  simp [AffineSpatialPlane.linearProjection, AffineSpatialPlane.projection, hd]

theorem fittingError_full_rank (L : AffineSpatialPlane n n) : S.fittingError L = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  have h := L.nearest z.1 (y := z.1) (by simp)
  simp only [sub_self, norm_zero] at h
  rw [le_antisymm h (norm_nonneg _)]
  norm_num

/-- Nonincreasing eigenvalues of the actual covariance. -/
def eigenvalue : Fin n → ℝ :=
  S.covariance_isSymmetric.eigenvalues (by simp [Spatial])

/-- An actual orthonormal eigenbasis, including repeated eigenvalues. -/
def eigenbasis : OrthonormalBasis (Fin n) ℝ (Spatial n) :=
  S.covariance_isSymmetric.eigenvectorBasis (by simp [Spatial])

theorem eigenvalue_antitone : Antitone S.eigenvalue :=
  S.covariance_isSymmetric.eigenvalues_antitone _

theorem eigenvalue_nonneg (i : Fin n) : 0 ≤ S.eigenvalue i :=
  S.covariance_isPositive.toLinearMap.nonneg_eigenvalues _ i

theorem covariance_eigenbasis (i : Fin n) :
    S.covariance (S.eigenbasis i) = S.eigenvalue i • S.eigenbasis i :=
  S.covariance_isSymmetric.apply_eigenvectorBasis _ i

theorem trace_covariance_eq_sum : spatialTrace S.covariance = ∑ i, S.eigenvalue i :=
  S.covariance_isSymmetric.trace_eq_sum_eigenvalues _

/-- The span of precisely the first `l` spectral vectors. -/
def topSubspace (l : ℕ) (hl : l ≤ n) : Submodule ℝ (Spatial n) :=
  Submodule.span ℝ (range fun i : Fin l => S.eigenbasis (Fin.castLE hl i))

theorem topSubspace_rank (l : ℕ) (hl : l ≤ n) :
    Module.finrank ℝ (S.topSubspace l hl) = l := by
  unfold topSubspace
  have hi : LinearIndependent ℝ (fun i : Fin l => S.eigenbasis (Fin.castLE hl i)) :=
    S.eigenbasis.orthonormal.linearIndependent.comp (Fin.castLE hl) (Fin.castLE_injective hl)
  exact (finrank_span_eq_card hi).trans (Fintype.card_fin l)

/-- Translate through the barycenter; `ofTranslate` supplies the canonical anchor. -/
def topPlane (l : ℕ) (hl : l ≤ n) : AffineSpatialPlane n l :=
  AffineSpatialPlane.ofTranslate (S.topSubspace l hl) (S.topSubspace_rank l hl) S.barycenter

theorem topPlane_projection_barycenter (l : ℕ) (hl : l ≤ n) :
    (S.topPlane l hl).projection S.barycenter = S.barycenter := by
  simp [topPlane, AffineSpatialPlane.ofTranslate, AffineSpatialPlane.projection,
    AffineSpatialPlane.linearProjection]

theorem topProjection_eigenbasis (l : ℕ) (hl : l ≤ n) (i : Fin n) :
    (S.topPlane l hl).linearProjection (S.eigenbasis i) =
      if i.val < l then S.eigenbasis i else 0 := by
  classical
  change (S.topSubspace l hl).starProjection (S.eigenbasis i) = _
  split_ifs with hi
  · apply Submodule.starProjection_eq_self_iff.mpr
    apply Submodule.subset_span
    exact ⟨⟨i.val, hi⟩, congrArg S.eigenbasis (Fin.ext rfl)⟩
  · apply (Submodule.starProjection_apply_eq_zero_iff (S.topSubspace l hl)).mpr
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact S.eigenbasis.inner_eq_zero (by intro h; have := congrArg Fin.val h; simp at this; omega)
    | zero => simp
    | add v w hv hw hvw hww => simp [inner_add_left, hvw, hww]
    | smul c v hv hvw => simp [inner_smul_left, hvw]

/-- Competitor diagonal weights in the same covariance eigenbasis. -/
def projectionWeight {l : ℕ} (L : AffineSpatialPlane n l) (i : Fin n) : ℝ :=
  ‖L.linearProjection (S.eigenbasis i)‖ ^ 2

theorem projectionWeight_nonneg {l : ℕ} (L : AffineSpatialPlane n l) (i : Fin n) :
    0 ≤ S.projectionWeight L i := sq_nonneg _

theorem projectionWeight_le_one {l : ℕ} (L : AffineSpatialPlane n l) (i : Fin n) :
    S.projectionWeight L i ≤ 1 := by
  have h := L.direction.norm_starProjection_apply_le (S.eigenbasis i)
  rw [S.eigenbasis.norm_eq_one i] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by norm_num)

theorem sum_projectionWeight {l : ℕ} (L : AffineSpatialPlane n l) :
    ∑ i, S.projectionWeight L i = l := by
  have ht := spatialTrace_eq_finrank_range L.linearProjection
    L.linearProjection_isStarProjection.isIdempotentElem
  rw [L.linearProjection_rank, spatialTrace,
    LinearMap.trace_eq_sum_inner _ S.eigenbasis] at ht
  simpa only [projectionWeight, ContinuousLinearMap.coe_coe,
    inner_projection_eq_norm_sq _ L.linearProjection_isStarProjection] using ht

theorem trace_projection_covariance {l : ℕ} (L : AffineSpatialPlane n l) :
    spatialTrace (L.linearProjection * S.covariance) =
      ∑ i, S.eigenvalue i * S.projectionWeight L i := by
  rw [spatialTrace, LinearMap.trace_eq_sum_inner _ S.eigenbasis]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪S.eigenbasis i, L.linearProjection (S.covariance (S.eigenbasis i))⟫ = _
  rw [S.covariance_eigenbasis, map_smul, inner_smul_right,
    inner_projection_eq_norm_sq _ L.linearProjection_isStarProjection]
  rfl

theorem top_projectionWeight (l : ℕ) (hl : l ≤ n) (i : Fin n) :
    S.projectionWeight (S.topPlane l hl) i = if i.val < l then 1 else 0 := by
  classical
  unfold projectionWeight
  rw [S.topProjection_eigenbasis]
  split_ifs <;> simp [S.eigenbasis.norm_eq_one]

/-- The ordered weighted-sum bound uses `0 ≤ dᵢ ≤ 1` and the exact sum `l`. -/
theorem weighted_sum_le_top {l : ℕ} (hl : l ≤ n) (L : AffineSpatialPlane n l) :
    (∑ i, S.eigenvalue i * S.projectionWeight L i) ≤
      ∑ i, S.eigenvalue i * S.projectionWeight (S.topPlane l hl) i := by
  classical
  by_cases h0 : l = 0
  · subst l
    have hd (i : Fin n) : S.projectionWeight L i = 0 := by
      have h := Finset.single_le_sum (fun j _ => S.projectionWeight_nonneg L j)
        (Finset.mem_univ i)
      rw [S.sum_projectionWeight] at h
      exact le_antisymm (by simpa using h) (S.projectionWeight_nonneg L i)
    simp [hd, S.top_projectionWeight]
  · let k : Fin n := ⟨l - 1, by omega⟩
    have hpoint (i : Fin n) :
        S.eigenvalue i * (S.projectionWeight L i -
          S.projectionWeight (S.topPlane l hl) i) ≤
        S.eigenvalue k * (S.projectionWeight L i -
          S.projectionWeight (S.topPlane l hl) i) := by
      rw [S.top_projectionWeight]
      split_ifs with hi
      · apply mul_le_mul_of_nonpos_right
        · exact S.eigenvalue_antitone (show i ≤ k from by change i.val ≤ l - 1; omega)
        · linarith [S.projectionWeight_le_one L i]
      · apply mul_le_mul_of_nonneg_right
        · exact S.eigenvalue_antitone (show k ≤ i from by change l - 1 ≤ i.val; omega)
        · simpa using S.projectionWeight_nonneg L i
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
    rw [S.sum_projectionWeight L, S.sum_projectionWeight (S.topPlane l hl)] at h
    linarith

/-- The tail is indexed by zero-based `Fin n`: the first omitted index is `l`. -/
def spectralTail (l : ℕ) : ℝ := ∑ i : Fin n, if l ≤ i.val then S.eigenvalue i else 0

theorem trace_complement_top (l : ℕ) (hl : l ≤ n) :
    spatialTrace ((1 - (S.topPlane l hl).linearProjection) * S.covariance) =
      S.spectralTail l := by
  classical
  rw [sub_mul, one_mul, spatialTrace_sub, S.trace_covariance_eq_sum,
    S.trace_projection_covariance, ← Finset.sum_sub_distrib]
  unfold spectralTail
  apply Finset.sum_congr rfl
  intro i _
  rw [S.top_projectionWeight]
  by_cases h : i.val < l <;> simp [h, show (l ≤ i.val) ↔ ¬ i.val < l from by omega]

theorem topPlane_fittingError (l : ℕ) (hl : l ≤ n) :
    S.fittingError (S.topPlane l hl) = S.spectralTail l := by
  rw [S.fittingError_variance, S.topPlane_projection_barycenter,
    S.trace_complement_top]
  simp

theorem spectralTail_le_fittingError {l : ℕ} (hl : l ≤ n)
    (L : AffineSpatialPlane n l) : S.spectralTail l ≤ S.fittingError L := by
  have hw := S.weighted_sum_le_top hl L
  rw [← S.trace_projection_covariance L,
    ← S.trace_projection_covariance (S.topPlane l hl)] at hw
  rw [S.fittingError_variance, ← S.trace_complement_top l hl]
  simp only [sub_mul, one_mul, spatialTrace_sub]
  linarith [mul_nonneg S.mass_nonneg (sq_nonneg ‖S.barycenter - L.projection S.barycenter‖)]

/-- The genuine infimum over all affine planes of the prescribed rank. -/
def minimumError (l : ℕ) : ℝ := sInf (range fun L : AffineSpatialPlane n l => S.fittingError L)

theorem fittingErrors_nonempty (l : ℕ) (hl : l ≤ n) :
    (range fun L : AffineSpatialPlane n l => S.fittingError L).Nonempty :=
  ⟨_, ⟨S.topPlane l hl, rfl⟩⟩

theorem fittingErrors_bddBelow (l : ℕ) :
    BddBelow (range fun L : AffineSpatialPlane n l => S.fittingError L) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨L, rfl⟩
  exact S.fittingError_nonneg L

theorem minimumError_eq_tail (l : ℕ) (hl : l ≤ n) :
    S.minimumError l = S.spectralTail l := by
  apply le_antisymm
  · exact (csInf_le (S.fittingErrors_bddBelow l)
      (mem_range_self (S.topPlane l hl))).trans_eq (S.topPlane_fittingError l hl)
  · apply le_csInf (S.fittingErrors_nonempty l hl)
    rintro _ ⟨L, rfl⟩
    exact S.spectralTail_le_fittingError hl L

theorem minimumError_attained (l : ℕ) (hl : l ≤ n) :
    S.fittingError (S.topPlane l hl) = S.minimumError l := by
  rw [S.topPlane_fittingError, S.minimumError_eq_tail l hl]

theorem minimumError_nonneg (l : ℕ) (hl : l ≤ n) : 0 ≤ S.minimumError l := by
  rw [← S.minimumError_attained l hl]
  exact S.fittingError_nonneg _

theorem minimumError_eq_sum (l : ℕ) (hl : l ≤ n) :
    S.minimumError l = ∑ i : Fin n with l ≤ i.val, S.eigenvalue i := by
  rw [S.minimumError_eq_tail l hl, spectralTail, Finset.sum_filter]

theorem minimumError_step (l : ℕ) (hl0 : 1 ≤ l) (hln : l ≤ n) :
    S.minimumError (l - 1) = S.minimumError l +
      S.eigenvalue ⟨l - 1, by omega⟩ := by
  classical
  rw [S.minimumError_eq_tail (l - 1) (by omega), S.minimumError_eq_tail l hln]
  let k : Fin n := ⟨l - 1, by omega⟩
  have he (i : Fin n) : (if l - 1 ≤ i.val then S.eigenvalue i else 0) =
      (if l ≤ i.val then S.eigenvalue i else 0) +
        (if i = k then S.eigenvalue k else 0) := by
    by_cases hik : i = k
    · subst i; simp [k, show ¬ l ≤ l - 1 from by omega]
    · have hne : i.val ≠ l - 1 := by intro h; apply hik; exact Fin.ext h
      by_cases hi : l ≤ i.val <;> simp [hik, hi, show (l - 1 ≤ i.val) ↔ l ≤ i.val from by omega]
  simp only [spectralTail, he, Finset.sum_add_distrib]
  simp [k]

theorem minimumError_zero : S.minimumError 0 = spatialTrace S.covariance := by
  rw [S.minimumError_eq_tail 0 (Nat.zero_le _), S.trace_covariance_eq_sum]
  simp [spectralTail]

theorem minimumError_full : S.minimumError n = 0 := by
  rw [S.minimumError_eq_tail n le_rfl]
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (Nat.not_le.mpr i.isLt)

/-- The lower spectral bound needed by projection comparison, with source
`lambda_l` represented by zero-based index `l - 1`. -/
theorem covariance_sub_topProjection_isPositive (l : ℕ) (hl0 : 1 ≤ l) (hln : l ≤ n)
    (lambda : ℝ) (_hlambda : 0 < lambda)
    (hle : lambda ≤ S.eigenvalue ⟨l - 1, by omega⟩) :
    (S.covariance - lambda • (S.topPlane l hln).linearProjection).IsPositive := by
  classical
  let A := S.covariance - lambda • (S.topPlane l hln).linearProjection
  have hs : IsSelfAdjoint A := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact S.covariance_isSymmetric.sub
      (LinearMap.IsSymmetric.smul (by simp)
        (S.topPlane l hln).linearProjection_isStarProjection.isSelfAdjoint.isSymmetric)
  have he (i : Fin n) : A (S.eigenbasis i) =
      (S.eigenvalue i - if i.val < l then lambda else 0) • S.eigenbasis i := by
    simp only [A, sub_apply, smul_apply,
      S.covariance_eigenbasis, S.topProjection_eigenbasis]
    split_ifs <;> simp [sub_smul]
  have hc (i : Fin n) : 0 ≤ S.eigenvalue i - if i.val < l then lambda else 0 := by
    split_ifs with hi
    · have := S.eigenvalue_antitone (show i ≤ (⟨l - 1, by omega⟩ : Fin n) from by
        change i.val ≤ l - 1; omega)
      linarith
    · simpa using S.eigenvalue_nonneg i
  refine (ContinuousLinearMap.isPositive_iff A).mpr ⟨hs.isSymmetric, fun v => ?_⟩
  rw [← S.eigenbasis.sum_inner_mul_inner (A v) v]
  apply Finset.sum_nonneg
  intro i _
  have hsym := hs.isSymmetric v (S.eigenbasis i)
  change ⟪A v, S.eigenbasis i⟫ = ⟪v, A (S.eigenbasis i)⟫ at hsym
  rw [hsym, he, inner_smul_right,
    show ⟪v, S.eigenbasis i⟫ = ⟪S.eigenbasis i, v⟫ from real_inner_comm _ _]
  nlinarith [mul_nonneg (hc i) (sq_nonneg ⟪S.eigenbasis i, v⟫)]

end SpatialSource
end ParabolicRectifiability
