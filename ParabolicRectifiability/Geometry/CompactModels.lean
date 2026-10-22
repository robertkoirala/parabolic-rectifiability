import ParabolicRectifiability.Geometry.ModelSpace
import ParabolicRectifiability.Geometry.ProjectionComparison
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UnitInterval

/-! # Compact parameter sets for bounded affine models

The direction constraint is closed because rank equals trace on idempotents.
Bounding the canonical normal anchor therefore gives a genuinely compact set
of spatial affine models, without assuming compactness of an arbitrary family.
-/
noncomputable section
open Set Topology
open scoped RealInnerProductSpace
namespace ParabolicRectifiability

/-- Continuity of the actual finite-dimensional operator trace. -/
theorem continuous_spatialTrace (n : ℕ) :
    Continuous (spatialTrace (n := n)) := by
  have h : spatialTrace (n := n) = fun A =>
      ∑ i : Fin n, ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        A (EuclideanSpace.basisFun (Fin n) ℝ i)⟫ := by
    funext A
    exact LinearMap.trace_eq_sum_inner A.toLinearMap (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [h]
  fun_prop

/-- Canonical projection/anchor data with bounded anchor and prescribed rank. -/
def boundedSpatialParameters (n d : ℕ) (A : ℝ) : Set (SpatialParameters n) :=
  {p | IsSelfAdjoint p.1 ∧ IsIdempotentElem p.1 ∧ spatialTrace p.1 = d ∧
    p.1 p.2 = 0 ∧ ‖p.2‖ ≤ A}

theorem isClosed_boundedSpatialParameters (n d : ℕ) (A : ℝ) :
    IsClosed (boundedSpatialParameters n d A) := by
  have hs : IsClosed {p : SpatialParameters n | star p.1 = p.1} :=
    isClosed_eq (by
      simp_rw [ContinuousLinearMap.star_eq_adjoint]
      exact ContinuousLinearMap.adjoint.continuous.comp continuous_fst) continuous_fst
  have hi : IsClosed {p : SpatialParameters n | p.1 * p.1 = p.1} :=
    isClosed_eq (by fun_prop) continuous_fst
  have ht : IsClosed {p : SpatialParameters n | spatialTrace p.1 = (d : ℝ)} :=
    isClosed_eq ((continuous_spatialTrace n).comp continuous_fst) continuous_const
  have ha : IsClosed {p : SpatialParameters n | p.1 p.2 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hb : IsClosed {p : SpatialParameters n | ‖p.2‖ ≤ A} :=
    isClosed_le (by fun_prop) continuous_const
  exact hs.inter (hi.inter (ht.inter (ha.inter hb)))

theorem isCompact_boundedSpatialParameters (n d : ℕ) (A : ℝ) :
    IsCompact (boundedSpatialParameters n d A) := by
  apply ((isCompact_closedBall (0 : Spatial n →L[ℝ] Spatial n) 1).prod
    (isCompact_closedBall (0 : Spatial n) A)).of_isClosed_subset
      (isClosed_boundedSpatialParameters n d A)
  intro p hp
  rcases hp with ⟨hs, hi, ht, ha, hb⟩
  obtain ⟨hproj, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp ⟨hi, hs⟩
  let := hproj
  have hn : ‖p.1‖ ≤ 1 := by
    rw [heq]
    exact p.1.range.starProjection_norm_le
  exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hn,
    by simpa [Metric.mem_closedBall, dist_zero_right] using hb⟩

theorem mem_boundedSpatialParameters_iff {n d : ℕ} (A : ℝ) (p : SpatialParameters n) :
    p ∈ boundedSpatialParameters n d A ↔
      p ∈ Set.range (AffineSpatialPlane.parameters (n := n) (m := d)) ∧ ‖p.2‖ ≤ A := by
  rw [AffineSpatialPlane.mem_range_parameters_iff]
  change (IsSelfAdjoint p.1 ∧ IsIdempotentElem p.1 ∧ spatialTrace p.1 = (d : ℝ) ∧
    p.1 p.2 = 0 ∧ ‖p.2‖ ≤ A) ↔ _
  constructor
  · rintro ⟨hs, hi, ht, ha, hb⟩
    have hr : Module.finrank ℝ p.1.range = d := by
      exact_mod_cast ((spatialTrace_eq_finrank_range p.1 hi).symm.trans ht)
    exact ⟨⟨hs, hi, hr, ha⟩, hb⟩
  · rintro ⟨⟨hs, hi, hr, ha⟩, hb⟩
    refine ⟨hs, hi, ?_, ha, hb⟩
    rw [spatialTrace_eq_finrank_range p.1 hi, hr]

/-- Radially moving an exterior anchor to the ball cannot increase its distance
from a point inside the ball. -/
theorem norm_sub_radial_clamp_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : ℝ) (hA : 0 ≤ A) (y a : E)
    (hy : ‖y‖ ≤ A) (ha : A < ‖a‖) :
    ‖y - (A / ‖a‖) • a‖ ^ 2 ≤ ‖y - a‖ ^ 2 := by
  have ha0 : 0 < ‖a‖ := hA.trans_lt ha
  let q := A / ‖a‖
  have hq0 : 0 ≤ q := div_nonneg hA (norm_nonneg a)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_iff₀ ha0).2
    simpa using ha.le
  have hqa : q * ‖a‖ = A := div_mul_cancel₀ A ha0.ne'
  have hi : ⟪y, a⟫ ≤ A * ‖a‖ :=
    (real_inner_le_norm y a).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg a))
  have hiq : ⟪y, a⟫ ≤ q * ‖a‖ ^ 2 := by
    calc
      _ ≤ A * ‖a‖ := hi
      _ = q * ‖a‖ ^ 2 := by rw [← hqa]; ring
  have hpos : 0 ≤ (1 + q) * ‖a‖ ^ 2 - 2 * ⟪y, a⟫ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sq_nonneg ‖a‖)]
  have hprod := mul_nonneg (sub_nonneg.mpr hq1) hpos
  change ‖y - q • a‖ ^ 2 ≤ ‖y - a‖ ^ 2
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
  nlinarith

/-- Clamping a real time to an interval containing the source time decreases
its absolute time error. -/
theorem abs_sub_clamped_time_le (T : ℝ) (hT : 0 ≤ T) (t tau : ℝ)
    (ht : |t| ≤ T) :
    |t - (Set.projIcc (-T) T (by linarith) tau : ℝ)| ≤ |t - tau| := by
  have hmem : t ∈ Set.Icc (-T) T := abs_le.mp ht
  have hfix : (Set.projIcc (-T) T (by linarith) t : ℝ) = t := by
    exact congrArg Subtype.val (Set.projIcc_of_mem (show -T ≤ T by linarith) hmem)
  simpa only [hfix] using (Set.abs_projIcc_sub_projIcc (show -T ≤ T by linarith)
    (c := t) (d := tau))



/-- The bounded spatial parameter set lies in the actual affine-model image. -/
theorem boundedSpatialParameters_subset_range (n d : ℕ) (A : ℝ) :
    boundedSpatialParameters n d A ⊆
      Set.range (AffineSpatialPlane.parameters (n := n) (m := d)) :=
  fun p hp => ((mem_boundedSpatialParameters_iff A p).mp hp).1

def boundedHorizontalParameters (n k : ℕ) (A B : ℝ) : Set (HorizontalParameters n) :=
  if 1 ≤ k then boundedSpatialParameters n k A ×ˢ Set.Icc (-B) B else ∅

def boundedVerticalParameters (n k : ℕ) (A : ℝ) : Set (SpatialParameters n) :=
  if 2 ≤ k then boundedSpatialParameters n (k - 2) A else ∅

theorem isCompact_boundedHorizontalParameters (n k : ℕ) (A B : ℝ) :
    IsCompact (boundedHorizontalParameters n k A B) := by
  unfold boundedHorizontalParameters
  split_ifs
  · exact (isCompact_boundedSpatialParameters n k A).prod isCompact_Icc
  · exact isCompact_empty

theorem isCompact_boundedVerticalParameters (n k : ℕ) (A : ℝ) :
    IsCompact (boundedVerticalParameters n k A) := by
  unfold boundedVerticalParameters
  split_ifs
  · exact isCompact_boundedSpatialParameters n (k - 2) A
  · exact isCompact_empty

theorem boundedHorizontalParameters_subset_range (n k : ℕ) (A B : ℝ) :
    boundedHorizontalParameters n k A B ⊆
      Set.range (HorizontalModel.parameters (n := n) (k := k)) := by
  intro p hp
  by_cases hk : 1 ≤ k
  · rw [boundedHorizontalParameters, ite_eq_left hk] at hp
    exact (HorizontalModel.mem_range_parameters_iff p).mpr
      ⟨hk, boundedSpatialParameters_subset_range n k A hp.1⟩
  · simp [boundedHorizontalParameters, hk] at hp

theorem boundedVerticalParameters_subset_range (n k : ℕ) (A : ℝ) :
    boundedVerticalParameters n k A ⊆
      Set.range (VerticalModel.parameters (n := n) (k := k)) := by
  intro p hp
  by_cases hk : 2 ≤ k
  · rw [boundedVerticalParameters, ite_eq_left hk] at hp
    exact (VerticalModel.mem_range_parameters_iff p).mpr
      ⟨k - 2, hk, Nat.sub_add_cancel hk, boundedSpatialParameters_subset_range n (k - 2) A hp⟩
  · simp [boundedVerticalParameters, hk] at hp

def boundedHorizontalModels (n k : ℕ) (A B : ℝ) : Set (HorizontalModel n k) :=
  HorizontalModel.parameters ⁻¹' boundedHorizontalParameters n k A B

def boundedVerticalModels (n k : ℕ) (A : ℝ) : Set (VerticalModel n k) :=
  VerticalModel.parameters ⁻¹' boundedVerticalParameters n k A

theorem isCompact_boundedHorizontalModels (n k : ℕ) (A B : ℝ) :
    IsCompact (boundedHorizontalModels n k A B) :=
  HorizontalModel.isEmbedding_parameters.isInducing.isCompact_preimage'
    (isCompact_boundedHorizontalParameters n k A B)
    (boundedHorizontalParameters_subset_range n k A B)

theorem isCompact_boundedVerticalModels (n k : ℕ) (A : ℝ) :
    IsCompact (boundedVerticalModels n k A) :=
  VerticalModel.isEmbedding_parameters.isInducing.isCompact_preimage'
    (isCompact_boundedVerticalParameters n k A)
    (boundedVerticalParameters_subset_range n k A)

@[simp] theorem mem_boundedHorizontalModels {n k : ℕ} (A B : ℝ)
    (L : HorizontalModel n k) :
    L ∈ boundedHorizontalModels n k A B ↔ ‖L.spatial.anchor‖ ≤ A ∧ |L.time| ≤ B := by
  change L.parameters ∈ boundedHorizontalParameters n k A B ↔ _
  rw [boundedHorizontalParameters, ite_eq_left L.positive]
  change (L.spatial.parameters ∈ boundedSpatialParameters n k A ∧
    L.time ∈ Set.Icc (-B) B) ↔ _
  rw [mem_boundedSpatialParameters_iff]
  have hp : L.spatial.parameters ∈ Set.range (AffineSpatialPlane.parameters (n := n) (m := k)) :=
    ⟨L.spatial, rfl⟩
  simp only [hp, true_and, Set.mem_Icc, abs_le]
  rfl

@[simp] theorem mem_boundedVerticalModels {n k : ℕ} (A : ℝ)
    (L : VerticalModel n k) :
    L ∈ boundedVerticalModels n k A ↔ ‖L.spatial.anchor‖ ≤ A := by
  change L.parameters ∈ boundedVerticalParameters n k A ↔ _
  rw [boundedVerticalParameters, ite_eq_left L.two_le, mem_boundedSpatialParameters_iff]
  obtain ⟨m, ht, hm, hp⟩ := (VerticalModel.mem_range_parameters_iff L.parameters).mp ⟨L, rfl⟩
  have heq : m = k - 2 := by omega
  rw [heq] at hp
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

def boundedModels (n k : ℕ) (F : FamilyKind) (A B : ℝ) : Set (Models n k F) :=
  match F with
  | .horizontal => boundedHorizontalModels n k A B
  | .vertical => boundedVerticalModels n k A
  | .mixed => Sum.inl '' boundedHorizontalModels n k A B ∪ Sum.inr '' boundedVerticalModels n k A

theorem isCompact_boundedModels (n k : ℕ) (F : FamilyKind) (A B : ℝ) :
    IsCompact (boundedModels n k F A B) := by
  cases F with
  | horizontal => exact isCompact_boundedHorizontalModels n k A B
  | vertical => exact isCompact_boundedVerticalModels n k A
  | mixed =>
    have hH : IsCompact ((Sum.inl : HorizontalModel n k → AdmissibleModel n k) ''
        boundedHorizontalModels n k A B) :=
      (isCompact_boundedHorizontalModels n k A B).image continuous_inl
    have hV : IsCompact ((Sum.inr : VerticalModel n k → AdmissibleModel n k) ''
        boundedVerticalModels n k A) :=
      (isCompact_boundedVerticalModels n k A).image continuous_inr
    exact hH.union hV

namespace AffineSpatialPlane

variable {n d : ℕ}

/-- Keep the direction and radially clamp only the canonical normal anchor. -/
def clampAnchor (L : AffineSpatialPlane n d) (A : ℝ) : AffineSpatialPlane n d :=
  if ‖L.anchor‖ ≤ A then L else
    { direction := L.direction
      rank_eq := L.rank_eq
      anchor := (A / ‖L.anchor‖) • L.anchor
      anchor_orthogonal := L.direction.orthogonal.smul_mem _ L.anchor_orthogonal }

@[simp] theorem clampAnchor_direction (L : AffineSpatialPlane n d) (A : ℝ) :
    (L.clampAnchor A).direction = L.direction := by
  unfold clampAnchor
  split_ifs <;> rfl

theorem clampAnchor_norm_le (L : AffineSpatialPlane n d) {A : ℝ} (hA : 0 ≤ A) :
    ‖(L.clampAnchor A).anchor‖ ≤ A := by
  by_cases h : ‖L.anchor‖ ≤ A
  · simp [clampAnchor, h]
  · have ha : 0 < ‖L.anchor‖ := hA.trans_lt (lt_of_not_ge h)
    simp only [clampAnchor, ite_eq_right h, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hA (norm_nonneg _)), div_mul_cancel₀ A ha.ne', le_refl]

theorem clampAnchor_spatialCost_le (L : AffineSpatialPlane n d) {A : ℝ} (hA : 0 ≤ A)
    (y : Coordinates n) (hy : ‖y.1‖ ≤ A) :
    (L.clampAnchor A).spatialCost y ≤ L.spatialCost y := by
  by_cases h : ‖L.anchor‖ ≤ A
  · simp [clampAnchor, h]
  · have hn : ‖y.1 - L.direction.starProjection y.1‖ ≤ A := by
      rw [← L.direction.starProjection_orthogonal_val]
      exact (L.direction.orthogonal.norm_starProjection_apply_le y.1).trans hy
    simpa only [spatialCost, clampAnchor, ite_eq_right h] using
      norm_sub_radial_clamp_sq_le A hA _ _ hn (lt_of_not_ge h)

end AffineSpatialPlane


namespace HorizontalModel
variable {n k : ℕ}

def clamp (L : HorizontalModel n k) (A B : ℝ) (hB : 0 ≤ B) : HorizontalModel n k :=
  ⟨L.positive, L.spatial.clampAnchor A, Set.projIcc (-B) B (by linarith) L.time⟩

theorem clamp_mem_bounded (L : HorizontalModel n k) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    L.clamp A B hB ∈ boundedHorizontalModels n k A B := by
  rw [mem_boundedHorizontalModels]
  exact ⟨L.spatial.clampAnchor_norm_le hA,
    abs_le.mpr (Set.projIcc (-B) B (by linarith) L.time).property⟩

theorem clamp_realCost_le (L : HorizontalModel n k) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (z : Space n)
    (hx : ‖z.1‖ ≤ A) (ht : |z.2.val| ≤ B) :
    (L.clamp A B hB).realCost z ≤ L.realCost z := by
  exact max_le_max (L.spatial.clampAnchor_spatialCost_le hA (coordinatesHomeomorph n z) hx)
    (abs_sub_clamped_time_le B hB z.2.val L.time ht)

end HorizontalModel

namespace VerticalModel
variable {n k : ℕ}

def clamp (L : VerticalModel n k) (A : ℝ) : VerticalModel n k :=
  ⟨L.spatialRank, L.two_le, L.rank_eq, L.spatial.clampAnchor A⟩

theorem clamp_mem_bounded (L : VerticalModel n k) (A : ℝ) (hA : 0 ≤ A) :
    L.clamp A ∈ boundedVerticalModels n k A := by
  rw [mem_boundedVerticalModels]
  exact L.spatial.clampAnchor_norm_le hA

theorem clamp_realCost_le (L : VerticalModel n k) (A : ℝ) (hA : 0 ≤ A)
    (z : Space n) (hx : ‖z.1‖ ≤ A) : (L.clamp A).realCost z ≤ L.realCost z :=
  L.spatial.clampAnchor_spatialCost_le hA (coordinatesHomeomorph n z) hx

end VerticalModel

/-- A genuine bounded competitor, preserving the original model's type. -/
def clampModel {n k : ℕ} {F : FamilyKind} (L : Models n k F)
    (A B : ℝ) (hB : 0 ≤ B) : Models n k F :=
  match F with
  | .horizontal => L.clamp A B hB
  | .vertical => L.clamp A
  | .mixed => match L with
    | Sum.inl H => Sum.inl (H.clamp A B hB)
    | Sum.inr V => Sum.inr (V.clamp A)

theorem clampModel_mem_bounded {n k : ℕ} {F : FamilyKind} (L : Models n k F)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    clampModel L A B hB ∈ boundedModels n k F A B := by
  cases F with
  | horizontal => exact L.clamp_mem_bounded A B hA hB
  | vertical => exact L.clamp_mem_bounded A hA
  | mixed => cases L with
    | inl L => exact Or.inl ⟨L.clamp A B hB, L.clamp_mem_bounded A B hA hB, rfl⟩
    | inr L => exact Or.inr ⟨L.clamp A, L.clamp_mem_bounded A hA, rfl⟩

theorem boundedModels_nonempty {n k : ℕ} {F : FamilyKind}
    (hF : Nonempty (Models n k F)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (boundedModels n k F A B).Nonempty := by
  obtain ⟨L⟩ := hF
  exact ⟨clampModel L A B hB, clampModel_mem_bounded L A B hA hB⟩

/-- Pointwise domination of the actual squared parabolic distance, including
horizontal time error and both branches of a mixed family. -/
theorem modelCost_clampModel_le {n k : ℕ} {F : FamilyKind} (L : Models n k F)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (z : Space n)
    (hx : ‖z.1‖ ≤ A) (ht : |z.2.val| ≤ B) :
    modelCost (clampModel L A B hB) z ≤ modelCost L z := by
  rw [modelCost_eq_ofReal, modelCost_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  cases F with
  | horizontal => exact L.clamp_realCost_le A B hA hB z hx ht
  | vertical => exact L.clamp_realCost_le A hA z hx
  | mixed => cases L with
    | inl L => exact L.clamp_realCost_le A B hA hB z hx ht
    | inr L => exact L.clamp_realCost_le A hA z hx

end ParabolicRectifiability
