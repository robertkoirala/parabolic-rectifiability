import ParabolicRectifiability.Geometry.ModelDistance
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Projection parameters for affine models

Each affine model is encoded by its orthogonal projection, anchor and (for horizontal
models) time. The `mem_range_parameters_iff` lemmas characterize the parameter images,
`parametersHomeomorph` identifies each model type with its image, and `spatialParameterCost`, `horizontalParameterCost` extend the model costs to the
ambient parameter spaces. -/
noncomputable section
namespace ParabolicRectifiability
open Topology TopologicalSpace

abbrev SpatialParameters (n : ℕ) := (Spatial n →L[ℝ] Spatial n) × Spatial n
abbrev HorizontalParameters (n : ℕ) := SpatialParameters n × ℝ

namespace AffineSpatialPlane
variable {n m : ℕ}

def parameters (L : AffineSpatialPlane n m) : SpatialParameters n :=
  (L.linearProjection, L.anchor)

theorem linearProjection_range (L : AffineSpatialPlane n m) :
    L.linearProjection.range = L.direction := L.direction.range_starProjection

theorem linearProjection_selfAdjoint (L : AffineSpatialPlane n m) :
    IsSelfAdjoint L.linearProjection := isSelfAdjoint_starProjection L.direction

theorem linearProjection_idempotent (L : AffineSpatialPlane n m) :
    IsIdempotentElem L.linearProjection := L.direction.isIdempotentElem_starProjection

theorem linearProjection_rank (L : AffineSpatialPlane n m) :
    Module.finrank ℝ L.linearProjection.range = m := by
  rw [L.linearProjection_range, L.rank_eq]

/-- The parameter image consists exactly of canonical affine-plane data. -/
theorem mem_range_parameters_iff (p : SpatialParameters n) :
    p ∈ Set.range (parameters (n := n) (m := m)) ↔
      IsSelfAdjoint p.1 ∧ IsIdempotentElem p.1 ∧
      Module.finrank ℝ p.1.range = m ∧ p.1 p.2 = 0 := by
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.linearProjection_selfAdjoint, L.linearProjection_idempotent,
      L.linearProjection_rank, L.linearProjection_anchor⟩
  · rintro ⟨hs, hi, hr, ha⟩
    obtain ⟨_, hp⟩ := isStarProjection_iff_eq_starProjection_range.mp ⟨hi, hs⟩
    refine ⟨⟨p.1.range, hr, p.2, ?_⟩, ?_⟩
    · apply (Submodule.starProjection_apply_eq_zero_iff p.1.range).mp
      rw [← hp]
      exact ha
    · exact Prod.ext hp.symm rfl

theorem parameters_injective : Function.Injective (parameters (n := n) (m := m)) := by
  intro L Q h
  have hp : L.linearProjection = Q.linearProjection := congrArg Prod.fst h
  have ha : L.anchor = Q.anchor := congrArg Prod.snd h
  have hd : L.direction = Q.direction := by
    rw [← L.linearProjection_range, ← Q.linearProjection_range, hp]
  cases L
  cases Q
  cases hd
  cases ha
  rfl

instance instTopologicalSpace : TopologicalSpace (AffineSpatialPlane n m) :=
  TopologicalSpace.induced parameters inferInstance

theorem isEmbedding_parameters : IsEmbedding (parameters (n := n) (m := m)) :=
  parameters_injective.isEmbedding_induced

def parametersHomeomorph : AffineSpatialPlane n m ≃ₜ Set.range (parameters (n := n) (m := m)) :=
  isEmbedding_parameters.toHomeomorph

instance instSecondCountableTopology : SecondCountableTopology (AffineSpatialPlane n m) :=
  isEmbedding_parameters.secondCountableTopology

instance instSeparableSpace : SeparableSpace (AffineSpatialPlane n m) :=
  isEmbedding_parameters.separableSpace

theorem continuous_parameters : Continuous (parameters (n := n) (m := m)) :=
  isEmbedding_parameters.continuous

end AffineSpatialPlane

namespace HorizontalModel
variable {n k : ℕ}

def parameters (L : HorizontalModel n k) : HorizontalParameters n :=
  (L.spatial.parameters, L.time)

/-- Horizontal parameters retain the positive-dimensional guard and arbitrary real time. -/
theorem mem_range_parameters_iff (p : HorizontalParameters n) :
    p ∈ Set.range (parameters (n := n) (k := k)) ↔
      1 ≤ k ∧ p.1 ∈ Set.range (AffineSpatialPlane.parameters (n := n) (m := k)) := by
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.positive, L.spatial, rfl⟩
  · rintro ⟨hk, L, hL⟩
    exact ⟨⟨hk, L, p.2⟩, Prod.ext hL rfl⟩

theorem parameters_injective : Function.Injective (parameters (n := n) (k := k)) := by
  intro L Q h
  have hs := AffineSpatialPlane.parameters_injective (congrArg Prod.fst h)
  have ht : L.time = Q.time := congrArg Prod.snd h
  cases L
  cases Q
  cases hs
  cases ht
  rfl

instance instTopologicalSpace : TopologicalSpace (HorizontalModel n k) :=
  TopologicalSpace.induced parameters inferInstance

theorem isEmbedding_parameters : IsEmbedding (parameters (n := n) (k := k)) :=
  parameters_injective.isEmbedding_induced

def parametersHomeomorph : HorizontalModel n k ≃ₜ Set.range (parameters (n := n) (k := k)) :=
  isEmbedding_parameters.toHomeomorph

instance instSecondCountableTopology : SecondCountableTopology (HorizontalModel n k) :=
  isEmbedding_parameters.secondCountableTopology

instance instSeparableSpace : SeparableSpace (HorizontalModel n k) :=
  isEmbedding_parameters.separableSpace

theorem continuous_parameters : Continuous (parameters (n := n) (k := k)) :=
  isEmbedding_parameters.continuous

end HorizontalModel

namespace VerticalModel
variable {n k : ℕ}

def parameters (L : VerticalModel n k) : SpatialParameters n := L.spatial.parameters

/-- The vertical parameter image retains the actual guarded spatial rank. -/
theorem mem_range_parameters_iff (p : SpatialParameters n) :
    p ∈ Set.range (parameters (n := n) (k := k)) ↔
      ∃ m : ℕ, 2 ≤ k ∧ m + 2 = k ∧
        p ∈ Set.range (AffineSpatialPlane.parameters (n := n) (m := m)) := by
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L.spatialRank, L.two_le, L.rank_eq, L.spatial, rfl⟩
  · rintro ⟨m, hk, hm, L, hL⟩
    exact ⟨⟨m, hk, hm, L⟩, hL⟩

theorem parameters_injective : Function.Injective (parameters (n := n) (k := k)) := by
  intro L Q h
  have he : L.spatialRank = Q.spatialRank := by
    have := L.rank_eq
    have := Q.rank_eq
    omega
  cases L with
  | mk a ha ea A =>
    cases Q with
    | mk b hb eb B =>
      dsimp at he
      subst b
      have hs : A = B := AffineSpatialPlane.parameters_injective h
      cases hs
      rfl

instance instTopologicalSpace : TopologicalSpace (VerticalModel n k) :=
  TopologicalSpace.induced parameters inferInstance

theorem isEmbedding_parameters : IsEmbedding (parameters (n := n) (k := k)) :=
  parameters_injective.isEmbedding_induced

def parametersHomeomorph : VerticalModel n k ≃ₜ Set.range (parameters (n := n) (k := k)) :=
  isEmbedding_parameters.toHomeomorph

instance instSecondCountableTopology : SecondCountableTopology (VerticalModel n k) :=
  isEmbedding_parameters.secondCountableTopology

instance instSeparableSpace : SeparableSpace (VerticalModel n k) :=
  isEmbedding_parameters.separableSpace

theorem continuous_parameters : Continuous (parameters (n := n) (k := k)) :=
  isEmbedding_parameters.continuous

end VerticalModel

instance instTopologicalSpaceModels (n k : ℕ) (T : FamilyKind) : TopologicalSpace (Models n k T) :=
  match T with
  | .horizontal => (inferInstance : TopologicalSpace (HorizontalModel n k))
  | .vertical => (inferInstance : TopologicalSpace (VerticalModel n k))
  | .mixed => (inferInstance : TopologicalSpace (AdmissibleModel n k))

instance instSecondCountableTopologyModels (n k : ℕ) (T : FamilyKind) :
    SecondCountableTopology (Models n k T) := by
  cases T <;> dsimp [Models, instTopologicalSpaceModels] <;> infer_instance

instance instSeparableSpaceModels (n k : ℕ) (T : FamilyKind) : SeparableSpace (Models n k T) := by
  cases T <;> dsimp [Models, instTopologicalSpaceModels] <;> infer_instance

/-- The spatial formula extended to the ambient parameter space. -/
def spatialParameterCost {n : ℕ} (p : SpatialParameters n) (z : Space n) : ℝ :=
  ‖z.1 - p.1 z.1 - p.2‖ ^ 2

/-- The horizontal formula extended to the ambient parameter space. -/
def horizontalParameterCost {n : ℕ} (p : HorizontalParameters n) (z : Space n) : ℝ :=
  max (spatialParameterCost p.1 z) |z.2.val - p.2|

theorem continuous_spatialParameterCost (n : ℕ) :
    Continuous (Function.uncurry (spatialParameterCost (n := n))) := by
  unfold spatialParameterCost Function.uncurry
  fun_prop

theorem continuous_horizontalParameterCost (n : ℕ) :
    Continuous (Function.uncurry (horizontalParameterCost (n := n))) := by
  have harg : Continuous (fun p : HorizontalParameters n × Space n => (p.1.1, p.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  have hs := (continuous_spatialParameterCost n).comp harg
  have ht : Continuous (fun p : HorizontalParameters n × Space n => p.2.2.val - p.1.2) :=
    (continuous_time.comp continuous_snd).sub continuous_fst.snd
  exact hs.max ht.abs

theorem continuous_modelRealCost {n k : ℕ} {T : FamilyKind} :
    Continuous (fun p : Models n k T × Space n => modelRealCost p.1 p.2) := by
  have hargH : Continuous (fun p : HorizontalModel n k × Space n => (p.1.parameters, p.2)) :=
    (HorizontalModel.continuous_parameters.comp continuous_fst).prodMk continuous_snd
  have hargV : Continuous (fun p : VerticalModel n k × Space n => (p.1.parameters, p.2)) :=
    (VerticalModel.continuous_parameters.comp continuous_fst).prodMk continuous_snd
  have hH := (continuous_horizontalParameterCost n).comp hargH
  have hV := (continuous_spatialParameterCost n).comp hargV
  cases T with
  | horizontal => exact hH
  | vertical => exact hV
  | mixed =>
    apply ((hH.sumElim hV).comp Homeomorph.sumProdDistrib.continuous).congr
    rintro ⟨L, w⟩
    cases L <;> rfl

end ParabolicRectifiability
