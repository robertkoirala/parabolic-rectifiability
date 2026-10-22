import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal
import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.MemberAncestor
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.StopScaleLipschitz
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.StopScaleZero
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.Cutoff
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.OwnerCell
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.LocalFits
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.LocalError
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.Thinness
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.RootThinness
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.SelectionExists
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.StageFacts
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.AssignmentFields
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.CoreEquality
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.CenterSetFields
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.RadiusFields
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.FamilyFields
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.HeightParent
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.SameLevel
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.AdjacentLevel
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.RootAdjacent
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.Coherence
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.FittedTime
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.GenuineTime
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.Terminal.TimeCompatible
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.PointToFit
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.UpperRecentering
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.TubeMass
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.CovarianceLower
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.PlaneComparison

/-! # The terminal construction: composition of the proofs

Assembly of the proofs of the terminal-construction statements. The closed statements are
obtained by feeding each proof its hypotheses; the two inputs from the partition-energy
estimates are supplied by their proofs:

* `d1ccomp_pointToFit` is `PartitionEnergy.d1a_pointToFit_proof`;
* `d1ccomp_planeComparison` is `PartitionEnergy.d1a_planeComparison_proof` applied to
  `d1a_covarianceLower_proof d1a_upperRecentering_proof`;
* `d1ccomp_localADR_mono`, `d1ccomp_terminalConstruction_of` assemble the construction;
* `d1ccomp_<x>` close the statement `<x>`; `d1ccomp_terminalConstruction` is
  `TerminalConstructionStatement`, the type of `d1_hub_terminalConstruction`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

variable {n : ℕ}

/-- Local ADR persists in a smaller buffer. -/
theorem d1ccomp_localADR_mono {k : ℕ} {μ : Measure (Space n)} {A : ℝ} {a : Space n} {ρ ρ' : ℝ}
    (h : LocalADR μ k A a ρ) (hρ : ρ' ≤ ρ) : LocalADR μ k A a ρ' := fun x hx s hs hsρ =>
  h x ⟨hx.1, Metric.ball_subset_ball hρ hx.2⟩ s hs (hsρ.trans hρ)

/-- **Assembly.** The record's existence statements, its four geometric field statements and
its three uniform estimate statements give `TerminalConstructionStatement`. -/
theorem d1ccomp_terminalConstruction_of (hFits : LocalFitsStatement)
    (hSel : SelectionExistsStatement) (hCenter : CenterSetFieldsStatement)
    (hRadius : RadiusFieldsStatement) (hAssign : AssignmentFieldsStatement)
    (hFam : FamilyFieldsStatement) (hCoh : CoherenceStatement)
    (hHP : HeightParentStatement) (hTime : TimeCompatibleStatement) :
    TerminalConstructionStatement := by
  intro n hn k hk hkn A hA
  obtain ⟨Λ₁, hΛ₁, h₁⟩ := hCoh n hn k hk hkn A hA
  obtain ⟨Λ₂, -, h₂⟩ := hHP n hn k hk hkn A hA
  obtain ⟨Λ₃, -, h₃⟩ := hTime n hn k hk hkn A hA
  refine ⟨max Λ₁ (max Λ₂ Λ₃), le_trans hΛ₁ (le_max_left _ _), ?_⟩
  intro Λ hΛ
  obtain ⟨B₁, hB₁, g₁⟩ := h₁ Λ (le_trans (le_max_left _ _) hΛ)
  obtain ⟨B₂, -, g₂⟩ := h₂ Λ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΛ)
  obtain ⟨B₃, -, g₃⟩ := h₃ Λ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛ)
  refine ⟨max B₁ (max B₂ B₃), le_trans hB₁ (le_max_left _ _), ?_⟩
  intro ε hε
  obtain ⟨b₁, hb₁, f₁⟩ := g₁ ε hε
  obtain ⟨b₂, hb₂, f₂⟩ := g₂ ε hε
  obtain ⟨b₃, hb₃, f₃⟩ := g₃ ε hε
  refine ⟨min b₁ (min b₂ b₃), lt_min hb₁ (lt_min hb₂ hb₃), ?_⟩
  intro b hb hbb μ hfin hreg a ha R hR hADR P 𝒢 hroot
  have hR₁ : B₁ * R ≤ max B₁ (max B₂ B₃) * R :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le
  have hR₂ : B₂ * R ≤ max B₁ (max B₂ B₃) * R :=
    mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hR.le
  have hR₃ : B₃ * R ≤ max B₁ (max B₂ B₃) * R :=
    mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hR.le
  have hb₁' : b ≤ b₁ := le_trans hbb (min_le_left _ _)
  have hb₂' : b ≤ b₂ := le_trans hbb (le_trans (min_le_right _ _) (min_le_left _ _))
  have hb₃' : b ≤ b₃ := le_trans hbb (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨fits⟩ := hFits n μ.support R P μ k Λ b 𝒢 hfin
  obtain ⟨C, hC⟩ := hSel n μ.support R P μ k Λ b 𝒢
  have hCoh' := f₁ b hb hb₁' μ hfin hreg a ha R hR (d1ccomp_localADR_mono hADR hR₁) P 𝒢 hroot
    fits C hC
  have hHP' := f₂ b hb hb₂' μ hfin hreg a ha R hR (d1ccomp_localADR_mono hADR hR₂) P 𝒢 hroot
    fits C hC
  have hTime' := f₃ b hb hb₃' μ hfin hreg a ha R hR (d1ccomp_localADR_mono hADR hR₃) P 𝒢 hroot
    fits C hC
  have hCS := hCenter n μ.support R P μ k Λ b 𝒢 C hC
  have hRF := hRadius n μ.support R P μ k Λ b 𝒢 C hC
  have hAF := hAssign n μ.support R P μ k Λ b 𝒢 C hC
  have hFF := hFam n μ.support R P μ k Λ b 𝒢 fits C hC
  exact ⟨{
    tolerance_nonneg := ⟨hε.le, hε.le, hε.le, hε.le⟩
    centers := C.centers 𝒢
    isCompact_centers := hCS.isCompact_centers
    centers_nonempty := hCS.centers_nonempty
    centers_subset_closure := hCS.centers_subset_closure
    centers_subset := hCS.centers_subset
    radius := C.radius 𝒢
    radius_nonneg := hRF.radius_nonneg
    radius_le := hRF.radius_le
    core_eq := hRF.core_eq
    stop_separation := hRF.stop_separation
    core_separation := hRF.core_separation
    cutoff := hRF.cutoff
    assignment := C.assignment 𝒢
    measurable_assignment := hAF.measurable_assignment
    assignment_subset := hAF.assignment_subset
    assignment_disjoint := hAF.assignment_disjoint
    source_eq := hAF.source_eq
    family := C.family 𝒢 fits
    initialRadius_eq := hFF.initialRadius_eq
    initialPoint := (rootCenter 𝒢).1
    initialPoint_mem := hFF.initialPoint_mem
    initialPoint_near := hHP'.initialPoint_near
    center_mem := hHP'.center_mem
    coherent := hCoh'
    centerHeight := hHP'.centerHeight
    core_limit := hFF.core_limit
    stoppingParent := C.stoppingParent 𝒢
    stoppingParent_spec := hHP'.stoppingParent_spec
    timeCompatible := hTime'
    level_zero_plane := hFF.level_zero_plane
    initialPlane_fit := hFF.initialPlane_fit
    genuine_mem := hFF.genuine_mem
    genuine_scale := hFF.genuine_scale
    genuine_fit := hFF.genuine_fit }⟩

/-! ## Inputs to the partition energy bound -/

/-- `PointToFitStatement`, closed by its proof. -/
theorem d1ccomp_pointToFit : PartitionEnergy.PointToFitStatement :=
  PartitionEnergy.d1a_pointToFit_proof

/-- `PlaneComparisonStatement`, closed by its proofs. -/
theorem d1ccomp_planeComparison : PartitionEnergy.PlaneComparisonStatement :=
  PartitionEnergy.d1a_planeComparison_proof
    (PartitionEnergy.d1a_covarianceLower_proof PartitionEnergy.d1a_upperRecentering_proof)

/-! ## Closed statements -/

/-- `StopScaleZeroStatement`, closed through the ancestor and Lipschitz statements. -/
theorem d1ccomp_stopScaleZero : StopScaleZeroStatement :=
  d1c_stopScaleZero_proof d1c_ancestor_proof d1c_stopScaleLipschitz_proof

/-- `CutoffStatement`, closed. -/
theorem d1ccomp_cutoff : CutoffStatement :=
  d1c_cutoff_proof d1c_stopScaleLipschitz_proof

/-- **`OwnerStatement`, closed.** -/
theorem d1ccomp_owner : OwnerStatement :=
  d1c_owner_proof d1c_ancestor_proof d1c_stopScaleLipschitz_proof

/-- `LocalErrorStatement`, closed. -/
theorem d1ccomp_localError : LocalErrorStatement :=
  d1c_localError_proof d1ccomp_owner

/-- `ThinnessStatement`, closed. -/
theorem d1ccomp_thinness : ThinnessStatement :=
  d1c_thinness_proof d1ccomp_localError d1ccomp_pointToFit

/-- `RootThinnessStatement`, closed. -/
theorem d1ccomp_rootThinness : RootThinnessStatement :=
  d1c_rootThinness_proof d1ccomp_pointToFit

/-- `SelectionExistsStatement`, closed. -/
theorem d1ccomp_selectionExists : SelectionExistsStatement :=
  d1c_selectionExists_proof d1ccomp_cutoff

/-- `StageFactsStatement`, closed. -/
theorem d1ccomp_stageFacts : StageFactsStatement :=
  d1c_stageFacts_proof d1c_stopScaleLipschitz_proof d1ccomp_cutoff

/-- `AssignmentFieldsStatement`, closed. -/
theorem d1ccomp_assignmentFields : AssignmentFieldsStatement :=
  d1c_assignmentFields_proof d1c_stopScaleLipschitz_proof d1ccomp_stopScaleZero d1ccomp_cutoff
    d1ccomp_stageFacts

/-- `CoreEqualityStatement`, closed. -/
theorem d1ccomp_coreEquality : CoreEqualityStatement :=
  d1c_coreEquality_proof d1c_stopScaleLipschitz_proof d1ccomp_stopScaleZero d1ccomp_cutoff
    d1ccomp_stageFacts

/-- `CenterSetFieldsStatement`, closed. -/
theorem d1ccomp_centerSetFields : CenterSetFieldsStatement :=
  d1c_centerSetFields_proof d1c_ancestor_proof d1c_stopScaleLipschitz_proof d1ccomp_stopScaleZero
    d1ccomp_stageFacts d1ccomp_assignmentFields

/-- `RadiusFieldsStatement`, closed. -/
theorem d1ccomp_radiusFields : RadiusFieldsStatement :=
  d1c_radiusFields_proof d1c_stopScaleLipschitz_proof d1ccomp_stopScaleZero d1ccomp_cutoff
    d1ccomp_stageFacts

/-- `FamilyFieldsStatement`, closed. -/
theorem d1ccomp_familyFields : FamilyFieldsStatement :=
  d1c_familyFields_proof d1ccomp_stageFacts d1ccomp_coreEquality

/-- `HeightParentStatement`, closed. -/
theorem d1ccomp_heightParent : HeightParentStatement :=
  d1c_heightParent_proof d1ccomp_thinness d1ccomp_rootThinness d1ccomp_stageFacts

/-- `SameLevelStatement`, closed. -/
theorem d1ccomp_sameLevel : SameLevelStatement :=
  d1c_sameLevel_proof d1ccomp_localError d1ccomp_planeComparison

/-- `AdjacentLevelStatement`, closed. -/
theorem d1ccomp_adjacentLevel : AdjacentLevelStatement :=
  d1c_adjacentLevel_proof d1ccomp_localError d1ccomp_planeComparison

/-- `RootAdjacentStatement`, closed. -/
theorem d1ccomp_rootAdjacent : RootAdjacentStatement :=
  d1c_rootAdjacent_proof d1ccomp_localError d1ccomp_planeComparison

/-- `CoherenceStatement`, closed. -/
theorem d1ccomp_coherence : CoherenceStatement :=
  d1c_coherence_proof d1ccomp_sameLevel d1ccomp_adjacentLevel d1ccomp_rootAdjacent
    d1ccomp_rootThinness d1ccomp_stageFacts

/-- `FittedTimeStatement`, closed. -/
theorem d1ccomp_fittedTime : FittedTimeStatement :=
  d1c_fittedTime_proof d1ccomp_localError

/-- `GenuineTimeStatement`, closed. -/
theorem d1ccomp_genuineTime : GenuineTimeStatement :=
  d1c_genuineTime_proof d1c_localFits_proof d1ccomp_fittedTime d1ccomp_thinness
    d1ccomp_rootThinness d1ccomp_stageFacts

/-- `TimeCompatibleStatement`, closed. -/
theorem d1ccomp_timeCompatible : TimeCompatibleStatement :=
  d1c_timeCompatible_proof d1ccomp_genuineTime d1ccomp_rootThinness d1ccomp_stageFacts
    d1ccomp_coreEquality

/-- **The terminal construction** (`TerminalConstructionStatement`, the type of `d1_hub_terminalConstruction`), from
the proofs of its ingredients. -/
theorem d1ccomp_terminalConstruction : TerminalConstructionStatement :=
  d1ccomp_terminalConstruction_of d1c_localFits_proof d1ccomp_selectionExists
    d1ccomp_centerSetFields d1ccomp_radiusFields d1ccomp_assignmentFields
    d1ccomp_familyFields d1ccomp_coherence d1ccomp_heightParent
    d1ccomp_timeCompatible

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
