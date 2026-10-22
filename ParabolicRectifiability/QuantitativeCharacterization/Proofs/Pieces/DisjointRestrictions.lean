import ParabolicRectifiability.QuantitativeCharacterization.Statements.PiecesComponents

/-! # Disjoint Borel restrictions

Proof of `dp2_DisjointRestrictionStatement`, the type of
`dp2_disjoint_restrictions`. Proof idea: `E = disjointed B`;
`μ = μ⌊⋃ E` because `⋃ E = ⋃ B` is conull; then `Measure.restrict_iUnion`. No Radon assumption. -/

open MeasureTheory

namespace ParabolicRectifiability.QuantitativeCharacterization

theorem dp2_disjoint_restrictions_proof : dp2_DisjointRestrictionStatement := by
  intro n μ B hB hnull
  refine ⟨disjointed B, MeasurableSet.disjointed hB, disjoint_disjointed B, disjointed_subset B, ?_⟩
  have hae : (⋃ j, B j) ∈ MeasureTheory.ae μ := mem_ae_iff.2 hnull
  have h1 : μ.restrict (⋃ j, disjointed B j) = μ := by
    rw [iUnion_disjointed]
    exact Measure.restrict_eq_self_of_ae_mem hae
  calc μ = μ.restrict (⋃ j, disjointed B j) := h1.symm
    _ = Measure.sum (fun j => μ.restrict (disjointed B j)) :=
        Measure.restrict_iUnion (disjoint_disjointed B) (MeasurableSet.disjointed hB)

end ParabolicRectifiability.QuantitativeCharacterization
