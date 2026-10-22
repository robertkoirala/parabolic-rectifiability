import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.DifferentiationComponents

/-! # Differentiation along nested partitions: assembly

The theorem `coordinate_differentiation_of_leaves` proves
`CoordinateDifferentiationStatement` (the statement used as `coordinate_differentiation`):
for a finite measure and exact nested Borel partitions with shrinking cells, the cell
averages of an integrable function converge to it almost everywhere.

Assembly: statement (i) (`b3_cd_cells`) gives the monotone partition filtration below the
ambient σ-algebra, the null union of zero-mass cells (first conclusion) and the
identification of the cell averages with the conditional expectations; statement (ii.a)
(`b3_cd_generation`) gives `⨆_j ℱ_j = m`; statement (ii.b) (`b3_cd_levy`, Lévy's upward
theorem) then gives the a.e. convergence of the cell averages (second conclusion). The cell
average `b3_cd_average ρ P h j z` unfolds to
`(ρ (partitionCell (P j) z)).toReal⁻¹ * ∫ x in partitionCell (P j) z, h x ∂ρ`. The isometric
embedding, the boundedness and measurability of `R`, inner regularity and `1 ≤ n` are not
used.
-/

noncomputable section

namespace ParabolicRectifiability.Characterization.CoordinateDifferentiationTree

/-- **Differentiation along nested partitions.** Cell averages along exact nested Borel
partitions with shrinking cells converge almost everywhere to the integrand, and the
zero-mass cells have null union; proved from `b3_cd_cells`, `b3_cd_generation` and
`b3_cd_levy`. -/
theorem coordinate_differentiation_of_leaves : CoordinateDifferentiationStatement := by
  intro n _hn Y _ _ _ _he R _hR _hRb ρ hρ _hreg hRc P hP hdiam h hh
  obtain ⟨hmono, hle, hnull, hid⟩ := b3_cd_cells Y R ρ hρ hRc P hP h hh
  exact ⟨hnull, b3_cd_levy Y ρ hρ (b3_cd_filtration P) hmono hle
    (b3_cd_generation Y R P hP hdiam) (b3_cd_average ρ P h) h hh (fun j => (hid j).2)⟩

end ParabolicRectifiability.Characterization.CoordinateDifferentiationTree
