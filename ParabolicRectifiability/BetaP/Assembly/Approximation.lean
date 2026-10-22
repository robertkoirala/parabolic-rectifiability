import ParabolicRectifiability.BetaP.Assembly.AssemblyStatements

/-! # Compact inner approximation of a typing

Proof of `CasmCompactApproximationStatement`: finite inner regularity on the two Borel typed
pieces with loss `ε/2` each, then `K = H ∪ V` and `measure_union_le` (as in
`compactTypedPieces_exists`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- Compact inner approximation of one Borel set of a finite inner-regular measure with loss
`ε / 2` (Mathlib `MeasurableSet.exists_isCompact_diff_lt`). -/
theorem casm1_exists_isCompact_subset_sdiff_le {n : ℕ} (ν : Measure (Space n))
    [IsFiniteMeasure ν] [ν.InnerRegular] {A : Set (Space n)} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B, B ⊆ A ∧ IsCompact B ∧ ν (A \ B) ≤ ENNReal.ofReal (ε / 2) := by
  obtain ⟨B, hBA, hB, hlt⟩ := hA.exists_isCompact_sdiff_lt (measure_ne_top ν A)
    (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  exact ⟨B, hBA, hB, hlt.le⟩

/-- **Compact inner approximation of a typing** (`CasmCompactApproximationStatement`). -/
theorem casm_compactApproximation_proof : CasmCompactApproximationStatement := by
  intro n k T ν hfin hreg K D ε hε
  obtain ⟨AH, hAH, hAHc, hAHl⟩ :=
    casm1_exists_isCompact_subset_sdiff_le ν D.measurable_horizontal hε
  obtain ⟨AV, hAV, hAVc, hAVl⟩ :=
    casm1_exists_isCompact_subset_sdiff_le ν D.measurable_vertical hε
  refine ⟨AH, AV, hAHc, hAVc, hAH, hAV, ?_⟩
  calc
    ν (K \ (AH ∪ AV)) ≤ ν ((D.horizontal \ AH) ∪ (D.vertical \ AV)) := by
      apply measure_mono
      rintro x ⟨hxK, hxA⟩
      rw [← D.union_eq] at hxK
      rcases hxK with hx | hx
      · exact Or.inl ⟨hx, fun h => hxA (Or.inl h)⟩
      · exact Or.inr ⟨hx, fun h => hxA (Or.inr h)⟩
    _ ≤ ν (D.horizontal \ AH) + ν (D.vertical \ AV) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hAHl hAVl
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves]

end ParabolicRectifiability.BetaP
