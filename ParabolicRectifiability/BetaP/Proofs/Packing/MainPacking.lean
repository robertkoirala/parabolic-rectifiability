import ParabolicRectifiability.BetaP.Proofs.Support.IntermediateStatements
import ParabolicRectifiability.Measure.Neck.LocalStatements

/-! # The five active-radius packing statements

The quadratic discrete packing theorem is `discrete_packing_proof`, applied directly. The
bootstrap `activeRadiusPacking_of_discretePacking` and the variants
`activeRadiusPacking_variants` give the five statements below. No statement from outside the
`BetaP` development is used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

/-- The quadratic discrete theorem feeds the bootstrap: one constant for the full-source and
the truncated active-radius bounds. -/
theorem activeRadiusPacking_bounds (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ActiveRadiusPackingBound n p C ∧ ActiveRadiusPackingTruncatedBound n p C := by
  obtain ⟨C₀, hC₀, hdisc⟩ := discrete_packing_proof n
  exact activeRadiusPacking_of_discretePacking n hn p hp C₀ hC₀ hdisc

/-- Active-radius packing: the main assertion. -/
theorem activeRadiusPacking_skeleton : ActiveRadiusPackingStatement := by
  intro n hn p hp
  obtain ⟨C, hC, h, -⟩ := activeRadiusPacking_bounds n hn p hp
  exact ⟨C, hC, h⟩

/-- Active-radius packing with truncated testing sources. -/
theorem activeRadiusPacking_truncated_skeleton : ActiveRadiusPackingTruncatedStatement := by
  intro n hn p hp
  obtain ⟨C, hC, -, h⟩ := activeRadiusPacking_bounds n hn p hp
  exact ⟨C, hC, h⟩

/-- Active-radius packing in a unit parent, with endpoint two. -/
theorem activeRadiusPacking_unitParent_skeleton : ActiveRadiusPackingUnitParentStatement := by
  intro n hn p hp
  obtain ⟨C, hC, h, -⟩ := activeRadiusPacking_bounds n hn p hp
  obtain ⟨C', hC', hu, -, -⟩ := activeRadiusPacking_variants n hn p hp C hC h
  exact ⟨C', hC', hu⟩

/-- Active-radius packing with exceptional indices. -/
theorem activeRadiusPacking_exceptional_skeleton : ActiveRadiusPackingExceptionalStatement := by
  intro n hn p hp
  obtain ⟨C, hC, h, -⟩ := activeRadiusPacking_bounds n hn p hp
  obtain ⟨C', hC', -, he, -⟩ := activeRadiusPacking_variants n hn p hp C hC h
  exact ⟨C', hC', he⟩

/-- Active-radius packing with exceptional indices, in the unit-parent form. -/
theorem activeRadiusPacking_unitParent_exceptional_skeleton :
    ActiveRadiusPackingUnitParentExceptionalStatement := by
  intro n hn p hp
  obtain ⟨C, hC, h, -⟩ := activeRadiusPacking_bounds n hn p hp
  obtain ⟨C', hC', -, -, hue⟩ := activeRadiusPacking_variants n hn p hp C hC h
  exact ⟨C', hC', hue⟩

end ParabolicRectifiability.BetaP
