import ParabolicRectifiability.Foundations.Assembly.ProvedStatements

/-! # The compact bridge

The compact bridge rests on one statement, the representative identification
`representsGeneral_of_representsHalfTimeDerivative`. The function and cover inclusions are
derived from it (same representative, same Lipschitz and BMO bounds, same graphs), as in the
endpoint theorems for the compact bridge.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace ParabolicRectifiability.Foundations

/-- Representative identification for the compact bridge. -/
theorem compact_bridge_representative_skeleton : CompactBridgeRepresentativeStatement :=
  representsGeneral_of_representsHalfTimeDerivative

/-- Function inclusion at the same tolerance. -/
theorem compact_bridge_function_skeleton : CompactBridgeFunctionStatement := by
  intro n W G ε h
  obtain ⟨c, H, g, L, B, hG, -, hL, hB, hrep, hle⟩ := h
  subst hG
  exact ⟨g, L, B, hL, hB,
    representsGeneral_of_representsHalfTimeDerivative n W c H g hrep, hle⟩

/-- Cover inclusion without loss of tolerance. -/
theorem compact_bridge_cover_skeleton : CompactBridgeCoverStatement := by
  intro n k K ε h
  obtain ⟨I, G, hG⟩ := h
  refine ⟨I, fun i =>
    { vertical_dimension := (G i).vertical_dimension
      direction := (G i).direction
      rank_eq := (G i).rank_eq
      offset := (G i).offset
      function := (G i).function
      regular := compact_bridge_function_skeleton n
        (G i).direction (G i).function ε (G i).regular }, ?_⟩
  exact hG

end ParabolicRectifiability.Foundations
