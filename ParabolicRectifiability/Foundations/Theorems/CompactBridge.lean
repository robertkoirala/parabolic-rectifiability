import ParabolicRectifiability.Foundations.Statements.CompactBridge
import ParabolicRectifiability.Foundations.Proofs.CompactBridge

/-! # From the constructed regular class to the general regular class

The representative bridge identifies the existing componentwise `L²` half-time
derivative with the general homogeneous, ordered-window representation after
adding a constant. The function and graph-cover inclusions retain the same
Lipschitz and BMO bounds, hence lose no tolerance. The graph images and their
Hausdorff-null remainders are unchanged.

The exact contracts are `CompactBridgeRepresentativeStatement`, `CompactBridgeFunctionStatement`
and `CompactBridgeCoverStatement`; the analytic
identification is proved as `compactBridgeRepresentative_proof`. The general class uses zero-mean tests and does not
require compact support or global `L²` integrability of the full function.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace ParabolicRectifiability.Foundations

/-- Representative identification for the compact bridge. Statement:
`CompactBridgeRepresentativeStatement` (no compact-support or Lipschitz
hypothesis). The proof uses `|D_t|^{1/2}φ ∈ L¹`,
`∫ |D_t|^{1/2}φ = 0`, Fubini for the product-integrable pairing, which also yields the
inner and window integrability clauses, and the limit of the time windows.
It is the input of the two inclusions below. -/
theorem representsGeneralHalfTimeDerivative_of_compactPerturbation :
    CompactBridgeRepresentativeStatement := by
  exact ParabolicRectifiability.Foundations.compactBridgeRepresentative_proof

/-- Function inclusion at the same tolerance. The proof keeps the
same representative `g`, Lipschitz bound `L` and BMO bound `B`. It uses
`representsGeneralHalfTimeDerivative_of_compactPerturbation`. -/
theorem isGeneralRegularVerticalFunction_of_isRegularVerticalFunction :
    CompactBridgeFunctionStatement := by
  intro n W G ε h
  obtain ⟨c, H, g, L, B, hG, -, hL, hB, hrep, hle⟩ := h
  subst hG
  exact ⟨g, L, B, hL, hB,
    representsGeneralHalfTimeDerivative_of_compactPerturbation n W c H g hrep, hle⟩

/-- Cover inclusion without loss of tolerance. Each core graph
keeps its direction, offset and function. It uses
`representsGeneralHalfTimeDerivative_of_compactPerturbation`. -/
theorem hasGeneralRegularVerticalGraphCover_of_hasRegularVerticalGraphCover :
    CompactBridgeCoverStatement := by
  intro n k K ε h
  obtain ⟨I, G, hG⟩ := h
  refine ⟨I, fun i =>
    { vertical_dimension := (G i).vertical_dimension
      direction := (G i).direction
      rank_eq := (G i).rank_eq
      offset := (G i).offset
      function := (G i).function
      regular := isGeneralRegularVerticalFunction_of_isRegularVerticalFunction n
        (G i).direction (G i).function ε (G i).regular }, ?_⟩
  exact hG

end ParabolicRectifiability.Foundations
