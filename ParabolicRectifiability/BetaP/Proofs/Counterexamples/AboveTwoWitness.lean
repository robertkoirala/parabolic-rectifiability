import ParabolicRectifiability.BetaP.Statements.Failures
import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentWitness

/-! # The direct witness above two

`c2_directWitnessPlus` proves `DirectWitnessPlusStatement`, part (b) of the direct-witness
theorem: a planar set built from decorated horizontal segments whose Hausdorff source exhibits
the failure above the quadratic exponent. It is the statement used by
`directWitnessPlus_obligation` and `directWitness_plus`. All the geometry of the example is
taken from the `Examples.e2_sap…` lemmas; this file only assembles the clauses.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.BetaP

/-- **Direct witness above two.** The witness is the
decorated-segment set `Examples.e2_sapSet`, indexed by the codes of valid labels; the exceptional
set is the endpoint set `Examples.e2_sapEndpoints`. -/
theorem c2_directWitnessPlus : DirectWitnessPlusStatement := by
  obtain ⟨hmeas, hbdd⟩ := Examples.e2_sap_basicHub
  obtain ⟨hlow, hup⟩ := Examples.e2_sap_massHub
  refine ⟨Examples.e2_sapSet, hmeas, hbdd,
    ⟨Examples.e2_sapIndex, fun i => Examples.e2_sapLeft i, fun i => Examples.e2_sapRight i,
      fun i => Examples.e2_sapHeight i, fun i => (Examples.e2_sap_labelHub i i.2).1, rfl⟩,
    hlow, hup, ?_,
    ⟨Examples.e2_sapEndpoints, Examples.e2_sapEndpoints_countable,
      Examples.e2_sap_divergenceHub⟩,
    Examples.e2_sap_coverHub⟩
  exact Examples.e2_sap_densityHub Examples.e2_sapIndex (fun i => Examples.e2_sapLeft i)
    (fun i => Examples.e2_sapRight i) (fun i => Examples.e2_sapHeight i)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup)

end ParabolicRectifiability.BetaP
