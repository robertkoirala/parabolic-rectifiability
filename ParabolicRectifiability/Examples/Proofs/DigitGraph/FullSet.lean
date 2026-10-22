import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements

/-! # A common full set for predicates on the digit graph

A property holding at `T(x)` for almost every `x ∈ [0,1)` holds on a set of full measure for
the graph source `μ = T_#(L¹⌊[0,1))` (`e2_sb_fullSet_proof`). -/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane)

/-- Transfer a source almost-everywhere predicate to one full set in the plane.
The measurable null hull is taken in the source, and the graph locus retains
its source-domain condition. No measurability of the predicate is needed. -/
theorem e2_sb_fullSet_proof (hM : E2sbMeasurable) : E2sbFullSet := by
  intro P hP
  have hbad : volume {x : ℝ | x ∈ Ico (0 : ℝ) 1 ∧ ¬ P (e2_sbGraph x)} = 0 := by
    simpa only [not_imp] using (ae_iff.mp (ae_imp_of_ae_restrict hP))
  obtain ⟨N, hbadN, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  let G : Set Plane := {z | z 0 ∈ Ico (0 : ℝ) 1 \ N ∧ e2_sbGraph (z 0) = z}
  have hcoord : Measurable (fun z : Plane => z 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).measurable
  have hGm : MeasurableSet G :=
    ((measurableSet_Ico.diff hNm).preimage hcoord).inter
      (measurableSet_eq_fun (hM.2.2.comp hcoord) measurable_id)
  refine ⟨G, ?_, ?_⟩
  · rw [e2_sbSource, Measure.map_apply hM.2.2 hGm.compl,
      Measure.restrict_apply (hGm.compl.preimage hM.2.2)]
    apply measure_mono_null _ hN0
    intro x hx
    by_contra hxN
    apply hx.1
    change (e2_sbGraph x) 0 ∈ Ico (0 : ℝ) 1 \ N ∧
      e2_sbGraph ((e2_sbGraph x) 0) = e2_sbGraph x
    exact ⟨⟨hx.2, hxN⟩, rfl⟩
  · intro z hz
    by_contra hzP
    exact hz.1.2 (hbadN ⟨hz.1.1, fun hp => hzP (hz.2 ▸ hp)⟩)

end ParabolicRectifiability.Examples
