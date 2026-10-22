import ParabolicRectifiability.Characterization.Statements.SourceTransfer
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.Bases

/-! # Fivefold ball selection

Vitali fivefold selection for bounded-radius families of open balls in a separable metric
space: Mathlib's `Vitali.exists_disjoint_subfamily_covering_enlargement_ball` with `t = univ`
and `τ = 5`, then countability of the pairwise disjoint family of nonempty open balls in a
separable space. -/

namespace ParabolicRectifiability.Characterization

/-- `FivefoldSelectionStatement`, proved by Vitali's covering theorem. -/
theorem fivefold_ball_selection_proof : FivefoldSelectionStatement := by
  intro X _ _ ι z r hr hR
  obtain ⟨R, hR⟩ := hR
  obtain ⟨u, -, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball (Set.univ : Set ι) z r R
      (fun a _ => hR a) 5 (by norm_num)
  refine ⟨u, ?_, hdisj, ?_⟩
  · exact hdisj.countable_of_isOpen (fun i _ => Metric.isOpen_ball)
      (fun i _ => Metric.nonempty_ball.2 (hr i))
  · intro i
    obtain ⟨b, hb, hsub⟩ := hcov i (Set.mem_univ i)
    exact ⟨b, hb, hsub (Metric.mem_ball_self (hr i))⟩

end ParabolicRectifiability.Characterization
