import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # Measurability of the dispersed digit graph

The marked sets are inverse images under the measurable integer-valued floor map.
Countable sums of real-valued measurable functions are measurable, including the
zero value assigned by `tsum` outside its convergence set.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Examples

/-- The marked sets, the height sum, and the graph map are Borel measurable. -/
theorem e2_sb_measurable_proof : E2sbMeasurable := by
  have hmarked (j : ℕ) : MeasurableSet (e2_sbMarked j) := by
    exact ((measurable_id.div_const (e2_sbEll j)).floor)
      (to_countable {k : ℤ | ((j + 1 : ℕ) : ℤ) ∣ k}).measurableSet
  have hbit (j : ℕ) : Measurable (e2_sbBit j) :=
    measurable_const.indicator (hmarked j)
  have hheight : Measurable e2_sbHeight :=
    Measurable.tsum (fun i => (hbit (i + 1)).const_mul (e2_sbH (i + 1)))
  refine ⟨hmarked, hheight, ?_⟩
  unfold e2_sbGraph
  apply (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
  refine measurable_pi_iff.mpr ?_
  intro i
  fin_cases i
  · exact measurable_id
  · exact hheight

end ParabolicRectifiability.Examples
