import ParabolicRectifiability.BetaP.Statements.Failures

/-! # Statement of the Hausdorff time-slice pushforward

The named statement `C2TimeSliceHausdorffStatement` (a proposition only), used to prove
`TimeSliceTransferStatement`. It is proved by `c2_timeSlice_hausdorff` and used in
`c2_timeSliceTransfer`.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.BetaP

/-- **Hausdorff pushforward of the time slice** (`c2_timeSlice_hausdorff`). The isometric
Hausdorff pushforward of the constant-time slice, with coefficient one:
`ι_#(H¹⌊E) = H_P^1⌊ι(E)` for every Borel `E ⊆ ℝ²`. This is the second clause of
`TimeSliceTransferStatement`. -/
def C2TimeSliceHausdorffStatement : Prop :=
  ∀ E : Set Plane, MeasurableSet E →
    (μH[1].restrict E).map timeSlice = (hausdorffP 2 1).restrict (timeSlice '' E)

end ParabolicRectifiability.BetaP
