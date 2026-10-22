import ParabolicRectifiability.BetaP.Proofs.Counterexamples.TimeSliceHausdorffResult
import ParabolicRectifiability.Examples.Proofs.Reductions.TimeSlice

/-! # Transfer of the energies and Hausdorff measure through the time slice

`c2_timeSliceTransfer` proves `TimeSliceTransferStatement` (which is also the statement of
`timeSlice_transfer`): the `B_p` and `S_p` energies of a planar source and of its image under the
constant-time slice agree, and the slice carries Hausdorff measure to parabolic Hausdorff measure.

Assembly: `Plane` is `Spatial 2` and `timeSlice` is `fun x => point x 0`, so the `B_p` clause is
the identity `Examples.e2_timeSlice_betaPow` at `n = 2`, `k = 1`, `t₀ = 0`, and the `S_p` clause
is `Examples.e2_timeSlice_energies`; the Hausdorff clause is `c2_timeSlice_hausdorff`.
-/

open MeasureTheory

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Time-slice transfer**: the statement `TimeSliceTransferStatement` (the type of
`timeSliceTransfer_obligation` and `timeSlice_transfer`). -/
theorem c2_timeSliceTransfer : TimeSliceTransferStatement := by
  refine ⟨fun ν p hp T hT x => ?_, c2_timeSlice_hausdorff⟩
  have hβ : ∀ r : ℝ,
      betaPow (ν.map timeSlice) 1 T p (timeSlice x) r = euclideanBetaPow ν 1 p x r :=
    fun r => Examples.e2_timeSlice_betaPow 2 1 le_rfl (by norm_num) ν p hp 0 T hT x r
  exact ⟨hβ, fun a _ =>
    (Examples.e2_timeSlice_energies 2 1 le_rfl (by norm_num) ν p hp 0 T hT x a).1⟩

end ParabolicRectifiability.BetaP
