import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces
import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitWitness
import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiability

/-! # The direct witness below two

Part (a) of the direct-witness theorem: the dispersed digit graph in the plane.
`c2_belowTwoDigitWitness_exists` constructs a set satisfying `IsBelowTwoDigitWitness`, and
`c2_belowTwoDigitWitness_pure_of_graphSource` shows that every such set is purely
unrectifiable and that its time slice meets every horizontal graph in an `H¹`-null set. These
are the statements `belowTwoDigitWitness_exists` and `belowTwoDigitWitness_pure_of_graphSource`.
The geometry of the example comes from the `Examples.e2_sb…` lemmas.
-/

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Existence of a digit witness below two.** The witness is
the dispersed digit graph `Examples.e2_sbSet`; its natural source `H¹⌊E` is rewritten to the
pushforward source `Examples.e2_sbSource`. -/
theorem c2_belowTwoDigitWitness_exists : ∃ E : Set Plane, IsBelowTwoDigitWitness E := by
  obtain ⟨hc, hm, hid⟩ := Examples.e2_sb_measureHub
  refine ⟨Examples.e2_sbSet, hc, hm, ?_, ?_, ?_⟩ <;> rw [hid]
  · exact Examples.e2_sb_densityHub
  · exact Examples.e2_sb_spHub
  · exact Examples.e2_sb_fullHub

/-- **Digit witnesses below two are purely unrectifiable.**
Graph-intersection nullity on the common divergence set of `IsBelowTwoDigitWitness` (graph-source
necessity, `Characterization.GraphSourceStatement`, through the time-slice transfer and
`S_2 = S`), then pure unrectifiability.
Of the transfer `hTS` only the energy clause (clause 1) is used; the Hausdorff
clause (clause 2) is **not** needed: the `H¹`-null rest `E \ G` has null image because the time
slice is an isometry. -/
theorem c2_belowTwoDigitWitness_pure_of_graphSource (hGS : Characterization.GraphSourceStatement)
    (hTS : TimeSliceTransferStatement) (hE2 : EnergyTwoStatement) {E : Set Plane}
    (hE : IsBelowTwoDigitWitness E) :
    IsPurelyUnrectifiable E ∧
      ∀ (ε : ℝ) (G : HorizontalGraph 2 1 ε), hausdorffP 2 1 (timeSlice '' E ∩ G.image) = 0 := by
  obtain ⟨hc, hm, -, -, G, hG, hGdiv⟩ := hE
  have hnull : ∀ (ε : ℝ) (Γ : HorizontalGraph 2 1 ε),
      hausdorffP 2 1 (timeSlice '' E ∩ Γ.image) = 0 :=
    Examples.e2_sb_witnessGraphNull hGS hTS hE2 hc.isClosed.measurableSet
      (by rw [hm]; exact ENNReal.one_ne_top) hG (fun z hz => (hGdiv z hz).1)
  exact ⟨Examples.e2_sb_witnessPure E hnull, hnull⟩

end ParabolicRectifiability.BetaP
