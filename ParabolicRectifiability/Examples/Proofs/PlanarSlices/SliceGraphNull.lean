import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements
import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.BetaP.Statements.Failures
import ParabolicRectifiability.Foundations.Statements.Measurability

/-! # Graph nullity of the time-zero image where the quadratic energy diverges

For a finite planar measure `ν` and a set `S` on which the planar energy `S_{2,ν}^{1,E}` is
infinite, the time-zero image `ι(S)` meets every horizontal graph of finite slope in an
`H_P^1`-null set (`e2_sb_sliceGraphNull_proof`). The divergence is transferred to the slice
by `BetaP.TimeSliceTransferStatement` and `EnergyTwoStatement`, and graph necessity
(`Characterization.GraphSourceStatement`) is applied to the slice source. -/

noncomputable section
open MeasureTheory Set
namespace ParabolicRectifiability.Examples
open Foundations BetaP

/-- Transfer quadratic divergence, then apply full-source graph necessity. -/
theorem e2_sb_sliceGraphNull_proof (hGS : Characterization.GraphSourceStatement)
    (hTS : BetaP.TimeSliceTransferStatement) (hE2 : EnergyTwoStatement)
    (hSrc : E2sbSliceSource) : E2sbSliceGraphNull := by
  intro ν hν S hS ε Γ
  obtain ⟨hfinite, hinner⟩ := hSrc ν hν
  have hnull := (hGS 2 (by norm_num) 1 (by norm_num) (by norm_num)).1
    ε Γ (ν.map timeSlice) hfinite hinner 1 (by norm_num)
  apply measure_mono_null (t := Γ.image ∩
    {z | squareEnergy (ν.map timeSlice) 1 .horizontal 1 z = ⊤}) ?_ hnull
  rintro z ⟨⟨x, hx, rfl⟩, hΓ⟩
  refine ⟨hΓ, ?_⟩
  have htransfer := (hTS.1 ν 2 (by norm_num) .horizontal (Or.inl rfl) x).2
    1 (by norm_num)
  have htwo := (hE2 2 (by norm_num) 1 (by norm_num) (by norm_num)
    .horizontal (ν.map timeSlice) 1 (by norm_num) (timeSlice x)).1
  exact htwo.symm.trans (htransfer.trans (hS x hx))

end ParabolicRectifiability.Examples
