import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityLemmas

/-! # Graph-intersection nullity and pure one-unrectifiability for the digit graph

Graph-intersection nullity and pure one-unrectifiability of a planar set carrying the
divergence conclusion (infinite square function `S_2` at every scale endpoint, almost
everywhere). The theorems here are applied to `IsBelowTwoDigitWitness`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.BetaP (Plane timeSlice IsPurelyUnrectifiable)

/-- **Graph-intersection nullity.** If `E` is Borel with
`H¹(E) < ∞`, and `S_{2,λ}^{a,E} = ∞` for every `a > 0` on a set `G` of full `λ = H¹⌊E` measure,
then `ι(E)` meets every horizontal graph of every finite slope in an `H_P^1`-null set: on
`E ∩ G` by graph-source necessity (`E2sbSliceGraphNull`), on the `H¹`-null rest `E \ G` by
`E2sbSliceHausdorff`. -/
theorem e2_sb_witnessGraphNull (hGS : Characterization.GraphSourceStatement)
    (hTS : BetaP.TimeSliceTransferStatement) (hE2 : EnergyTwoStatement) {E : Set Plane}
    (hEm : MeasurableSet E) (hEfin : μH[1] E ≠ ⊤) {G : Set Plane}
    (hG : μH[1].restrict E Gᶜ = 0)
    (hdiv : ∀ z ∈ G, ∀ a : ℝ, 0 < a → euclideanEnergyS (μH[1].restrict E) 1 2 a z = ⊤)
    (ε : ℝ) (Γ : HorizontalGraph 2 1 ε) :
    hausdorffP 2 1 (timeSlice '' E ∩ Γ.image) = 0 := by
  have : IsFiniteMeasure (μH[1].restrict E) := isFiniteMeasure_restrict.mpr hEfin
  have h₁ : hausdorffP 2 1 (timeSlice '' (E ∩ G) ∩ Γ.image) = 0 :=
    e2_sb_sliceGraphNull hGS hTS hE2 e2_sb_sliceSource (μH[1].restrict E) inferInstance (E ∩ G)
      (fun z hz => hdiv z hz.2 1 one_pos) ε Γ
  have h₂ : hausdorffP 2 1 (timeSlice '' (E \ G)) = 0 := by
    rw [e2_sb_sliceHausdorff (E \ G)]
    rw [Measure.restrict_apply' hEm] at hG
    rwa [Set.sdiff_eq, Set.inter_comm]
  refine measure_mono_null ?_ (measure_union_null h₁ h₂)
  rintro _ ⟨⟨x, hxE, rfl⟩, hxΓ⟩
  by_cases hxG : x ∈ G
  · exact Or.inl ⟨⟨x, ⟨hxE, hxG⟩, rfl⟩, hxΓ⟩
  · exact Or.inr ⟨x, ⟨hxE, hxG⟩, rfl⟩

/-- **Pure one-unrectifiability** `E2sbPurity` from its six inputs. -/
theorem e2_sb_witnessPure : E2sbPurity :=
  e2_sb_purity e2_sb_sliceHausdorff e2_sb_lipschitzExtend e2_sb_lipschitzNondiff
    e2_sb_zeroDerivImage e2_sb_smallSlopePieces e2_sb_slopeGraph

end ParabolicRectifiability.Examples
