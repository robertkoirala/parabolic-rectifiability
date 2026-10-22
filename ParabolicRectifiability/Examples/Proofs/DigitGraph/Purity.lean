import ParabolicRectifiability.Examples.Proofs.DigitGraph.PureUnrectifiabilityStatements

/-! # Pure unrectifiability from horizontal graph nullity

Extend each Lipschitz parametrization to the real line. Its nondifferentiability and
zero-derivative images are null. The remaining parameters lie in countably many
small-slope pieces, whose images embed into horizontal graphs at time zero.
The slice Hausdorff identity transfers graph nullity back to the plane.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane timeSlice IsPurelyUnrectifiable)

/-- Graph-intersection nullity implies pure one-unrectifiability, using the six
curve and slice statements with their full arbitrary-set quantifiers. -/
theorem e2_sb_purity_proof (hH : E2sbSliceHausdorff) (hX : E2sbLipschitzExtend)
    (hN : E2sbLipschitzNondiff) (hZ : E2sbZeroDerivImage) (hP : E2sbSmallSlopePieces)
    (hG : E2sbSlopeGraph) : E2sbPurity := by
  classical
  intro E hE A f K hf
  obtain ⟨F, K', hF, hFf⟩ := hX A f K hf
  obtain ⟨P, V, hV, hcover, hslope⟩ := hP F 1 zero_lt_one
  have hpiece (i : ℕ) : μH[1] (E ∩ F '' P i) = 0 := by
    obtain ⟨Γ, hΓ⟩ := hG (F '' P i) (V i) 1 (hV i) zero_le_one (by
      rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
      exact hslope i t ht s hs)
    rw [← hH (E ∩ F '' P i)]
    apply measure_mono_null _ (hE 1 Γ)
    rintro z ⟨x, ⟨hxE, hxP⟩, rfl⟩
    exact ⟨⟨x, hxE, rfl⟩, hΓ ⟨x, hxP, rfl⟩⟩
  have hpieces : μH[1] (⋃ i, E ∩ F '' P i) = 0 := measure_iUnion_null hpiece
  have hbad : μH[1] (F '' {s | ¬ DifferentiableAt ℝ F s} ∪
      F '' {s | HasDerivAt F 0 s} ∪ ⋃ i, E ∩ F '' P i) = 0 :=
    measure_union_null (measure_union_null (hN F K' hF) (hZ F)) hpieces
  apply measure_mono_null _ hbad
  rintro x ⟨hxE, s, hsA, hsf⟩
  have hsF : F s = x := (hFf hsA).trans hsf
  by_cases hd : DifferentiableAt ℝ F s
  · by_cases hz : deriv F s = 0
    · exact Or.inl (Or.inr ⟨s, by
        change HasDerivAt F 0 s
        simpa only [hz] using hd.hasDerivAt, hsF⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨deriv F s, hz, hd.hasDerivAt⟩)
      exact Or.inr (mem_iUnion.mpr ⟨i, hxE, s, hi, hsF⟩)
  · exact Or.inl (Or.inl ⟨s, hd, hsF⟩)

end ParabolicRectifiability.Examples
