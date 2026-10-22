import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # The slab families are Borel subsets of the tested pairs

Proves `SlabBasicsStatement → SlabFamilyStatement`, with `SlabBasicsStatement` as an implication
hypothesis. Bad cells and region members are cells (`bad_forest`, `below_root`), hence countably
many; then `MeasurableSet.biUnion` and `iUnion₂_subset`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- A union of slabs over a set `T` of cell addresses is Borel and lies in the tested pairs. -/
theorem d1fsfam_union (hB : SlabBasicsStatement) {n : ℕ} (μ : MeasureTheory.Measure (Space n))
    (a : Space n) (R : ℝ) (P : DirectPartition μ.support R) (T : Set (ℕ × Space n))
    (hT : ∀ Q ∈ T, P.IsCell Q) :
    MeasurableSet (⋃ Q ∈ T, slab P a R Q) ∧ (⋃ Q ∈ T, slab P a R Q) ⊆ rootPairs μ a R := by
  obtain ⟨hc, hm, hs⟩ := hB n μ a R P
  exact ⟨MeasurableSet.biUnion (hc.mono hT) (fun Q _ => hm Q),
    iUnion₂_subset (fun Q hQ => hs Q (hT Q hQ))⟩

/-- **Slab families**: the slab families are Borel subsets of the tested pairs (implication form
over `SlabBasicsStatement`). -/
theorem d1f_slabFamily_proof : SlabBasicsStatement → SlabFamilyStatement := by
  intro hB n μ a R P k Λ b K SD
  have hbad : ∀ Q ∈ SD.bad, P.IsCell Q := by
    intro Q hQ
    obtain ⟨z₀, _, _, hb⟩ := SD.bad_forest Q hQ
    exact hb.1
  have hgood : ∀ S : SD.roots, ∀ Q ∈ (SD.region S).members, P.IsCell Q := by
    intro S Q hQ
    exact ((SD.region S).below_root Q hQ).1
  obtain ⟨h1, h2⟩ := d1fsfam_union hB μ a R P SD.bad hbad
  refine ⟨h1, fun S => (d1fsfam_union hB μ a R P _ (hgood S)).1, h2,
    fun S => (d1fsfam_union hB μ a R P _ (hgood S)).2⟩

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
