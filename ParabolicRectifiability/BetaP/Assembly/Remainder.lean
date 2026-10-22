import ParabolicRectifiability.BetaP.Assembly.AssemblyStatements

/-! # Remainder bookkeeping

Proof of `CasmRemainderStatement`: a point of
`P(0,1)` outside `E_H ∪ E_V` is either bad (`S_{p,μ}^2 > M`) or good, hence in some `region_i`
(`S.cover`) and outside `A_H i ∪ A_V i`; then outer-measure subadditivity (as in
`GoodSourceLocalization.remainder_le`). No
measurability of `A_T i` and no sign assumptions on `Γ`, `ℓ` are used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Remainder bookkeeping** (`CasmRemainderStatement`). -/
theorem casm_remainder_proof : CasmRemainderStatement := by
  intro n k N T p M μ S AH AV Γ ℓ hbad hloss
  have hsub : Metric.ball (point 0 0) 1 ∩
        ((⋃ i, S.region i ∩ AH i) ∪ ⋃ i, S.region i ∩ AV i)ᶜ ⊆
      (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ∪
        ⋃ i, S.region i ∩ (AH i ∪ AV i)ᶜ := by
    rintro z ⟨hzB, hzHV⟩
    by_cases hz : ENNReal.ofReal M < energyS μ k T p 2 z
    · exact Or.inl ⟨hzB, hz⟩
    · have hgood : z ∈ pGoodSet μ k T p M := ⟨hzB, not_lt.mp hz⟩
      rw [← S.cover] at hgood
      obtain ⟨i, hi⟩ := mem_iUnion.mp hgood
      refine Or.inr (mem_iUnion.mpr ⟨i, hi, fun hzhv => hzHV ?_⟩)
      rcases hzhv with h | h
      · exact Or.inl (mem_iUnion.mpr ⟨i, hi, h⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨i, hi, h⟩)
  have hpiece : ∀ i, μ (S.region i ∩ (AH i ∪ AV i)ᶜ) ≤ ENNReal.ofReal ℓ := by
    intro i
    have h := hloss i
    rwa [Measure.restrict_apply' (S.measurable i), inter_comm] at h
  calc
    _ ≤ μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) +
          μ (⋃ i, S.region i ∩ (AH i ∪ AV i)ᶜ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal Γ + ∑ _i : Fin S.count, ENNReal.ofReal ℓ :=
        add_le_add hbad
          ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => hpiece i))

end ParabolicRectifiability.BetaP
