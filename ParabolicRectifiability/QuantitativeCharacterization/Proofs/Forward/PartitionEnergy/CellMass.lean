import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # ADR cell masses

For every direct partition of `supp μ` (any top scale), local ADR in `P(a, ρ)` and a cell `Q`
with centre in `P(a, ρ)` and `2 ℓ_Q ≤ ρ`: `A⁻¹ (ℓ_Q/4)^k ≤ μ(Q) ≤ A (2 ℓ_Q)^k`.
Route: `supp μ ∩ P(z_Q, ℓ_Q/4) ⊆ Q ⊆ P(z_Q, 2 ℓ_Q)`, `μ((supp μ)ᶜ) = 0` and
`z_Q ∈ supp μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

open ParabolicRectifiability.Foundations

/-- **ADR cell masses** (`CellMassStatement`). -/
theorem d1a_cellMass_proof : CellMassStatement := by
  intro n k μ A a ρ ℓ₀ P hADR Q hQ hQa h2ℓ
  have hℓ : 0 < P.scale Q.1 := by
    have h : 0 < ℓ₀ / 10 ^ Q.1 := div_pos P.scale_pos (by positivity)
    exact h
  have hz : Q.2 ∈ μ.support := P.center_subset Q.1 hQ
  have hmem : Q.2 ∈ μ.support ∩ Metric.ball a ρ := ⟨hz, hQa⟩
  constructor
  · -- lower bound: the quarter ball is, up to a null set, inside the cell
    have hs : (0 : ℝ) < P.scale Q.1 / 4 := by positivity
    have hsρ : P.scale Q.1 / 4 ≤ ρ := by linarith
    have hlow := (hADR Q.2 hmem (P.scale Q.1 / 4) hs hsρ).1
    have hsub : Metric.ball Q.2 (P.scale Q.1 / 4) ⊆ P.cellOf Q ∪ μ.supportᶜ := by
      intro x hx
      by_cases hxs : x ∈ μ.support
      · exact Or.inl (P.inner_subset Q.1 Q.2 hQ ⟨hxs, hx⟩)
      · exact Or.inr hxs
    calc ENNReal.ofReal (A⁻¹ * (P.scale Q.1 / 4) ^ k)
        ≤ μ (Metric.ball Q.2 (P.scale Q.1 / 4)) := hlow
      _ ≤ μ (P.cellOf Q ∪ μ.supportᶜ) := measure_mono hsub
      _ ≤ μ (P.cellOf Q) + μ μ.supportᶜ := measure_union_le _ _
      _ = μ (P.cellOf Q) := by rw [Measure.measure_compl_support, add_zero]
  · -- upper bound: the cell lies in the double ball
    have hs : (0 : ℝ) < 2 * P.scale Q.1 := by positivity
    have hup := (hADR Q.2 hmem (2 * P.scale Q.1) hs h2ℓ).2
    exact (measure_mono (P.cell_subset_ball Q.1 Q.2 hQ)).trans hup

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
