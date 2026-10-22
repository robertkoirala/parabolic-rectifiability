import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceBasic

/-! # Support and carrier of the typed references

Proves `b2_reference_support_carrier_proof` (the statement of `b2_reference_support_carrier`).
For every typed `L`-reference `ρ`, `supp σ = Γ` and `Γ ≠ ∅`:
* horizontal: `Γ = supp σ` by definition, and `σ ≠ 0` because `(F,T)` is Borel
  (`b1basic_measurable_map`) and `σ(X) = L^k(ℝ^k)`;
* vertical: `supp σ = im Φ` (`b1basic_vertical_support`), and the range is nonempty;
* ambient: `supp L^{n+1} = X` (`b1basic_parabolicVolume_support`).

No hypothesis on `L` is needed: the helpers use no sign condition on `L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- **Support of a typed reference.** For every typed `L`-reference with measure `σ` and carrier
`Γ`, `supp σ = Γ` and `Γ` is nonempty (the statement of `b2_reference_support_carrier`). -/
theorem b2_reference_support_carrier_proof :
    ∀ (n k : ℕ) (L : ℝ) (ρ : Reference n k L),
      ρ.measure.support = ρ.carrier ∧ ρ.carrier.Nonempty := by
  intro n k L ρ
  cases ρ with
  | horizontal H =>
    exact ⟨rfl, Measure.nonempty_support (b1basic_horizontal_measure_ne_zero H)⟩
  | vertical V =>
    exact ⟨b1basic_vertical_support V, ⟨V.map (point 0 0), mem_range_self _⟩⟩
  | ambient _ =>
    exact ⟨b1basic_parabolicVolume_support n, ⟨point 0 0, mem_univ _⟩⟩

end ParabolicRectifiability.Characterization
