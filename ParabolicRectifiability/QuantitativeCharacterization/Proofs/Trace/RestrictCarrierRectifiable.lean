import ParabolicRectifiability.QuantitativeCharacterization.Statements.TraceComponents
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapters
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ADRHausdorffComparison

/-! # Reference-null transfer

Proof of `dp2_restrict_carrier_rectifiable`, whose statement is
`dp2_RestrictCarrierRectifiableStatement`.

Proof idea.
1. `b2_reference_adr_square` gives `c, C` with `IsADRCarrier k c C ρ.carrier ρ.measure` for
   every `L`-reference `ρ` (horizontal, vertical and ambient alike).
2. `b2_adr_hausdorff_comparison_proof k c C` gives `b` with `H_P^k(S ∩ Γ) ≤ b σ(S)` for every
   set `S`. So a `σ`-null `S` has `H_P^k(S ∩ Γ) = 0`, hence `μ(S ∩ Γ) = 0` by `μ ≪ H_P^k`, and
   `(μ⌊Γ)(S) = μ(S ∩ Γ)` since `Γ` is closed: `μ⌊Γ ≪ σ`.
3. The typed cover of `σ` at tolerance `1` is then a carrier of `μ⌊Γ` with the constant norm
   `fun _ => 1` (`dp2_t3_isCarried_of_typedMeasureCover`, split on the family kind).
4. `μ⌊Γ ≤ μ ≪ H_P^k`.

All helpers are prefixed `dp2_t3_`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- A typed measure cover of `σ` at tolerance `ε` carries every `ν ≪ σ`, with the constant
norm `ε`. -/
theorem dp2_t3_isCarried_of_typedMeasureCover {n k : ℕ} (T : FamilyKind)
    {σ ν : Measure (Space n)} {ε : ℝ} (hνσ : ν ≪ σ) (hcov : HasTypedMeasureCover T k σ ε) :
    IsCarriedByFiniteNormGraphs T k ν := by
  cases T with
  | horizontal =>
    obtain ⟨I, H, hH⟩ := hcov
    exact ⟨I, fun _ => ε, H, hνσ hH⟩
  | vertical =>
    obtain ⟨J, V, hV⟩ := hcov
    exact ⟨J, fun _ => ε, V, hνσ hV⟩
  | mixed =>
    obtain ⟨I, J, H, V, hHV⟩ := hcov
    exact ⟨I, J, fun _ => ε, H, fun _ => ε, V, hνσ hHV⟩

/-- **Reference-null transfer.** The type `dp2_RestrictCarrierRectifiableStatement`. -/
theorem dp2_restrict_carrier_rectifiable_proof : dp2_RestrictCarrierRectifiableStatement := by
  intro n hn k hk hkn L hL ρ hcov μ hμ
  obtain ⟨c, C, hadr⟩ := Characterization.b2_reference_adr_square n hn k hk hkn L hL
  obtain ⟨_a, b, _, _, hcmp⟩ := Characterization.b2_adr_hausdorff_comparison_proof k c C
  have hΓ : IsADRCarrier k c C ρ.carrier ρ.measure := (hadr ρ).1
  have hνσ : μ.restrict ρ.carrier ≪ ρ.measure := by
    intro S hS
    rw [Measure.restrict_apply' hΓ.isClosed.measurableSet]
    apply hμ
    have hle : hausdorffP n k (S ∩ ρ.carrier) ≤ ENNReal.ofReal b * ρ.measure S :=
      (hcmp n hn ρ.carrier ρ.measure hΓ S).2
    rw [hS, mul_zero] at hle
    exact nonpos_iff_eq_zero.1 hle
  exact ⟨(Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hμ,
    dp2_t3_isCarried_of_typedMeasureCover ρ.kind hνσ hcov⟩

end ParabolicRectifiability.QuantitativeCharacterization
