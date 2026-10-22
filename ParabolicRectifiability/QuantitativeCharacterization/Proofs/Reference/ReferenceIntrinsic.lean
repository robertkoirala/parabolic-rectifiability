import ParabolicRectifiability.Foundations.Carriers
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapters
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ADRHausdorffComparison

/-! # Intrinsic properties of references from the reference ADR comparison

Proof of `reference_intrinsic_of_estimates`, restated here with its type (so that this file does
not depend on the module in which that statement is declared).

Proof idea. `b2_reference_adr_square` gives, for every reference `ρ`, an
`IsADRCarrier k c C ρ.carrier ρ.measure` with `c, C` depending only on `(n, k, L)` and the
a.e. finiteness of the own-type square at radius `1`. The ADR hypothesis and the energy bound of
the statement are not needed. Local finiteness and inner regularity are fields of
`IsADRCarrier`. `b2_adr_hausdorff_comparison_proof` gives `σ S ≤ a H_P^k(S ∩ Γ)`, hence
`σ ≪ H_P^k`, and `H_P^k(S ∩ Γ) ≤ b σ S`, hence `H_P^k` is finite on the compact pieces
`Γ ∩ closedBall z₀ j`, which are Borel and carry `σ` because `σ Γᶜ = 0`.

All helpers are prefixed `dp2_`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.Characterization

/-- The reference measure does not charge the complement of its carrier. -/
theorem dp2_measure_compl {n k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hσ : IsADRCarrier k c C Γ σ) : σ Γᶜ = 0 := by
  rw [← hσ.support_eq]
  exact Measure.measure_compl_support

/-- An ADR carrier measure is absolutely continuous with respect to `H_P^k` and has a Borel
sigma-finite `H_P^k` carrier, given the comparison constants. -/
theorem dp2_intrinsic_of_carrier {n : ℕ} (_hn : 1 ≤ n) {k : ℕ} {c C : ℝ} {Γ : Set (Space n)}
    {σ : Measure (Space n)} (hσ : IsADRCarrier k c C Γ σ) {a b : ℝ}
    (hcmp : ∀ S : Set (Space n),
        σ S ≤ ENNReal.ofReal a * hausdorffP n k (S ∩ Γ) ∧
          hausdorffP n k (S ∩ Γ) ≤ ENNReal.ofReal b * σ S) :
    σ ≪ hausdorffP n k ∧ HasBorelSigmaFiniteHausdorffCarrier k σ := by
  refine ⟨?_, ?_⟩
  · intro S hS
    have h1 := (hcmp S).1
    have h2 : hausdorffP n k (S ∩ Γ) = 0 :=
      measure_mono_null Set.inter_subset_left hS
    rw [h2, mul_zero] at h1
    exact nonpos_iff_eq_zero.1 h1
  · have : IsFiniteMeasureOnCompacts σ := hσ.finiteOnCompacts
    obtain ⟨z₀, hz₀⟩ := hσ.nonempty
    refine ⟨fun j => Γ ∩ Metric.closedBall z₀ (j : ℝ), fun j => ?_, fun j => ?_, ?_⟩
    · exact hσ.isClosed.measurableSet.inter Metric.isClosed_closedBall.measurableSet
    · have hfin : σ (Γ ∩ Metric.closedBall z₀ (j : ℝ)) < ⊤ :=
        lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (isCompact_closedBall z₀ (j : ℝ)).measure_lt_top
      have hle := (hcmp (Γ ∩ Metric.closedBall z₀ (j : ℝ))).2
      have hsub : (Γ ∩ Metric.closedBall z₀ (j : ℝ)) ∩ Γ = Γ ∩ Metric.closedBall z₀ (j : ℝ) := by
        ext x; simp only [mem_inter_iff]; tauto
      rw [hsub] at hle
      exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
    · refine measure_mono_null ?_ (dp2_measure_compl hσ)
      intro x hx hxΓ
      obtain ⟨j, hj⟩ := exists_nat_ge (dist x z₀)
      exact hx (mem_iUnion.2 ⟨j, hxΓ, Metric.mem_closedBall.2 hj⟩)

/-- **Intrinsic properties of references**: the type of `reference_intrinsic_of_estimates`. -/
theorem dp2_referenceIntrinsic_proof :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L → ∀ A C : ℝ,
    ∀ ρ : Reference n k L, IsADR A k ρ.measure → referenceEnergy ρ ≤ ENNReal.ofReal C →
      IsFiniteMeasureOnCompacts ρ.measure ∧ ρ.measure.InnerRegular ∧
        ρ.measure ≪ hausdorffP n k ∧ HasBorelSigmaFiniteHausdorffCarrier k ρ.measure ∧
        ∃ R : ℝ, 0 < R ∧ ∀ᵐ z ∂ρ.measure, squareEnergy ρ.measure k ρ.kind R z < ⊤ := by
  intro n hn k hk hkn L hL A C ρ _ _
  obtain ⟨c, C', hρ⟩ := b2_reference_adr_square n hn k hk hkn L hL
  obtain ⟨hcar, hsq⟩ := hρ ρ
  obtain ⟨a, b, -, -, hab⟩ := b2_adr_hausdorff_comparison_proof k c C'
  have hint := dp2_intrinsic_of_carrier hn hcar (hab n hn ρ.carrier ρ.measure hcar)
  exact ⟨hcar.finiteOnCompacts, hcar.innerRegular, hint.1, hint.2, 1, one_pos, hsq⟩

end ParabolicRectifiability.QuantitativeCharacterization
