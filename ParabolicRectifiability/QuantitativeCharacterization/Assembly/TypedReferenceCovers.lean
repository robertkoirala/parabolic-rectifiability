import ParabolicRectifiability.QuantitativeCharacterization.Assembly.ComponentStatements
import ParabolicRectifiability.Characterization.Statements.Branches

/-! # Typed graph covers of the reference measures

Every available `L`-reference measure has typed graph covers at every positive tolerance (the
countable typed graph coverage given by the qualitative fixed-family theorem): the statements
`reference_estimates` and `reference_intrinsic_of_estimates` put the reference measure in the
hypotheses of the fixed-family intrinsic sufficiency theorem, taken here as a hypothesis. The type
of a reference is available.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- The type of an `L`-reference is an available family: a horizontal reference needs
`1 ≤ k ≤ n`, a vertical one `2 ≤ k < n + 2`, and the ambient reference is vertical at
`k = n + 2`. -/
theorem Reference.kind_available {n k : ℕ} (hn : 1 ≤ n) {L : ℝ} (ρ : Reference n k L) :
    Nonempty (Models n k ρ.kind) := by
  cases ρ with
  | horizontal H => exact HorizontalModel.nonempty_iff.mpr H.available
  | vertical V =>
    have h1 := V.rank_eq
    have h2 := V.lt_ambient
    exact VerticalModel.nonempty_iff.mpr ⟨by omega, by omega⟩
  | ambient h => exact VerticalModel.nonempty_iff.mpr ⟨by omega, by omega⟩

/-- **Typed reference covers.** From the fixed-family intrinsic sufficiency theorem: every
`L`-reference measure is carried, for every `ε > 0`, by countably many graphs of its own type
with slope or regular norm at most `ε`. -/
theorem reference_typed_covers (hIS : Characterization.IntrinsicSufficiencyStatement)
    {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2) {L : ℝ} (hL : 1 ≤ L) :
    ∀ ρ : Reference n k L, ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover ρ.kind k ρ.measure ε := by
  obtain ⟨A, -, C, -, hest⟩ := reference_estimates n hn k hk hkn L hL
  intro ρ ε hε
  obtain ⟨hfin, hreg, hac, hcar, hen⟩ :=
    reference_intrinsic_of_estimates n hn k hk hkn L hL A C ρ (hest ρ).1 (hest ρ).2.1
  exact hIS n hn k hk hkn ρ.kind (ρ.kind_available hn) ρ.measure hfin hreg hac hcar hen ε hε

end ParabolicRectifiability.QuantitativeCharacterization
