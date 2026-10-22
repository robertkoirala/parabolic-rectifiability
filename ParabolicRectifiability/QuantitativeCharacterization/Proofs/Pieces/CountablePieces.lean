import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Pieces.ComponentTheorems
import ParabolicRectifiability.Foundations.Proofs.Rectifiability.Sums

/-! # Countable quantitative pieces: assembly

* `dp2_countable_pieces_of_typed_covers` has exactly the type of
  `QuantitativeCharacterization.countable_pieces_of_typed_covers`; it is assembled from the
  auxiliary statements for the sharp horizontal chart, the horizontal and vertical references, the
  disjoint Borel restrictions and the one-reference certificate.
* `dp2_isRegularlyRectifiableMeasure_of_sum_restrict` has exactly the type of
  `QuantitativeCharacterization.isRegularlyRectifiableMeasure_of_sum_restrict`; it follows from
  the countable-sum statement for regularly rectifiable measures.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **Countable quantitative pieces from typed covers** (forward direction): exactly the type of
`countable_pieces_of_typed_covers`. The pieces assembly applied to the horizontal references
(themselves built from the sharp chart), the vertical references, the disjoint restrictions and
the one-reference certificate. -/
theorem dp2_countable_pieces_of_typed_covers :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    μ ≪ hausdorffP n k →
    ∀ EH EV : Set (Space n), MeasurableSet EH → MeasurableSet EV → Disjoint EH EV →
    μ (EH ∪ EV)ᶜ = 0 →
    HasTypedMeasureCover .horizontal k (μ.restrict EH) 1 →
    HasTypedMeasureCover .vertical k (μ.restrict EV) 1 →
      ∃ E : ℕ → Set (Space n), (∀ j, MeasurableSet (E j)) ∧
        Pairwise (fun i j => Disjoint (E i) (E j)) ∧
        μ = Measure.sum (fun j => μ.restrict (E j)) ∧
        ∀ j, μ.restrict (E j) ≠ 0 →
          IsQuantitativelyMixedRectifiable k ((2 : ℝ) ^ k) (max 2 (Real.sqrt (1 + n)))
            (μ.restrict (E j)) :=
  dp2_pieces_assembly (dp2_horizontal_reference_cover dp2_sharp_chart) dp2_vertical_reference
    dp2_disjoint_restrictions dp2_one_reference_certificate

/-- **Regular rectifiability from a countable restricted sum** (converse assembly): exactly the
type of `isRegularlyRectifiableMeasure_of_sum_restrict`. The countable-sum lemma
`f2i_isRegularlyRectifiableMeasure_sum` at `ι = ℕ`, `T = .mixed`, `ν_j = μ⌊E_j`, rewritten by the
supplied identity. The measurability of the `E_j` and the dimension guards are not used. -/
theorem dp2_isRegularlyRectifiableMeasure_of_sum_restrict :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
    ∀ μ : Measure (Space n), ∀ E : ℕ → Set (Space n), (∀ j, MeasurableSet (E j)) →
    μ = Measure.sum (fun j => μ.restrict (E j)) →
    (∀ j, μ.restrict (E j) ≠ 0 → IsRegularlyRectifiableMeasure .mixed k (μ.restrict (E j))) →
      IsRegularlyRectifiableMeasure .mixed k μ := by
  intro n _ k _ _ μ E _ hsum hpieces
  have h := f2i_isRegularlyRectifiableMeasure_sum .mixed (fun j => μ.restrict (E j)) hpieces
  rw [← hsum] at h
  exact h

end ParabolicRectifiability.QuantitativeCharacterization
