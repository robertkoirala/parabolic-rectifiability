import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # Statements: quantitative coverings and qualitative regular rectifiability

Proposition definitions only. The endpoint theorems are in the `Endpoints` module of the same
name.

* a measure with a quantitative covering is rectifiable (`AnyCoverRectifiableStatement`);
* countable quantitative pieces (`CountableQuantitativePiecesStatement`).

Regular mixed parabolic `k`-rectifiability of a measure is the Foundations
`IsRegularlyRectifiableMeasure .mixed k μ` (`μ ≪ H_P^k` and a countable carrier of
horizontal graphs of finite slope and full general regular vertical graphs of finite norm),
which is condition (1) of the qualitative characterization.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **A measure with a quantitative covering is rectifiable**: a locally Radon measure with the
`(K,L)` property for some finite `K, L ≥ 1` is regularly mixed parabolically
`k`-rectifiable. No ADR or upper-growth assumption is made. -/
def AnyCoverRectifiableStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ K L : ℝ, 1 ≤ K → 1 ≤ L → IsQuantitativelyMixedRectifiable k K L μ →
    IsRegularlyRectifiableMeasure .mixed k μ

/-- **Countable quantitative pieces.** With `K_* = 2^k` and `L_* = max {2, √(1+n)}`, a locally
Radon `μ` is regularly mixed parabolically `k`-rectifiable if and only if there are pairwise
disjoint Borel sets `E_j` (indexed here by `j ∈ ℕ` instead of `j ≥ 1`) with
`μ = Σ_j μ ⌊ E_j` and every nonzero piece `μ ⌊ E_j` being `(K_*, L_*)`-quantitatively
mixed parabolically rectifiable. No ADR or uniform conclusion for the sum is asserted. -/
def CountableQuantitativePiecesStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    (IsRegularlyRectifiableMeasure .mixed k μ ↔
      ∃ E : ℕ → Set (Space n), (∀ j, MeasurableSet (E j)) ∧
        Pairwise (fun i j => Disjoint (E i) (E j)) ∧
        μ = Measure.sum (fun j => μ.restrict (E j)) ∧
        ∀ j, μ.restrict (E j) ≠ 0 →
          IsQuantitativelyMixedRectifiable k ((2 : ℝ) ^ k) (max 2 (Real.sqrt (1 + n)))
            (μ.restrict (E j)))

end ParabolicRectifiability.QuantitativeCharacterization
