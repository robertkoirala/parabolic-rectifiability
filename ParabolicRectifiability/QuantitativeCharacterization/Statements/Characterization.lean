import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # Statements: the quantitative characterization and its beta-`p` comparison remark

Proposition definitions only. The endpoint theorems are in the `Endpoints` module of the
same name.

* the quantitative characterization (`QuantitativeCharacterizationStatement`).
* The beta-`p` comparison (`BetaPowCarlesonComparisonStatement`).

The constant-dependent bodies are named `MainTheoremBounds` and `BetaPowForwardBounds`, so that
the common constants `L₀, C` of the quantitative characterization and its corollaries can be exported in one
existential (`QuantitativeCommonConstantsStatement`).

The global `A`-ADR class of the quantitative characterization is: `μ ≠ 0`, nonnegative Radon (finite on
compacts and inner regular), with unbounded (closed) support, and `IsADR A k μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- The conclusion of part 1 of the quantitative characterization for given constants `L₀` and `C`: every `μ ≠ 0` Radon with unbounded support
and `A`-ADR satisfies
* `M_β(μ) < ∞` iff `μ` is `(K,L₀)`-quantitatively mixed parabolically rectifiable for some
  finite `K ≥ 1`;
* if `M_β(μ) < ∞`, then `μ` is `(C(1 + M_β(μ)), L₀)`-quantitatively rectifiable;
* `M_β(μ) ≤ C K` for every `K ≥ 1` with the `(K,L₀)` property.

This predicate only names the body of `QuantitativeCharacterizationStatement` so that the same
`L₀, C` can be exported jointly with the corollaries (`QuantitativeCommonConstantsStatement`). -/
def MainTheoremBounds (n k : ℕ) (A L₀ C : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
    ¬ Bornology.IsBounded μ.support → IsADR A k μ →
      (carlesonEnergy μ k < ⊤ ↔
          ∃ K : ℝ, 1 ≤ K ∧ IsQuantitativelyMixedRectifiable k K L₀ μ) ∧
        (carlesonEnergy μ k < ⊤ →
          IsQuantitativelyMixedRectifiable k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ) ∧
        (∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L₀ μ →
          carlesonEnergy μ k ≤ ENNReal.ofReal (C * K))

/-- **The quantitative characterization.**

For `n ≥ 1`, `1 ≤ k ≤ n + 2` and `A ≥ 1`:
1. there are `L₀(n,k,A) ≥ 1` and `C(n,k,A) ≥ 1`, fixed before the measure, such that every
   `μ ≠ 0` Radon with unbounded support and `A`-ADR satisfies
   * `M_β(μ) < ∞` iff `μ` is `(K,L₀)`-quantitatively mixed parabolically rectifiable for
     some finite `K ≥ 1`;
   * forward bound: if `M_β(μ) < ∞`, then `μ` is `(C(1 + M_β(μ)), L₀)`-quantitatively
     rectifiable (a forward covering with `K ≤ C(1 + M_β)`; by monotonicity in `K` this is
     the same claim);
   * reverse bound: `M_β(μ) ≤ C K` for every uniform covering constant `K ≥ 1` of a
     `(K,L₀)` property;
2. for every `L ≥ 1` there is `C_rev(n,k,A,L)`, fixed before the measure, such that on the
   same class the `(K,L)` property gives `M_β(μ) ≤ C_rev K`. -/
def QuantitativeCharacterizationStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A : ℝ, 1 ≤ A →
    (∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ MainTheoremBounds n k A L₀ C) ∧
    (∀ L : ℝ, 1 ≤ L → ∃ Crev : ℝ, 0 < Crev ∧
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
        ¬ Bornology.IsBounded μ.support → IsADR A k μ →
          ∀ K : ℝ, 1 ≤ K → IsQuantitativelyMixedRectifiable k K L μ →
            carlesonEnergy μ k ≤ ENNReal.ofReal (Crev * K))

/-- The forward clause of the beta-`p` comparison for given constants `L₀` and `C`: on the global `A`-ADR class, finiteness of
`M_{S_p}` (`p ≥ 2`) or of `M_{T_p}` (`0 < p ≤ 2`) gives `M_β < ∞` and the
`(C(1 + M_β), L₀)` property.

This predicate only names the second conjunct of `BetaPowCarlesonComparisonStatement` so that
the same `L₀, C` can be exported jointly (`QuantitativeCommonConstantsStatement`). -/
def BetaPowForwardBounds (n k : ℕ) (A L₀ C : ℝ) : Prop :=
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
    ¬ Bornology.IsBounded μ.support → IsADR A k μ → ∀ p : ℝ,
      (2 ≤ p → carlesonEnergyS μ k p < ⊤ →
        carlesonEnergy μ k < ⊤ ∧
          IsQuantitativelyMixedRectifiable k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ) ∧
      (0 < p → p ≤ 2 → carlesonEnergyT μ k p < ⊤ →
        carlesonEnergy μ k < ⊤ ∧
          IsQuantitativelyMixedRectifiable k (C * (1 + (carlesonEnergy μ k).toReal)) L₀ μ)

/-- **The beta-`p` comparison.**
On the global `A`-ADR class of the quantitative characterization, with `M_{S_p}`, `M_{T_p}` the root energies
of the mixed-family beta-`p` energies of the whole source:
1. `M_β ≤ A^{1-2/p} M_{S_p}` for `p ≥ 2`, and `M_β ≤ 2^{2-p} M_{T_p}` for `0 < p ≤ 2`
   (one-sided; no beta-`p` equivalence is asserted);
2. finiteness of the indicated root bound gives `M_β < ∞` and the quadratic quantitative
   covering property with the forward bound `K ≤ C(1 + M_β)`, for constants
   `L₀(n,k,A) ≥ 1`, `C(n,k,A) ≥ 1` fixed before the measure. -/
def BetaPowCarlesonComparisonStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ A : ℝ, 1 ≤ A →
    (∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular → μ ≠ 0 →
      ¬ Bornology.IsBounded μ.support → IsADR A k μ → ∀ p : ℝ,
        (2 ≤ p → carlesonEnergy μ k ≤ ENNReal.ofReal (A ^ (1 - 2 / p)) * carlesonEnergyS μ k p) ∧
        (0 < p → p ≤ 2 →
          carlesonEnergy μ k ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 - p)) * carlesonEnergyT μ k p)) ∧
    (∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ BetaPowForwardBounds n k A L₀ C)

end ParabolicRectifiability.QuantitativeCharacterization
