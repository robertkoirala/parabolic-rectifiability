import ParabolicRectifiability.QuantitativeCharacterization.Coverings
import ParabolicRectifiability.Measure.BetaLaws

/-! # Statements: beta scaling, monotonicity of the property, reference estimates

Proposition definitions only. The endpoint theorems are in the `Endpoints` module of the same
name.

* the exact beta scaling identity (`BetaScalingStatement`);
* monotonicity of the `(K,L)` property in `K` and `L`
  (`QuantitativeRectifiabilityMonoStatement`);
* the reference estimates (`ReferenceEstimatesStatement`).

Conventions: the standing assumptions `1 ≤ n`, `1 ≤ k ≤ n + 2` are hypotheses; "locally
Radon" is `IsFiniteMeasureOnCompacts μ` together with `μ.InnerRegular`; real constants are
compared through `ENNReal.ofReal`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **The scaling identity.** For `S_{a,R}(z) = δ_{1/R}(z - a)` and
`μ_{a,R} = R^{-k} (S_{a,R})_# μ`, which is the existing `rescaledSource μ k a R hR`,
`β_{μ_{a,R}}(z,r)² = β_μ(a + δ_R z, R r)²` for the mixed family, every centre `z` and every
positive radius `r`. The point `a + δ_R z` is `(similarity a R hR).symm z`
(`similarity_symm_apply`). As in the cited sentence, no regularity of `μ` is assumed and
`a` is arbitrary. (The identity at a moved centre for every family is the existing
`betaSq_rescaledSource`.) -/
def BetaScalingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), ∀ (a : Space n) (R : ℝ) (hR : 0 < R),
  ∀ (z : Space n) (r : ℝ), 0 < r →
    betaSq (rescaledSource μ k a R hR) k .mixed z r =
      betaSq μ k .mixed ((similarity a R hR).symm z) (R * r)

/-- **Monotonicity**: increasing either constant preserves the
`(K,L)`-quantitative mixed parabolic rectifiability of a locally Radon measure. -/
def QuantitativeRectifiabilityMonoStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ K K' L L' : ℝ, 1 ≤ K → K ≤ K' → 1 ≤ L → L ≤ L' →
    IsQuantitativelyMixedRectifiable k K L μ → IsQuantitativelyMixedRectifiable k K' L' μ

/-- **Reference estimates**: for `n ≥ 1`,
`1 ≤ k ≤ n + 2` and finite `L ≥ 1`, there are constants depending only on `(n,k,L)` such
that every available `L`-reference `(Γ, σ)` (horizontal, vertical, or ambient at
`k = n + 2`) is globally `k`-ADR with these constants, and its own-type Carleson energy
`sup_{a ∈ Γ, R > 0} R^{-k} ∫_{P(a,R)} ∫_0^R β_{σ,T}(z,r)² dr/r dσ(z)` is at most
`C(n,k,L)`; at `k = n + 2` this energy is zero. These are conclusions about the reference
classes, not fields of their definitions. -/
def ReferenceEstimatesStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L →
  ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
    ∀ ρ : Reference n k L,
      IsADR A k ρ.measure ∧ referenceEnergy ρ ≤ ENNReal.ofReal C ∧
        (k = n + 2 → referenceEnergy ρ = 0)

end ParabolicRectifiability.QuantitativeCharacterization
