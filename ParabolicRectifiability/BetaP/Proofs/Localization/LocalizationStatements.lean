import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces
import ParabolicRectifiability.BetaP.Statements.Laws

/-! # Statements for the localization of a source

Named statements (propositions only) used to prove `exists_p_localization`, whose output is
`PLocalization`.

The geometric part (the fixed finite grid of radius-`1/64` balls, disjointified, chosen from the
dimension only) and the regularity of the restrictions (finite, inner regular, support in the
closed cell) are taken from the quadratic localization `goodSourceLocalization`.
Two statements remain:
* `ClocPTailStatement`, the exact tail identity for every exponent `p > 0`:
  `∫_2^∞ β_p^2 ds/s = (2^{q_p}-1)^{-1} ∫_1^2 β_p^2 ds/s`, `q_p = 2 + 2k/p`, with
  `β_p^2 = B_p^{2/p}`. It is a separate named statement because the endpoint-two variants of
  the packing statements and the zero bridge use the same identity.
* `ClocAllScaleStatement`, the all-scale bound `2M` for a small restriction: restriction
  monotonicity on `(0,2)` plus the exact tail on `(2,∞)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Exact `p`-tail.** For every
source `ν` whose support is compact of diameter `< 1`, every `z ∈ supp ν`, every exponent
`p > 0`, rank `k` and family `T`:
`∫_{(2,∞)} B_p(ν;z,s)^{2/p} ds/s = (2^{q_p} - 1)^{-1} ∫_{(1,2)} B_p(ν;z,s)^{2/p} ds/s` with
`q_p = 2 + 2k/p` (real power). For `s ≥ 1` the testing ball contains the whole support, so
`B_p(ν;z,s) = s^{-k-p} I_p` with `I_p = inf_L ∫ d_P(w,L)^p dν` and `B_p^{2/p} = s^{-q_p} I_p^{2/p}`;
the identity holds in `[0,∞]` also for `I_p = 0` and `I_p = ⊤`. -/
def ClocPTailStatement : Prop :=
  ∀ {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p : ℝ), 0 < p →
    IsCompact ν.support → Metric.diam ν.support < 1 → ∀ {z : Space n}, z ∈ ν.support →
      (∫⁻ s in Ioi (2 : ℝ), betaPow ν k T p z s ^ (2 / p) ∂scaleMeasure) =
        (ENNReal.ofReal ((2 : ℝ) ^ (2 + 2 * (k : ℝ) / p) - 1))⁻¹ *
          ∫⁻ s in Ioo (1 : ℝ) 2, betaPow ν k T p z s ^ (2 / p) ∂scaleMeasure

/-- **All-scale bound of a small restriction.** Let `n ≥ 1`, `1 ≤ k ≤ n+2`, `T` available, `p > 0`, `M ≥ 0`. If the restriction `μ⌊G` has
support in a closed ball of radius `1/64` and `z ∈ supp(μ⌊G)` has `S_{p,μ,T}^2(z) ≤ M` for the
original source, then the all-scale square of the restriction is at most `2M`:
`∫_0^∞ β_{p,μ⌊G}(z,s)^2 ds/s ≤ 2M`. Inputs (implication form):
`BetaPowRestrictionStatement` and `ClocPTailStatement`. -/
def ClocAllScaleStatement : Prop :=
  BetaPowRestrictionStatement → ClocPTailStatement →
  ∀ {n : ℕ}, 1 ≤ n → ∀ {k : ℕ}, 1 ≤ k → k ≤ n + 2 → ∀ {T : FamilyKind}, Nonempty (Models n k T) →
  ∀ (μ : Measure (Space n)) {p : ℝ}, 0 < p → ∀ {M : ℝ}, 0 ≤ M →
  ∀ {G : Set (Space n)} {c : Space n},
    (μ.restrict G).support ⊆ Metric.closedBall c (1 / 64) →
    ∀ {z : Space n}, z ∈ (μ.restrict G).support →
      energyS μ k T p 2 z ≤ ENNReal.ofReal M →
      allScaleEnergyP (μ.restrict G) k T p z ≤ ENNReal.ofReal (2 * M)

end ParabolicRectifiability.BetaP
