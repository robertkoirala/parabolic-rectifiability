import ParabolicRectifiability.Foundations.Graphs

/-! # The support-conclusion bundle

One Prop-valued bundle for the support conclusions shared by the quantitative main theorem
(at `a = 0`, `R = 1`), its scaled form and the beta-`p` theorem (unit and localized forms).

It concerns only the two typed supports `K_H`, `K_V` and their union `K`. The source
measure, the decomposition and the loss are not part of it, so it applies both to the
restriction decomposition of the parabolic rectifiable Reifenberg theorem and to the nonnegative decomposition of Main
theorem 3. The encodings follow `HasRectifiabilityContentBounds`: `Finset` for finite
separated sets, `Fin l` and `I : Set ℕ` for finite and countable disjoint ball families,
and extended distance for the tubular neighbourhood (the empty set has an empty one).

The bundle includes emptiness of the support of each unavailable type. This is not implied by
the graph-cover fields: an empty family of an unavailable type covers any
`H_P^k`-null support, such as a point.

**What the bundle does not contain.** It states no measure identity (the decomposition
of the source measure, its restrictions or the vanishing of unavailable measure parts),
no loss or remainder bound, and no identification of `K_H`, `K_V` with the actual
supports of the decomposition pieces. Those clauses stay in each consuming endpoint.
Likewise, emptiness of a type that is available but disallowed in a fixed-family
statement is not part of this bundle; consumers state it explicitly.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.Foundations

/-- The support conclusions at centre `a` and scale `R`, with constant `C`, for the typed
supports `K_H`, `K_V` and `K = K_H ∪ K_V`: compact supports in the closed ball
`P̄(a,R)`, empty supports for unavailable types, typed graph covers at every positive
tolerance (vertical covers in the general regular class), the global Hausdorff bound
`C R^k`, and the local Hausdorff, separated-set, finite and countable packing bounds at
every scale `0 < s ≤ R`, and the tube bound `C R^k r^{n+2-k}` for `0 < r ≤ R`.

It contains no measure identity, no loss and no identification of `K_H`, `K_V` with
actual supports; see the module documentation. -/
structure HasRegularSupportBounds {n : ℕ} (k : ℕ) (C : ℝ) (a : Space n) (R : ℝ)
    (KH KV : Set (Space n)) : Prop where
  horizontal_compact : IsCompact KH
  vertical_compact : IsCompact KV
  horizontal_subset : KH ⊆ Metric.closedBall a R
  vertical_subset : KV ⊆ Metric.closedBall a R
  horizontal_unavailable : ¬ (1 ≤ k ∧ k ≤ n) → KH = ∅
  vertical_unavailable : ¬ (2 ≤ k ∧ k ≤ n + 2) → KV = ∅
  horizontal_graphs : ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k KH ε
  vertical_graphs : ∀ ε : ℝ, 0 < ε → HasGeneralRegularVerticalGraphCover k KV ε
  hausdorff_total : hausdorffP n k (KH ∪ KV) ≤ ENNReal.ofReal (C * R ^ k)
  hausdorff_local : ∀ q s, 0 < s → s ≤ R →
    hausdorffP n k ((KH ∪ KV) ∩ Metric.ball q s) ≤ ENNReal.ofReal (C * s ^ k)
  separated : ∀ q s r, 0 < s → s ≤ R → 0 < r → r ≤ s →
    ∀ F : Finset (Space n), (↑F : Set (Space n)) ⊆ (KH ∪ KV) ∩ Metric.ball q s →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r ≤ dist x y) →
        (F.card : ℝ) ≤ C * (s / r) ^ k
  minkowski : ∀ r, 0 < r → r ≤ R →
    parabolicVolume n {z | Metric.infEDist z (KH ∪ KV) < ENNReal.ofReal r} ≤
      ENNReal.ofReal (C * R ^ k * r ^ (n + 2 - k))
  finite_packing : ∀ q s, 0 < s → s ≤ R →
    ∀ (l : ℕ) (z : Fin l → Space n) (r : Fin l → ℝ),
      (∀ i, z i ∈ (KH ∪ KV) ∩ Metric.ball q s) →
      (∀ i, 0 < r i ∧ r i ≤ s) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑ i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * s ^ k)
  countable_packing : ∀ q s, 0 < s → s ≤ R →
    ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ),
      (∀ i, z i ∈ (KH ∪ KV) ∩ Metric.ball q s) →
      (∀ i, 0 < r i ∧ r i ≤ s) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑' i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * s ^ k)

end ParabolicRectifiability.Foundations
