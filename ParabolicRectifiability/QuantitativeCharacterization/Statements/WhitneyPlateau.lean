import ParabolicRectifiability.QuantitativeCharacterization.References

/-! # Named statement: the Whitney plateau completion of a compact trace

Proposition definition only. The horizontal-reference data (`HorizontalReference`) can be
completed from any admissible trace.

The statement is used in two places: for the Lipschitz-extended spatial chart of a compact
horizontal subset graph, with the graph's time function as trace; and for the neck traces in the
forward covering (the exact compact trace of a horizontal neck has such a completion; if the
centre set is empty, choose a singleton trace on its spatial chart, otherwise use its actual
nonempty compact preimage).

It is therefore stated for an arbitrary global `L`-bi-Lipschitz spatial map, an arbitrary
nonempty compact domain and an arbitrary trace with the quadratic bound on the domain, and
it fixes exactly the three pieces of data prescribed (spatial map, domain, trace); the grid,
cubes, anchors and faces are produced. The construction takes any translated and dilated dyadic
Whitney decomposition: such cubes arise by taking maximal dyadic cubes satisfying the lower
inequality, and the failed inequality for the parent gives the upper one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **Whitney plateau completion.**

For `1 ≤ k ≤ n`, every real `L`, every global spatial map `F : ℝ^k → ℝ^n` with
`|u - v| ≤ L |F(u) - F(v)|` and `|F(u) - F(v)| ≤ L |u - v|` for all `u, v`, every nonempty
compact `D ⊆ ℝ^k` and every trace `τ : ℝ^k → ℝ` with `|τ(u) - τ(v)| ≤ L² |u - v|²` for
`u, v ∈ D`, there is a horizontal `L`-reference whose spatial map is `F`, whose domain is `D`
and whose plateau function agrees with `τ` on `D`.

Only `τ|_D` matters; the plateau function off `D` is produced (constant `τ(a_Q)` on each
assigned face). The Whitney cubes (`4 diam Q ≤ dist(Q,D) ≤ 10 diam Q`), their single
translated and dilated dyadic grid, the nearest anchors `a_Q ∈ D` and the Borel face
assignment are produced; they do not depend on `F`, `τ` or `L`. -/
def WhitneyPlateauCompletionStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n →
  ∀ (L : ℝ) (F : Spatial k → Spatial n),
    (∀ u v : Spatial k, dist u v ≤ L * dist (F u) (F v) ∧ dist (F u) (F v) ≤ L * dist u v) →
  ∀ D : Set (Spatial k), D.Nonempty → IsCompact D →
  ∀ τ : Spatial k → ℝ, (∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ L ^ 2 * dist u v ^ 2) →
    ∃ H : HorizontalReference n k L,
      H.spatialMap = F ∧ H.domain = D ∧ ∀ u ∈ D, H.height u = τ u

end ParabolicRectifiability.QuantitativeCharacterization
