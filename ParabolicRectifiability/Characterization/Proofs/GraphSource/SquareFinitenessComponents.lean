import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ADRCarrierFacts
import ParabolicRectifiability.Characterization.Proofs.GraphSource.HorizontalCompactCover
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Component estimates for graph-source square finiteness

The declarations expose the component estimates used for square finiteness of graph sources,
each with its original hypotheses and one mathematical responsibility. They delegate to the
corresponding proof theorems from `Characterization/Proofs/`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-- Finite-source localization: for locally finite `μ`, use the finite sources
`μ_N = μ⌊P̄(0,N)`. On `P(0,N-1)` their testing integrals equal the full `μ` integrals for every
`r < 1`, exactly.

If `dist(z,a) + R ≤ ρ`, then the square up to the endpoint `R` at `z` is the
same for `μ` and for its restriction to the closed ball `P̄(a,ρ)`, for every family and every
source.

Proof route. For `0 < r < R`, `P(z,r) ⊆ P̄(a,ρ)`, so
`(μ⌊P̄(a,ρ))⌊P(z,r) = μ⌊P(z,r)` (`Measure.restrict_restrict`, the ball is measurable) and every
`fit` agrees; hence `betaSq` agrees on `Ioo 0 R` and so do the `scaleMeasure` integrals
(`setLIntegral_congr_fun`). No inequality reversing source restriction is used.
-/
theorem b2_squareEnergy_restrict_closedBall :
    ∀ (n k : ℕ) (T : FamilyKind) (μ : Measure (Space n)) (a : Space n) (ρ R : ℝ)
      (z : Space n), dist z a + R ≤ ρ →
        squareEnergy (μ.restrict (Metric.closedBall a ρ)) k T R z = squareEnergy μ k T R z := by
  exact ParabolicRectifiability.Characterization.b2_squareEnergy_restrict_closedBall_proof

/-- Compact exhaustion of a horizontal subset graph modulo `H_P^k`: complete horizontal domains
only by closure, and exhaust them modulo volume by compact subsets.

Every horizontal subset graph of slope at most `ε` (arbitrary, possibly
non-Borel, domain) is covered, modulo `H_P^k` (outer measure), by countably many horizontal
graphs of the same slope bound whose domains are nonempty and compact.

Proof route (with the Borel envelope). Take the envelope `G'` of `graph_borel_envelope`
(`G.image ⊆ G'.image`, `G'.image` Borel). Its domain is Borel in `U = G'.direction`: it is the
image of the Borel set `G'.image` under the continuous map `(x,t) ↦ π_U(x - a)`, injective on
the graph (Lusin–Souslin, `MeasurableSet.image_of_continuousOn_injOn`). Exhaust it modulo
Lebesgue measure on `U` by compact sets `K_j` (inner regularity), drop the empty ones, and
restrict `G'` to each `K_j` (same direction, offset and slope bound). The graph map
`u ↦ (a + u + g(u), h(u))` is `√(1+ε²)`-Lipschitz from `U` to `X`, so the
image of the Lebesgue-null remainder is `H_P^k`-null (`LipschitzOnWith.hausdorffMeasure_image_le`
and `H^k = c_k L^k` on `U`).

Alternative: if the envelope has a closed domain (`HorizontalClosedEnvelopeStatement`), take
`K_N = dom(G') ∩ B̄(0,N)` with an empty remainder; Lusin–Souslin and inner regularity are then
not needed. Another option: the `ε`-Lipschitz `g` and the quadratic modulus of `h` extend
uniquely to `closure D` with the same bounds, which gives `K_N = closure D ∩ B̄(0,N)` with an
empty remainder. -/
theorem b2_horizontal_compact_cover :
    ∀ (n k : ℕ) (ε : ℝ) (G : HorizontalGraph n k ε),
      ∃ (J : Set ℕ) (Gc : J → HorizontalGraph n k ε),
        (∀ j, (Gc j).domain.Nonempty ∧ IsCompact (Gc j).domain) ∧
        hausdorffP n k (G.image \ ⋃ j, (Gc j).image) = 0 := by
  exact ParabolicRectifiability.Characterization.b2_horizontal_compact_cover_proof

end ParabolicRectifiability.Characterization
