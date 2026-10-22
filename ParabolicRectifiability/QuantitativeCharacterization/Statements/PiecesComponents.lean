import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # Countable quantitative pieces: statements

Proposition definitions for the auxiliary facts behind
`QuantitativeCharacterization.countable_pieces_of_typed_covers`, the forward direction of the
countable quantitative pieces characterization. Notation: `L_* = max 2 √(1+n)` and `K_* = 2^k`.

* `dp2_SharpChartStatement`: the Pythagorean chart of a slope-one horizontal graph,
  bi-Lipschitz with constants `1` and `√(1+n)` (the previously available chart only gives
  `1 + √n`).
* `dp2_HorizontalReferenceCoverStatement`: every slope-one horizontal graph is covered,
  modulo `H_P^k`, by countably many closed carriers of horizontal `L_*`-references.
* `dp2_VerticalReferenceStatement`: a nonambient norm-one full general regular vertical graph
  has the same carrier as a vertical `L_*`-reference.
* `dp2_DisjointRestrictionStatement`: disjoint Borel assignment of a countable Borel family
  carrying `μ`.
* `dp2_OneReferenceCertificateStatement`: absolute continuity and support inside one
  `L`-reference carrier, `L ≥ 2`, give the `(2^k, L)` property by one ball `P(a,2R)` per root.
* `dp2_CountablePiecesStatement`: the type of `countable_pieces_of_typed_covers`, the conclusion
  of the pieces assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **The sharp horizontal chart.** Every horizontal graph of slope at most `1` has a global spatial chart
`F : ℝ^k → ℝ^n` with `|u - v| ≤ |F u - F v| ≤ √(1+n) |u - v|`, a base `D` (nonempty or compact
when the graph domain is) and a trace `τ` with `|τ u - τ v| ≤ |u - v|²` on `D`, such that the
graph image lies in `{(F u, τ u) : u ∈ D}`. -/
def dp2_SharpChartStatement : Prop :=
  ∀ (n k : ℕ) (G : HorizontalGraph n k 1),
    ∃ (F : Spatial k → Spatial n) (D : Set (Spatial k)) (τ : Spatial k → ℝ),
      (∀ u v : Spatial k, dist u v ≤ dist (F u) (F v) ∧
        dist (F u) (F v) ≤ Real.sqrt (1 + n) * dist u v) ∧
      (∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ dist u v ^ 2) ∧
      (G.domain.Nonempty → D.Nonempty) ∧ (IsCompact G.domain → IsCompact D) ∧
      G.image ⊆ (fun u => point (F u) (τ u)) '' D

/-- **Horizontal references.** For `k ≥ 1`, every
horizontal graph of slope at most `1` is covered, modulo `H_P^k`, by the closed carriers
`Γ = supp σ` of countably many horizontal `L_*`-references, `L_* = max 2 √(1+n)`. -/
def dp2_HorizontalReferenceCoverStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → ∀ G : HorizontalGraph n k 1,
    ∃ (J : Set ℕ) (H : J → HorizontalReference n k (max 2 (Real.sqrt (1 + n)))),
      hausdorffP n k (G.image \ ⋃ j, (H j).carrier) = 0

/-- **Vertical references.** For `k < n + 2`, every full
general regular vertical graph of norm at most `1` (including spatial rank zero, `k = 2`) has
exactly the carrier of a vertical `L_*`-reference. -/
def dp2_VerticalReferenceStatement : Prop :=
  ∀ (n k : ℕ), k < n + 2 → ∀ G : GeneralRegularVerticalGraph n k 1,
    ∃ V : VerticalReference n k (max 2 (Real.sqrt (1 + n))), V.carrier = G.image

/-- **Disjoint Borel restrictions.** A countable Borel
family `B_j` whose union carries `μ` yields pairwise disjoint Borel `E_j ⊆ B_j` with
`μ = Σ_j μ⌊E_j`. -/
def dp2_DisjointRestrictionStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (B : ℕ → Set (Space n)), (∀ j, MeasurableSet (B j)) →
    μ (⋃ j, B j)ᶜ = 0 →
      ∃ E : ℕ → Set (Space n), (∀ j, MeasurableSet (E j)) ∧
        Pairwise (fun i j => Disjoint (E i) (E j)) ∧ (∀ j, E j ⊆ B j) ∧
        μ = Measure.sum (fun j => μ.restrict (E j))

/-- **The one-reference certificate.** If `L ≥ 2`,
`ν ≪ H_P^k` and `supp ν` lies in the carrier of one `L`-reference, then `ν` is
`(2^k, L)`-quantitatively mixed rectifiable: every support-centred root `P(a,R)` has the
covering with the single model ball `P(a,2R)`, that reference, empty bad set and the whole
tested cylinder as scale set. -/
def dp2_OneReferenceCertificateStatement : Prop :=
  ∀ (n k : ℕ) (L : ℝ), 2 ≤ L → ∀ (ρ : Reference n k L) (ν : Measure (Space n)),
    ν ≪ hausdorffP n k → ν.support ⊆ ρ.carrier →
      IsQuantitativelyMixedRectifiable k ((2 : ℝ) ^ k) L ν

/-- The type of `countable_pieces_of_typed_covers`: the conclusion of the pieces assembly. -/
def dp2_CountablePiecesStatement : Prop :=
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
          (μ.restrict (E j))

end ParabolicRectifiability.QuantitativeCharacterization
