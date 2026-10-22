import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Foundations.Proofs.RectifiableSums

/-! # Typed-rectifiability helpers: domination and countable sums

Two helpers for typed regular rectifiability, with prefix `f2i_`: it passes to dominated
measures (and absolutely continuous ones), and it is closed under countable sums.

Both declarations delegate to the corresponding `_proof` theorems. Those proofs use the
defining absolute continuity and graph-carriage clauses; no local-finiteness assumption is
added.

Conventions: `IsRegularlyRectifiableMeasure T k μ` is `μ ≪ H_P^k` together with a countable
carrier of typed graphs, each with its own finite norm.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ParabolicRectifiability.Foundations

/-- **Domination helper S1.** Typed regular rectifiability passes to
every measure absolutely continuous with respect to a rectifiable one; in particular to every
dominated measure `ν ≤ μ` (`Measure.absolutelyContinuous_of_le`) and every restriction.

Absolute continuity is inherited from `μ`. The hypothesis `ν ≪ μ` covers both dominated
measures and restrictions.

Route: both conjuncts of `IsRegularlyRectifiableMeasure`.
`ν ≪ μ ≪ H_P^k` (`Measure.AbsolutelyContinuous.trans`); keep the same graph family, and the
complement of its union is `μ`-null, hence `ν`-null. A case split on `T` (three constructors)
exposes the carrier of each type. Elementary bookkeeping. It is used in
`f2i_isRegularlyRectifiableMeasure_of_restrict_cover` and for the multiplicity layers
`μ⌊A_{T,N} ≤ μ^N_T` of the canonical decomposition. -/
theorem f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous
    {n k : ℕ} (T : FamilyKind) {μ ν : Measure (Space n)}
    (hμ : IsRegularlyRectifiableMeasure T k μ) (hνμ : ν ≪ μ) :
    IsRegularlyRectifiableMeasure T k ν := by
  exact ParabolicRectifiability.Foundations.f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous_proof T hμ hνμ

/-- **Typed countable-sum helper.** A countable sum of measures each of which is zero or typed
regularly rectifiable is typed regularly rectifiable. (Take the countable union of the
resulting graph covers and add the absolutely continuous restrictions; the zero measure causes
no exception.)

Route:
1. Zero summands: supply empty horizontal and vertical families (`Set ℕ` index `∅`).
2. AC: for an `H_P^k`-null `A`, `Measure.sum_apply_of_countable` (arbitrary sets) gives `(Σ ν)(A) = Σ ν_i(A) = 0`; alternatively
   `Measure.absolutelyContinuous_sum_left`.
3. Choose for each nonzero summand its finite-norm graph witnesses; package a graph with its
   own norm as `(ε, G) : Σ ε : ℝ, HorizontalGraph n k ε` (and vertically).
4. Merge over `Σ i, I_i` with `Countable.exists_injective_nat` and `Set.iUnion_sigma`,
   keeping every graph's own norm; the same reindexing is used in
   `exists_natSubset_reindex`, `iUnion_eq_of_range_eq`, `exists_merge_families`.
5. `ν_i(Uᶜ) = 0` by monotonicity for every `i`; `Measure.sum_apply_eq_zero`
   (arbitrary sets) gives `(Σ ν)(Uᶜ) = 0`.
The case split on `T` (three constructors) is needed for the carrier conjunct.

It is used with `ι = ℕ`, `T = .mixed`, in
`f2i_isRegularlyRectifiableMeasure_of_restrict_cover`, and in the canonical decomposition
(`ι = ℕ` for the multiplicity layers and `ι = Bool` with `Measure.sum_cond` for binary sums). -/
theorem f2i_isRegularlyRectifiableMeasure_sum
    {n k : ℕ} {ι : Type*} [Countable ι]
    (T : FamilyKind) (ν : ι → Measure (Space n))
    (hν : ∀ i, ν i ≠ 0 →
      IsRegularlyRectifiableMeasure T k (ν i)) :
    IsRegularlyRectifiableMeasure T k (Measure.sum ν) := by
  exact ParabolicRectifiability.Foundations.f2i_isRegularlyRectifiableMeasure_sum_proof T ν hν

end ParabolicRectifiability.Foundations
