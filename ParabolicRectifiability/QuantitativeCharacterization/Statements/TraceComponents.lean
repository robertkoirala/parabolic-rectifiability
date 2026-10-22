import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # Trace statements for quantitative mixed rectifiability

Proposition definitions for the three auxiliary facts behind
`QuantitativeCharacterization.qmr_rectifiable_of_reference_covers`: a measure with a
`(K,L)`-regular mixed covering at every root is regularly rectifiable.

* `dp2_InfiniteMultiplicityNullStatement`: the set of points lying in
  infinitely many model balls of a covering is `H_P^k`-null.
* `dp2_TraceCarriageStatement`: where the multiplicity is finite a.e. on the root, almost every
  point of the root lies on the trace `P_i ∩ Γ_i` of one of its models.
* `dp2_RestrictCarrierRectifiableStatement`: reference-null transfer; typed graph
  covers of a reference measure give typed regular rectifiability of every `μ ≪ H_P^k`
  restricted to the reference carrier.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- **Infinite multiplicity is null.** For every `(K,L)` regular mixed covering of a
root, with `k ≥ 1`, the points of infinite multiplicity (those lying in infinitely many model
balls `P_i = P(a_i,R_i)`, i.e. `limsup_i P_i`) form an `H_P^k`-null set. Only the root packing
`Σ_i R_i^k ≤ K R^k < ∞` is used; no property of `μ`. -/
def dp2_InfiniteMultiplicityNullStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → ∀ (K L : ℝ) (μ : Measure (Space n)) (a : Space n) (R : ℝ)
    (𝒞 : RegularMixedCovering k K L μ a R),
      hausdorffP n k {z | 𝒞.multiplicity z = ⊤} = 0

/-- **Trace carriage.** For a
`(K,L)` regular mixed covering of the root `P(a,R)` with `L ≥ 1`, of a locally Radon measure,
if the multiplicity is finite at `μ`-a.e. point of the root, then `μ`-almost every point of the
root lies on one of the traces `P_i ∩ Γ_i`. The proof uses the finite bad logarithmic fibre
(Fubini on `bad_bound`), the pointwise scale partition (`cover_null`), the scale cover with its
distance floor `L⁻¹ dist(z,Γ_i) ≤ r`, and the closedness of the carriers.

The finite-multiplicity hypothesis is separate so that it can be supplied in two ways: from the
null set of infinite multiplicity and `μ ≪ H_P^k`, or from the first-moment bound
`∫_{P₀} m dμ ≤ A_* Σ_i R_i^k`. In both uses `μ` is locally Radon; local finiteness and inner regularity are assumed only for
σ-finiteness and the conull support (`Measure.measure_compl_support_of_innerRegular`). -/
def dp2_TraceCarriageStatement : Prop :=
  ∀ (n k : ℕ) (K L : ℝ), 1 ≤ L → ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ →
    μ.InnerRegular → ∀ (a : Space n) (R : ℝ) (𝒞 : RegularMixedCovering k K L μ a R),
      (∀ᵐ z ∂μ, z ∈ Metric.ball a R → 𝒞.multiplicity z < ⊤) →
        μ (Metric.ball a R \ ⋃ i, 𝒞.ball i ∩ (𝒞.reference i).carrier) = 0

/-- **Reference-null transfer.** If the measure of an
`L`-reference (`L ≥ 1`, `n ≥ 1`, `1 ≤ k ≤ n + 2`) is carried by countably many graphs of its
own type of norm at most `1`, then for every `μ ≪ H_P^k` the restriction `μ⌊Γ` to the
reference carrier is regularly rectifiable of the reference type: reference-null sets in `Γ`
are `H_P^k`-null by lower reference ADR, hence `μ`-null. -/
def dp2_RestrictCarrierRectifiableStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L →
    ∀ ρ : Reference n k L, HasTypedMeasureCover ρ.kind k ρ.measure 1 →
    ∀ μ : Measure (Space n), μ ≪ hausdorffP n k →
      IsRegularlyRectifiableMeasure ρ.kind k (μ.restrict ρ.carrier)

end ParabolicRectifiability.QuantitativeCharacterization
