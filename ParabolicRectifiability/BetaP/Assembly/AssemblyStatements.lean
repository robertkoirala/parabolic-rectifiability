import ParabolicRectifiability.BetaP.Proofs.Support.Interfaces

/-! # Finite assembly of a beta-`p` decomposition: intermediate statements

Proposition definitions used in the proof of `exists_assembled_p_decomposition`, which assembles
a decomposition of `μ` from finitely many localized pieces. Its inputs are
the localization `S : PLocalization μ k T p M N`, the carriers `K i : PCarrier (μ⌊region_i) k T p
M C_c` and their Borel typings `D i : TypedSplit k T (K i).set`; Hausdorff-null residuals are
already assigned to a type inside `TypedSplit`.

The decomposition is the restriction decomposition (the cleaner nonnegative
choice): with compact `A_{H,i} ⊆ H_i`, `A_{V,i} ⊆ V_i` and
`E_T = ⋃_i region_i ∩ A_{T,i}`, put `μ_T = μ⌊E_T = Σ_i ν_i⌊A_{T,i}` (`ν_i = μ⌊region_i`, the
regions are disjoint) and `μ⁺ = μ⌊(E_H ∪ E_V)ᶜ = μ - μ_H - μ_V`. Three statements remain:
* `CasmCompactApproximationStatement`: compact inner approximation of a typing in source
  measure;
* `CasmRemainderStatement`: the remainder in `P(0,1)` is at most `Γ` plus the per-piece losses;
* `CasmSupportBoundsStatement`: the support bundle of the actual supports by finite summation of
  the carrier bounds.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- **Compact inner approximation of a typing.** For a finite inner-regular source `ν`, a Borel typing `D : TypedSplit k T K` and
`ε > 0`, there are compact `A_H ⊆ D.horizontal`, `A_V ⊆ D.vertical` with
`ν(K \ (A_H ∪ A_V)) ≤ ε`. -/
def CasmCompactApproximationStatement : Prop :=
  ∀ {n k : ℕ} {T : FamilyKind} (ν : Measure (Space n)), IsFiniteMeasure ν → ν.InnerRegular →
    ∀ {K : Set (Space n)} (D : TypedSplit k T K) (ε : ℝ), 0 < ε →
      ∃ AH AV : Set (Space n), IsCompact AH ∧ IsCompact AV ∧ AH ⊆ D.horizontal ∧
        AV ⊆ D.vertical ∧ ν (K \ (AH ∪ AV)) ≤ ENNReal.ofReal ε

/-- **Remainder bookkeeping.** For a localization `S`
of the `S_p` good set, sets `A_H i`, `A_V i` (one pair per region) whose union misses at most
`ℓ` of the localized source `μ⌊region_i`, and the threshold hypothesis
`μ(P(0,1) ∩ {S_{p,μ,T}^2 > M}) ≤ Γ`: the part of `P(0,1)` outside
`E_H ∪ E_V = ⋃_i region_i ∩ A_H i ∪ ⋃_i region_i ∩ A_V i` has `μ`-measure at most
`Γ + Σ_i ℓ` (coefficient one on `Γ`). Outer measure; no measurability of `A_T i` is needed. -/
def CasmRemainderStatement : Prop :=
  ∀ {n k N : ℕ} {T : FamilyKind} {p M : ℝ} (μ : Measure (Space n))
    (S : PLocalization μ k T p M N) (AH AV : Fin S.count → Set (Space n)) (Γ ℓ : ℝ),
    μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < energyS μ k T p 2 z}) ≤
      ENNReal.ofReal Γ →
    (∀ i, μ.restrict (S.region i) (AH i ∪ AV i)ᶜ ≤ ENNReal.ofReal ℓ) →
    μ (Metric.ball (point 0 0) 1 ∩
        ((⋃ i, S.region i ∩ AH i) ∪ ⋃ i, S.region i ∩ AV i)ᶜ) ≤
      ENNReal.ofReal Γ + ∑ _i : Fin S.count, ENNReal.ofReal ℓ

/-- **Support bundle by finite summation.** Let `c` carriers `K i : PCarrier (ν i) k T p M C_c` of sources supported in
`P̄(center i, 1/64)`, with typings `D i`, and compact `A_H i ⊆ (D i).horizontal`,
`A_V i ⊆ (D i).vertical` be given, `C_c ≥ 0`. Then every pair of closed sets
`K_H ⊆ (⋃_i A_H i) ∩ P̄(0,1)`, `K_V ⊆ (⋃_i A_V i) ∩ P̄(0,1)` satisfies the support bundle at
centre `0`, scale `1`, with every constant `C ≥ c C_c`: compactness, emptiness for unavailable
types, own-type covers at every tolerance (from the typings), `H_P^k(K) ≤ C` (each carrier lies
in a ball of radius one), and the local Hausdorff, separated-set, tube, finite and countable
packing bounds (finite unions of the carriers' content and packing bounds). -/
def CasmSupportBoundsStatement : Prop :=
  ∀ {n k c : ℕ} {T : FamilyKind} {p M Cc : ℝ} (ν : Fin c → Measure (Space n))
    (center : Fin c → Space n), 0 ≤ Cc →
    (∀ i, (ν i).support ⊆ Metric.closedBall (center i) (1 / 64)) →
    ∀ (K : ∀ i, PCarrier (ν i) k T p M Cc) (D : ∀ i, TypedSplit k T (K i).set)
      (AH AV : Fin c → Set (Space n)),
    (∀ i, IsCompact (AH i)) → (∀ i, IsCompact (AV i)) →
    (∀ i, AH i ⊆ (D i).horizontal) → (∀ i, AV i ⊆ (D i).vertical) →
    ∀ KH KV : Set (Space n), IsClosed KH → IsClosed KV →
      KH ⊆ (⋃ i, AH i) ∩ Metric.closedBall (point 0 0) 1 →
      KV ⊆ (⋃ i, AV i) ∩ Metric.closedBall (point 0 0) 1 →
      ∀ C : ℝ, (c : ℝ) * Cc ≤ C →
        HasRegularSupportBounds k C (point 0 0) 1 KH KV

end ParabolicRectifiability.BetaP
