import ParabolicRectifiability.Characterization.Proofs.SourceTransfer.TransferStatements

/-! # Named statements for the replacement of the bad region

Proposition definitions only. The component estimates are proved in the corresponding proof
modules and exposed as `b3_rp_goodSet`, …; `bad_region_replacement_of_leaves` assembles them into
`ReplacementStatement` (the statement of `bad_region_replacement`).

**Constants.** `ReplacementStatement` requires `0 < C₀` and `0 < C₁` before any ADR
hypothesis, so the assembly chooses `C₀ = max (C * 5 ^ k) 1` and
`C₁ = max ((5 ^ k + 205 ^ k) / c) 1`, exactly. The component statements give their bounds with
these constants (the sharp bound `C 5^k`, resp. `(5^k + 205^k)/c`, is weakened with
`le_max_left`).

There are four component statements:
* (i) `RpGoodSetStatement`: closedness of `G_A`, nonempty `G_A`, the bad-mass estimate;
* (ii.a) `RpWhitneySelectionStatement`: Whitney selection of disjoint relative balls in
  `Γ \ G` for a closed nonempty `G ⊆ Γ` of finite complementary reference mass;
* (ii.b) `RpAllocationStatement`: exact Borel allocation of `Ω_A` and the piece bounds;
* (iii) `RpAssemblyStatement`: domination `ν_A ≤ C₁ A σ` and mass preservation.
Two further estimates are used as inputs: `FivefoldSelectionStatement`
(`fivefold_ball_selection`) and `GoodDominationStatement` (`good_set_domination`).

 `G_A = adrGoodSet Γ ν k A`,
`Ω_A = Γ \ G_A`, `B_i = Γ ∩ P(z_i, r_i)`; `b3_replacedSource` is the measure `ν_A`.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.ReplacementTree

open ParabolicRectifiability.Foundations
open ParabolicRectifiability.Characterization.SourceTransferTree

/-- **(i) The good set: closedness, nonemptiness, bad mass.**

Given fivefold selection, under the reference hypotheses, for a finite `ν` carried by
`Γ` and `A > 0`: `G_A` is closed, nonempty, and `σ(Ω_A) ≤ (max (C 5^k) 1 / A) ν(Γ)`.

Proof route:
* closedness: `Γ` is closed; if `z_m → z` with `z_m ∈ G_A`, then for `0 < δ < r`,
  `P(z, r - δ) ⊆ P(z_m, r)` for large `m`, so `ν(P(z,r-δ)) ≤ A r^k`; let `δ → 0`
  (`Metric.ball` is the increasing union of the `P(z, r - δ)`,
  `tendsto_measure_iUnion_atTop`), so `ν(P(z,r)) ≤ A r^k`;
* bad mass: every `z ∈ Ω_A` has a radius `r_z > 0` with `ν(P(z,r_z)) > A r_z^k` (choice);
  `A r_z^k < ν(Space n) = ν(Γ) < ∞` and `k ≥ 1` bound the radii; fivefold selection (in the separable
  `Space n`) gives a countable disjoint subfamily whose fivefold dilates cover `Ω_A`; then
  `σ(Ω_A) ≤ Σ C (5 r_j)^k ≤ (C 5^k / A) Σ ν(P(z_j,r_j)) ≤ (C 5^k / A) ν(Γ)` (upper ADR at
  `z_j ∈ Γ`, disjoint Borel balls, `ν(Γᶜ) = 0`);
* nonempty: lower ADR and `k > 0` give `σ(Γ) = ∞` (`σ(Γᶜ) = 0`), while `σ(Ω_A) < ∞`.
For `ν = 0` every point of `Γ` is good and `Ω_A = ∅`. -/
def RpGoodSetStatement : Prop :=
  FivefoldSelectionStatement →
  ∀ n : ℕ, 1 ≤ n →
  ∀ (k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν Γᶜ = 0 → ∀ A : ℝ, 0 < A →
    IsClosed (adrGoodSet Γ ν k A) ∧ (adrGoodSet Γ ν k A).Nonempty ∧
    σ (Γ \ adrGoodSet Γ ν k A) ≤ ENNReal.ofReal (max (C * 5 ^ k) 1 / A) * ν Γ

/-- **(ii.a) Whitney selection.**

Given fivefold selection, under the reference hypotheses, for a closed nonempty `G ⊆ Γ` with
`σ(Γ \ G) < ∞`: there are countably many centres `z_i ∈ Γ \ G` and radii `r_i > 0`,
indexed by `I ⊆ ℕ`, with pairwise disjoint relative balls `B_i = Γ ∩ P(z_i,r_i) ⊆ Γ \ G`,
whose fivefold dilates `P(z_i, 5 r_i)` cover `Γ \ G`, and each centre is within `200 r_i` of
a point of `G`.

Proof route: for `z ∈ Γ \ G`, `s(z) = infDist z G > 0` (`G` closed, nonempty) and
`r_z = s(z)/100`. Since `Γ ∩ P(z, s(z)) ⊆ Γ \ G`, lower ADR gives
`c s(z)^k ≤ σ(Γ \ G) < ∞`, so the radii are bounded. Apply fivefold selection to the balls `P(z, r_z)`,
`z ∈ Γ \ G` (index type the subtype); the selected family `J` is countable and pairwise
disjoint, and its fivefold dilates contain every centre. Reindex `J` by an injection into
`ℕ` (`Set.Countable.toEncodable`, `Encodable.encode`), so `I` is its range. Proximity:
`infDist z G < 2 s(z) = 200 r_z` gives `g ∈ G` with `dist z g < 200 r_z`
(`Metric.exists_dist_lt_of_infDist_lt`). For `Γ \ G = ∅` take `I = ∅`. -/
def RpWhitneySelectionStatement : Prop :=
  FivefoldSelectionStatement →
  ∀ (n k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ G : Set (Space n), IsClosed G → G.Nonempty → G ⊆ Γ → σ (Γ \ G) < ⊤ →
    ∃ (I : Set ℕ) (z : I → Space n) (r : I → ℝ),
      (∀ i, z i ∈ Γ ∧ 0 < r i) ∧
      Pairwise (Disjoint on fun i => Γ ∩ Metric.ball (z i) (r i)) ∧
      (∀ i, Γ ∩ Metric.ball (z i) (r i) ⊆ Γ \ G) ∧
      (Γ \ G ⊆ ⋃ i, Metric.ball (z i) (5 * r i)) ∧
      (∀ i, ∃ g ∈ G, dist (z i) g < 200 * r i)

/-- **(ii.b) Exact allocation and piece bounds.**

For Borel `Γ` and `G_A`, and a family of balls whose fivefold dilates cover `Ω_A` and whose
centres lie within `200 r_i` of `G_A`: there are pairwise disjoint Borel sets
`E_i ⊆ Γ ∩ P(z_i, 5 r_i)` with union exactly `Ω_A` and `ν(E_i) ≤ 205^k A r_i^k`.

Proof route: `F_j = Ω_A ∩ P(z_j, 5 r_j)` for `j ∈ I` and `F_j = ∅` otherwise (`j : ℕ`);
`E_i = disjointed F i` (`MeasurableSet.disjointed`, `disjoint_disjointed`,
`iUnion_disjointed`, `disjointed_subset`). Piece bound: with `g_i ∈ G_A`,
`dist(z_i, g_i) < 200 r_i`, `E_i ⊆ P(z_i, 5r_i) ⊆ P(g_i, 205 r_i)`, and the good-set bound
at `g_i` gives `ν(E_i) ≤ A (205 r_i)^k = 205^k A r_i^k` (`mul_pow`). -/
def RpAllocationStatement : Prop :=
  ∀ (n k : ℕ) (Γ : Set (Space n)) (ν : Measure (Space n)) (A : ℝ),
    MeasurableSet Γ → MeasurableSet (adrGoodSet Γ ν k A) →
  ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ), (∀ i, 0 < r i) →
    (Γ \ adrGoodSet Γ ν k A ⊆ ⋃ i, Metric.ball (z i) (5 * r i)) →
    (∀ i, ∃ g ∈ adrGoodSet Γ ν k A, dist (z i) g < 200 * r i) →
    ∃ E : I → Set (Space n),
      (∀ i, MeasurableSet (E i)) ∧
      (∀ i, E i ⊆ Γ ∩ Metric.ball (z i) (5 * r i)) ∧
      Pairwise (Disjoint on E) ∧
      (⋃ i, E i) = Γ \ adrGoodSet Γ ν k A ∧
      (∀ i, ν (E i) ≤ ENNReal.ofReal (205 ^ k * A * r i ^ k))

/-- **(iii) Domination and mass preservation.**

Under the reference hypotheses, for a finite `ν` carried by `Γ`, `A > 0`, a Borel good set
with the domination `ν⌊G_A ≤ (5^k/c) A σ` (supplied by
`GoodDominationStatement`), and data with centres in `Γ`, positive radii, disjoint relative
balls, disjoint Borel pieces of union `Ω_A` and the piece bounds: the replaced source
`ν_A = b3_replacedSource …` satisfies `ν_A ≤ max ((5^k + 205^k)/c) 1 · A · σ` and
`ν_A(Γ) = ν(Γ)`.

Proof route: `σ(Γᶜ) = 0`; lower and upper ADR give `0 < c r_i^k ≤ σ(B_i) ≤ C r_i^k < ∞`.
Domination (`Measure.le_iff`, measurable `S`):
`Σ_i (m_i / σ(B_i)) σ(S ∩ B_i) ≤ (205^k A / c) Σ_i σ(S ∩ B_i) ≤ (205^k A / c) σ(S)`
(disjoint Borel `B_i`, `Γ` closed), plus `ν⌊G_A ≤ (5^k/c) A σ`; then `(5^k + 205^k)/c ≤ C₁`
and `A > 0`. Mass: `ν_A(Γ) = ν(G_A) + Σ_i m_i = ν(G_A) + ν(Ω_A) = ν(Γ)` (`G_A ⊆ Γ` Borel,
`measure_iUnion` over the disjoint `E_i`, `ENNReal.div_mul_cancel` with
`0 < σ(B_i) < ∞`). -/
def RpAssemblyStatement : Prop :=
  ∀ (n k : ℕ) (c C : ℝ) (Γ : Set (Space n)) (σ : Measure (Space n)),
    IsADRCarrier k c C Γ σ →
  ∀ ν : Measure (Space n), IsFiniteMeasure ν → ν Γᶜ = 0 → ∀ A : ℝ, 0 < A →
    MeasurableSet (adrGoodSet Γ ν k A) →
    ν.restrict (adrGoodSet Γ ν k A) ≤ ENNReal.ofReal (5 ^ k / c * A) • σ →
  ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ) (E : I → Set (Space n)),
    (∀ i, z i ∈ Γ ∧ 0 < r i) →
    Pairwise (Disjoint on fun i => Γ ∩ Metric.ball (z i) (r i)) →
    (∀ i, MeasurableSet (E i)) →
    Pairwise (Disjoint on E) →
    (⋃ i, E i) = Γ \ adrGoodSet Γ ν k A →
    (∀ i, ν (E i) ≤ ENNReal.ofReal (205 ^ k * A * r i ^ k)) →
    b3_replacedSource k Γ σ ν A I z r E ≤
        ENNReal.ofReal (max ((5 ^ k + 205 ^ k) / c) 1 * A) • σ ∧
      b3_replacedSource k Γ σ ν A I z r E Γ = ν Γ

end ParabolicRectifiability.Characterization.ReplacementTree
