import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # Coverage assembly of the forward covering: slabs and named statements

Definitions and proposition definitions only. This module fixes the statements below
`CoverageAssemblyStatement`: the exact point/scale slabs and the named statements of the component
estimates. Their proofs are in the `Forward.Coverage` modules, with assembly in
`d1fcomp_coverageAssembly_of`.

The covering at one support-centred root `P₀ = P(a,R)` (direct partition from `ℓ₀ = R`, ratio
`h = 1/10`, a stopping decomposition `SD` with packing constant `K`):
* the **slab** of a cell `Q` is `(Q ∩ P₀) × [ℓ_Q/10, ℓ_Q)`; the slabs of the forest
  cells partition the tested pairs `(P₀ ∩ E) × (0,R)` exactly (no null set is discarded);
* the bad set `𝓑` is the union of the bad slabs; its cost is `log 10 · ∑_{bad} μ(Q) ≤ (log 10) K R^k`
  (with the bad mass of `SD`), so `C₆ = 3`;
* the good root `S` (indexed in `ℕ` through a bijection `I ≃ roots`, `I ⊆ ℕ`) receives the slabs
  of its region's cells as `𝓤_S`, its reference `Γ_S`, and the model ball `P(z_S, 4 ℓ_S)`;
* with the sharp constant:
  `d_P(z, Γ_S) ≤ ℓ_Q/99` for `z ∈ Q ∈ 𝒯`, so the distance floor `L⁻¹ d_P(z,Γ_S) ≤ ℓ_Q/10 ≤ r`
  needs only `L ≥ 10/99`; `z_S ∈ P(a,5R)` and `4 ℓ_S ≤ 4R` give `P(z_S,4ℓ_S) ⊆ P(a,9R)`, so
  `L ≥ 9` gives containment. This improves the cruder sufficient choice `L₀ ≥ 80`
  (`L₀⁻¹ ≤ h/(4 C_d)` with `C_d = 2`); here `L₀ = 9`.

This step takes no ADR hypothesis; `C = 3`, `L₀ = 9` depend on nothing. The stopping-scale
Lipschitz lemma (`Terminal.StopScaleLipschitzStatement`) is the only input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

section Data

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}

/-- The exact slab `(Q ∩ P₀) × [ℓ_Q/10, ℓ_Q)` of a cell `Q` at the root `P₀ = P(a,R)` (`h = 1/10`). -/
def slab (P : DirectPartition E ℓ₀) (a : Space n) (R : ℝ) (Q : ℕ × Space n) :
    Set (Space n × ℝ) :=
  (P.cellOf Q ∩ Metric.ball a R) ×ˢ Ico (P.scale Q.1 / 10) (P.scale Q.1)

variable {P : DirectPartition E ℓ₀} {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {a : Space n}
  {R K : ℝ}

/-- The bad set `𝓑`: the union of the slabs of the bad cells. -/
def badSlabs (SD : StoppingDecomposition P μ k Λ b a R K) : Set (Space n × ℝ) :=
  ⋃ Q ∈ SD.bad, slab P a R Q

/-- The scale set `𝓤_S` of a good root `S`: the union of the slabs of the cells of its region. -/
def goodSlabs (SD : StoppingDecomposition P μ k Λ b a R K) (S : SD.roots) :
    Set (Space n × ℝ) :=
  ⋃ Q ∈ (SD.region S).members, slab P a R Q

end Data

/-! ## Coverage -/

/-- **Coverage with the constant `1/99`.** For any good region, any terminal construction from it and any set `Γ`
containing its centres, every point `z` of a member cell `Q` has `d_P(z, Γ) ≤ ℓ_Q/99`. Core points
lie in `Γ`; an assigned point `z ∈ A_c` has `100 d_c ≤ ρ(c) ≤ ρ(z) + d_P(z,c) < ℓ_Q + d_c`. -/
def CoverageStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (δ κ θ γ : ℝ) (TN : TerminalNeck 𝒢 δ κ θ γ)
    (Γ : Set (Space n)), TN.centers ⊆ Γ →
    ∀ Q ∈ 𝒢.members, ∀ z ∈ P.cellOf Q, Metric.infDist z Γ ≤ P.scale Q.1 / 99

/-- **The good scale sets are covered by their references** (the scale cover): for `L ≥ 10/99`, every pair `(z,r)` of the scale set of a
good root `S` has `z ∈ P₀ ∩ P(z_S, 4 ℓ_S)`, `L⁻¹ d_P(z, Γ) ≤ r` and `r < 4 ℓ_S`, for any `Γ`
containing the centres of a terminal construction of the region of `S`. -/
def GoodSlabCoverStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R)
    (k : ℕ) (Λ b K : ℝ) (SD : StoppingDecomposition P μ k Λ b a R K) (S : SD.roots)
    (δ κ θ γ : ℝ) (TN : TerminalNeck (SD.region S) δ κ θ γ) (Γ : Set (Space n)),
    TN.centers ⊆ Γ → ∀ L : ℝ, 10 / 99 ≤ L →
    goodSlabs SD S ⊆
      {p : Space n × ℝ | p.1 ∈ Metric.ball a R ∩ Metric.ball S.1.2 (4 * P.scale S.1.1) ∧
        L⁻¹ * Metric.infDist p.1 Γ ≤ p.2 ∧ p.2 < 4 * P.scale S.1.1}

/-! ## The exact slabs -/

/-- **Slab basics**: the cells of a direct partition of `supp μ` are countably many;
every slab is Borel; the slab of a cell lies in the tested pairs `(P₀ ∩ E) × (0,R)`. -/
def SlabBasicsStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R),
    {Q : ℕ × Space n | P.IsCell Q}.Countable ∧ (∀ Q, MeasurableSet (slab P a R Q)) ∧
    ∀ Q, P.IsCell Q → slab P a R Q ⊆ rootPairs μ a R

/-- **Slab cover**: every tested pair `(z,r)`, `z ∈ P₀ ∩ E`,
`0 < r < R`, lies in the slab of a cell of the root forest (the level `j` with
`ℓ_j/10 ≤ r < ℓ_j`, the level-`j` cell containing `z`, below the top cell containing `z`). -/
def SlabCoverStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R),
    ∀ p ∈ rootPairs μ a R, ∃ Q : ℕ × Space n, P.InForest a R Q ∧ p ∈ slab P a R Q

/-- **Slab disjointness**: distinct cell addresses have disjoint slabs (same level:
disjoint cells; different levels: disjoint scale intervals). -/
def SlabDisjointStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (a : Space n) (R : ℝ)
    (Q Q' : ℕ × Space n), P.IsCell Q → P.IsCell Q' → Q ≠ Q' →
    Disjoint (slab P a R Q) (slab P a R Q')

/-- **The slab families are Borel subsets of the tested pairs** (measurability and containment). -/
def SlabFamilyStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R)
    (k : ℕ) (Λ b K : ℝ) (SD : StoppingDecomposition P μ k Λ b a R K),
    MeasurableSet (badSlabs SD) ∧ (∀ S, MeasurableSet (goodSlabs SD S)) ∧
    badSlabs SD ⊆ rootPairs μ a R ∧ ∀ S, goodSlabs SD S ⊆ rootPairs μ a R

/-- **The slab families partition the tested pairs exactly**: the bad
set misses every good scale set, the scale sets of distinct roots are disjoint, and together they
cover `(P₀ ∩ E) × (0,R)` (every forest cell is bad or in exactly one region). -/
def SlabPartitionStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R)
    (k : ℕ) (Λ b K : ℝ) (SD : StoppingDecomposition P μ k Λ b a R K),
    (∀ S, Disjoint (badSlabs SD) (goodSlabs SD S)) ∧
    (∀ S S', S ≠ S' → Disjoint (goodSlabs SD S) (goodSlabs SD S')) ∧
    rootPairs μ a R ⊆ badSlabs SD ∪ ⋃ S, goodSlabs SD S

/-! ## The bad cost -/

/-- **The bad cost**: `∬_𝓑 dμ dr/r ≤ log 10 · ∑_{bad} μ(Q) ≤
(log 10) K R^k` (`dr/r` of `[ℓ/10, ℓ)` is `log 10`; the bad mass of `SD`). -/
def BadCostStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R)
    (k : ℕ) (Λ b K : ℝ) (SD : StoppingDecomposition P μ k Λ b a R K),
    pointScaleMeasure μ (badSlabs SD) ≤ ENNReal.ofReal (Real.log 10 * (K * R ^ k))

/-! ## Model balls and indexing -/

/-- **The model balls**: for a good root `S` and any `Γ` containing
the centres of a terminal construction of its region, the centre `z_S` is in `supp μ`, the radius
`4 ℓ_S` is positive, `P(z_S, 4 ℓ_S) ⊆ P(a, 9R)` (`z_S ∈ P(a,5R)`, `ℓ_S ≤ R`), and the ball meets
`Γ` (the centres lie in `closure S ⊆ closedBall(z_S, 2 ℓ_S)`). -/
def ModelBallStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R)
    (k : ℕ) (Λ b K : ℝ) (SD : StoppingDecomposition P μ k Λ b a R K) (S : SD.roots)
    (δ κ θ γ : ℝ) (TN : TerminalNeck (SD.region S) δ κ θ γ) (Γ : Set (Space n)),
    TN.centers ⊆ Γ →
    S.1.2 ∈ μ.support ∧ 0 < 4 * P.scale S.1.1 ∧
      Metric.ball S.1.2 (4 * P.scale S.1.1) ⊆ Metric.ball a (9 * R) ∧
      (Metric.ball S.1.2 (4 * P.scale S.1.1) ∩ Γ).Nonempty

/-- **Indexing of the good roots in `ℕ`** (families indexed by a subset of
`ℕ`): the roots of a stopping decomposition, a set of cell addresses, are in bijection with a
subset of `ℕ`. -/
def IndexingStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (Space n)) (a : Space n) (R : ℝ) (P : DirectPartition μ.support R)
    (k : ℕ) (Λ b K : ℝ) (SD : StoppingDecomposition P μ k Λ b a R K),
    ∃ I : Set ℕ, Nonempty (I ≃ SD.roots)

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
