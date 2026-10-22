import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # Stopping and packing for the forward covering: data and named statements

Definitions and proposition definitions only. This module fixes the statements below
`StoppingPackingStatement`: the combinatorial stopping data and the named statements of the
component estimates. Their proofs are in the `Forward.Stopping` modules, with assembly in
`StoppingPacking`.

Two branches:
* **Stopping and packing**: the combinatorial stopping of the root forest
  (`StoppingForest`: bad blocks `a_Q > b/2`, hereditary regions with inclusive chain sum `≤ b`,
  and the three ways a root is entered: top cell, child of a bad block, budget exit), the
  per-region exit mass, the first-entrance inequality including the bad-parent
  term, the mass-to-content conversion below a forest cell, root packing, same-family local packing
  with recentring at an eligible root centre, and the bad mass. The packing constant
  `4·192^k·A²` is independent of `b` and `Λ` (the central estimate is
  `∑_{S ⊂ T} μ(S) ≤ (1 + 4M/b) μ(T)`).
* **Typing with exact optimal models**: attainment of
  each family's fitting infimum on a bounded ball (horizontally the joint objective
  `∫ max{dist(x,L)², |t-τ|} dμ`, since a horizontal model carries its time level), attainment of
  the mixed coefficient by an available type, the adjacent-cell type rigidity from the fitting gap
  for `Λ ≥ 3` and `b < 2c/[Λ^p(10^p+1)]`, `p = k+2`, and the assembly of a `GoodRegion` for
  every root.

Conventions: every beta and fit uses the whole original `μ`; masses and energies are `ℝ≥0∞`;
real constants enter through `ENNReal.ofReal`. Cells are addresses `(j, z)`, `z ∈ 𝒵_j`, as in
the first level; tree order is `DirectPartition.IsBelow`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

open ParabolicRectifiability.Foundations

section Data

variable {n : ℕ}

/-! ## Tree facts of a direct partition -/

/-- **Tree facts of a direct partition** (consequences of the fields of `DirectPartition`): positive scales with ratio `1/10`; each cell contains its centre; every cell has
a unique ancestor cell at each coarser level (existence by iterated parents, uniqueness by
same-level disjointness of nonempty cells); `IsBelow` is reflexive on cells and transitive, and
two ancestors of one cell are nested; two cells are nested or disjoint; the root forest of
`P(a,R)` is closed downward and its cells lie in `P(a, R + 4 ℓ₀)`. -/
structure PartitionTree {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀) : Prop where
  scale_pos : ∀ j : ℕ, 0 < P.scale j
  scale_zero : P.scale 0 = ℓ₀
  scale_succ : ∀ j : ℕ, P.scale (j + 1) = P.scale j / 10
  center_mem_cell : ∀ Q : ℕ × Space n, P.IsCell Q → Q.2 ∈ P.cellOf Q
  isBelow_refl : ∀ Q : ℕ × Space n, P.IsCell Q → P.IsBelow Q Q
  isBelow_trans : ∀ Q T U : ℕ × Space n, P.IsBelow Q T → P.IsBelow T U → P.IsBelow Q U
  exists_ancestor : ∀ Q : ℕ × Space n, P.IsCell Q → ∀ j : ℕ, j ≤ Q.1 →
    ∃ T : ℕ × Space n, P.IsCell T ∧ T.1 = j ∧ P.IsBelow Q T
  eq_of_isBelow : ∀ Q T : ℕ × Space n, P.IsCell T → P.IsBelow Q T → Q.1 = T.1 → Q = T
  isBelow_of_common : ∀ Q T U : ℕ × Space n, P.IsCell T → P.IsCell U →
    P.IsBelow Q T → P.IsBelow Q U → T.1 ≤ U.1 → P.IsBelow U T
  isBelow_or_disjoint : ∀ Q T : ℕ × Space n, P.IsCell Q → P.IsCell T → T.1 ≤ Q.1 →
    P.IsBelow Q T ∨ Disjoint (P.cellOf Q) (P.cellOf T)
  inForest_of_isBelow : ∀ (a : Space n) (R : ℝ) (Q T : ℕ × Space n),
    P.InForest a R T → P.IsBelow Q T → P.InForest a R Q
  inForest_subset : ∀ (a : Space n) (R : ℝ) (Q : ℕ × Space n),
    P.InForest a R Q → P.cellOf Q ⊆ Metric.ball a (R + 4 * ℓ₀)

/-! ## The combinatorial stopping -/

/-- The inclusive chain sum `∑_{Q' ∈ 𝒮, Q ⊆ Q'} a_{Q'}` of the coefficients of the cells of a set
`𝒮` (a region) lying above `Q`. For a member `Q` of a hereditary region below its
root this is the sum over the chain from the root down to `Q`, one cell per level. -/
def chainSum {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ : ℝ) (𝒮 : Set (ℕ × Space n)) (Q : ℕ × Space n) : ℝ≥0∞ :=
  ∑' Q' : {Q' : ℕ × Space n // Q' ∈ 𝒮 ∧ P.IsBelow Q Q'}, P.coeff μ k Λ Q'.1

/-- **The combinatorial stopping of the root forest** of `P(a,R)` at threshold `b`, before any typing: bad blocks (`a_Q > b/2`) and roots of good regions,
both in the root forest; the region `members S` of a root `S` is hereditary below `S`, contains
`S`, has only nonbad cells and inclusive chain sums `≤ b`; every forest cell is bad or in exactly
one region; and every root is entered in one of three ways: it is a top cell,
or its parent is a bad block (the restart below a bad block), or it is a budget exit from the
region of a root `S'` containing its parent `Q`, and then the chain sum above `Q` exceeds `b/2`
(since `∑_{Q_* ⊇ Q' ⊋ S} a_{Q'} > b - a_S ≥ b/2`). No measure property is used. -/
structure StoppingForest {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (μ : Measure (Space n)) (k : ℕ) (Λ b : ℝ) (a : Space n) (R : ℝ) where
  bad : Set (ℕ × Space n)
  roots : Set (ℕ × Space n)
  /-- The members of the region of a root (junk for non-roots). -/
  members : ℕ × Space n → Set (ℕ × Space n)
  bad_forest : ∀ Q ∈ bad, P.InForest a R Q
  roots_forest : ∀ S ∈ roots, P.InForest a R S
  bad_coeff : ∀ Q ∈ bad, ENNReal.ofReal (b / 2) < P.coeff μ k Λ Q
  root_mem : ∀ S ∈ roots, S ∈ members S
  below_root : ∀ S ∈ roots, ∀ Q ∈ members S, P.IsBelow Q S
  hereditary : ∀ S ∈ roots, ∀ Q ∈ members S, ∀ Q' : ℕ × Space n,
    P.IsBelow Q Q' → P.IsBelow Q' S → Q' ∈ members S
  member_coeff : ∀ S ∈ roots, ∀ Q ∈ members S, P.coeff μ k Λ Q ≤ ENNReal.ofReal (b / 2)
  chain_budget : ∀ S ∈ roots, ∀ Q ∈ members S, chainSum P μ k Λ (members S) Q ≤ ENNReal.ofReal b
  classify : ∀ Q : ℕ × Space n, P.InForest a R Q →
    (Q ∈ bad ∧ ∀ S : roots, Q ∉ members S.1) ∨ (Q ∉ bad ∧ ∃! S : roots, Q ∈ members S.1)
  root_entry : ∀ S ∈ roots, S.1 = 0 ∨
    (∃ Q ∈ bad, Q.1 + 1 = S.1 ∧ P.IsBelow S Q) ∨
    (∃ S' ∈ roots, ∃ Q ∈ members S', Q.1 + 1 = S.1 ∧ P.IsBelow S Q ∧
      ENNReal.ofReal (b / 2) < chainSum P μ k Λ (members S') Q)

/-- The exits of the region of `S'`: the roots whose parent cell is a member of that region
(by `root_entry` and `classify` these are exactly the budget exits of that region). -/
def StoppingForest.exits {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} {a : Space n} {R : ℝ}
    (F : StoppingForest P μ k Λ b a R) (S' : ℕ × Space n) : Set (ℕ × Space n) :=
  {S | S ∈ F.roots ∧ ∃ Q ∈ F.members S', Q.1 + 1 = S.1 ∧ P.IsBelow S Q}

end Data

/-! ## Stopping and packing -/

/-- **Tree facts** hold for every direct partition of every set. -/
def PartitionTreeStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀), PartitionTree P

/-- **The combinatorial stopping exists** for every direct partition, source,
coefficient dilation, threshold `b > 0` and root ball. -/
def StoppingForestStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (a : Space n) (R : ℝ), 0 < b → Nonempty (StoppingForest P μ k Λ b a R)

/-- **Exit mass**: for every root `S'`,
`(b/2) ∑_{S exit of S'} μ(S) ≤ ∑_{Q in the region of S'} a_Q μ(Q)`. -/
def ExitMassStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (a : Space n) (R : ℝ), 0 < b →
    ∀ F : StoppingForest P μ k Λ b a R, ∀ S' ∈ F.roots,
      ENNReal.ofReal (b / 2) * (∑' S : F.exits S', μ (P.cellOf S.1)) ≤
        ∑' Q : F.members S', P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)

/-- **The first-entrance inequality** for every
cell `T`: with `ℛ` the roots and the bad blocks,
`∑_{S ∈ ℛ, S ⊂ T} μ(S) ≤ μ(T) + (4/b) ∑_{Q ⊂ T} a_Q μ(Q)`. The first-entrance roots inside `T`
form an antichain (mass `≤ μ(T)`); a bad block costs `(2/b) a_Q μ(Q)` and the same again for its
child roots; a later budget exit is charged to a region whose root lies inside `T` by the exit mass bound. This
accounts for energy above `T`, including a bad parent above it. -/
def FirstEntranceStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (a : Space n) (R : ℝ), 0 < b →
    ∀ F : StoppingForest P μ k Λ b a R, ∀ T : ℕ × Space n, P.IsCell T →
      (∑' S : {S : ℕ × Space n // (S ∈ F.roots ∨ S ∈ F.bad) ∧ P.IsBelow S T},
          μ (P.cellOf S.1)) ≤
        μ (P.cellOf T) + ENNReal.ofReal (4 / b) * P.descendantEnergy μ k Λ T

/-- **Root content below a forest cell**: with local ADR in `P(a, ρ)`,
`5R ≤ ρ`, and the forest energy `∑_{Q ⊂ T} a_Q μ(Q) ≤ M μ(T)`, every forest cell `T` has
`∑_{S root, S ⊂ T} (4 ℓ_S)^k ≤ 16^k A (1 + 4M/b) μ(T)` (by the first-entrance inequality and
`ℓ_S^k ≤ 4^k A μ(S)` from the lower cell mass). -/
def RootContentStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (A : ℝ) (a : Space n) (R ρ Λ b M : ℝ),
    1 ≤ A → 0 < R → 5 * R ≤ ρ → 0 < b → 0 ≤ M → LocalADR μ k A a ρ →
    ∀ (P : DirectPartition μ.support R) (F : StoppingForest P μ k Λ b a R),
      (∀ T : ℕ × Space n, P.InForest a R T →
        P.descendantEnergy μ k Λ T ≤ ENNReal.ofReal M * μ (P.cellOf T)) →
      ∀ T : ℕ × Space n, P.InForest a R T →
        (∑' S : {S : ℕ × Space n // S ∈ F.roots ∧ P.IsBelow S T},
            ENNReal.ofReal (4 * P.scale S.1.1) ^ k) ≤
          ENNReal.ofReal (16 ^ k * A * (1 + 4 * M / b)) * μ (P.cellOf T)

/-- **Root packing**: `∑_S (4 ℓ_S)^k ≤ 80^k A² (1 + 4M/b) R^k` over all good roots
(group under the disjoint top cells, which lie in `P(a, 5R)`; upper ADR at `a`). -/
def RootPackingStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (A : ℝ) (a : Space n) (R ρ Λ b M : ℝ),
    1 ≤ A → a ∈ μ.support → 0 < R → 5 * R ≤ ρ → 0 < b → 0 ≤ M → LocalADR μ k A a ρ →
    ∀ (P : DirectPartition μ.support R) (F : StoppingForest P μ k Λ b a R),
      (∀ T : ℕ × Space n, P.InForest a R T →
        P.descendantEnergy μ k Λ T ≤ ENNReal.ofReal M * μ (P.cellOf T)) →
      (∑' S : F.roots, ENNReal.ofReal (4 * P.scale S.1.1) ^ k) ≤
        ENNReal.ofReal (80 ^ k * A ^ 2 * (1 + 4 * M / b) * R ^ k)

open scoped Classical in
/-- **Same-family local packing** with recentring:
`∑_{z_S ∈ P(w,s), 4 ℓ_S ≤ s} (4 ℓ_S)^k ≤ 192^k A² (1 + 4M/b) s^k` for every `w`, `s > 0`, for
the one family of roots already constructed (no reselection per test). Tests `s ≥ R` use root
packing; for `s < R` group the eligible roots under their ancestors at the level `j ≥ 0` with
`s/4 ≤ ℓ_j < 10s/4`; these disjoint forest cells lie in `P(z_{S₀}, 12 s)` for any eligible root
centre `z_{S₀} ∈ supp μ ∩ P(a, 5R)`, where local upper ADR applies (`12 s ≤ 12 R ≤ ρ`). -/
def LocalPackingStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (A : ℝ) (a : Space n) (R ρ Λ b M : ℝ),
    1 ≤ A → a ∈ μ.support → 0 < R → 12 * R ≤ ρ → 0 < b → 0 ≤ M → LocalADR μ k A a ρ →
    ∀ (P : DirectPartition μ.support R) (F : StoppingForest P μ k Λ b a R),
      (∀ T : ℕ × Space n, P.InForest a R T →
        P.descendantEnergy μ k Λ T ≤ ENNReal.ofReal M * μ (P.cellOf T)) →
      ∀ (w : Space n) (s : ℝ), 0 < s →
        (∑' S : F.roots, if S.1.2 ∈ Metric.ball w s ∧ 4 * P.scale S.1.1 ≤ s then
            ENNReal.ofReal (4 * P.scale S.1.1) ^ k else 0) ≤
          ENNReal.ofReal (192 ^ k * A ^ 2 * (1 + 4 * M / b) * s ^ k)

/-- **Bad mass**: `∑_{Q bad} μ(Q) ≤ (2M/b) A (5R)^k`, from
`μ(Q) ≤ (2/b) a_Q μ(Q)` for a bad block, the forest energy at the top cells and upper ADR at `a`. -/
def BadMassStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (A : ℝ) (a : Space n) (R ρ Λ b M : ℝ),
    1 ≤ A → a ∈ μ.support → 0 < R → 5 * R ≤ ρ → 0 < b → 0 ≤ M → LocalADR μ k A a ρ →
    ∀ (P : DirectPartition μ.support R) (F : StoppingForest P μ k Λ b a R),
      (∀ T : ℕ × Space n, P.InForest a R T →
        P.descendantEnergy μ k Λ T ≤ ENNReal.ofReal M * μ (P.cellOf T)) →
      (∑' Q : F.bad, μ (P.cellOf Q.1)) ≤ ENNReal.ofReal (2 * M / b * (A * (5 * R) ^ k))

/-! ## Typing with exact optimal models -/

/-- **Exact family optimizers**: for a source finite on compacts and
an available type `T`, the fitting infimum of the family `T` on every ball `P(z, r)` is attained.
Horizontally the model carries its time level and `fit` integrates
`d_P(w, L)² = max{dist(x, a+U)², |t - τ|}`: the joint objective, not a covariance minimizer plus
a separate median. -/
def ExactModelStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)), IsFiniteMeasureOnCompacts μ →
    ∀ T : NeckType, T.Available n k → ∀ (z : Space n) (r : ℝ),
      ∃ L : Models n k T.toFamilyKind, ∀ L' : Models n k T.toFamilyKind,
        fit μ L z r ≤ fit μ L' z r

/-- **The mixed coefficient is attained by an available type**: for
`1 ≤ k < n + 2`, some available type has a model whose fit on `P(z, r)` is at most that of every
mixed model. -/
def MixedAttainmentStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → ∀ (z : Space n) (r : ℝ),
      ∃ T : NeckType, T.Available n k ∧ ∃ L : Models n k T.toFamilyKind,
        ∀ L' : Models n k .mixed, fit μ L z r ≤ fit μ L' z r

/-- **Adjacent-cell type rigidity**:
for `Λ ≥ 3` there is `b₀ > 0` (one may take `b₀ = c/[Λ^p(10^p+1)]`, `p = k + 2`, `c` the fitting
gap constant) such that for `0 < b ≤ b₀` no parent/child pair of cells `Q' ⊃ Q`, with
`P(z_Q, 4 ℓ_Q)` in the ADR buffer, carries a horizontal and a vertical model, one on each cell,
both with normalized error `≤ b/2` on the coefficient balls `P(z, Λ ℓ)`: the ball `P(z_Q, ℓ_Q)`
lies in both coefficient balls, so the fitting gap would give `c ℓ_Q^p ≤ (b/2) Λ^p (10^p + 1) ℓ_Q^p`. -/
def AdjacentTypeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A → ∀ Λ : ℝ, 3 ≤ Λ →
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ (μ : Measure (Space n)) (a : Space n) (ρ ℓ₀ : ℝ), LocalADR μ k A a ρ →
    ∀ (P : DirectPartition μ.support ℓ₀) (Q Q' : ℕ × Space n), P.IsCell Q' →
      P.IsBelow Q Q' → Q'.1 + 1 = Q.1 →
      Metric.ball Q.2 (4 * P.scale Q.1) ⊆ Metric.ball a ρ → 4 * P.scale Q.1 ≤ ρ →
      ∀ (H : Models n k .horizontal) (V : Models n k .vertical),
        ¬ ((P.modelCoeff μ Λ H Q ≤ ENNReal.ofReal (b / 2) ∧
              P.modelCoeff μ Λ V Q' ≤ ENNReal.ofReal (b / 2)) ∨
            (P.modelCoeff μ Λ V Q ≤ ENNReal.ofReal (b / 2) ∧
              P.modelCoeff μ Λ H Q' ≤ ENNReal.ofReal (b / 2)))

/-- **Typed good regions with exact optimal models**: for
`Λ ≥ 3` there is `b₀ > 0` such that for `0 < b ≤ b₀`, local ADR in `P(a, ρ)` with `9R ≤ ρ`, every
root of every combinatorial stopping of a direct partition of the support from `ℓ₀ = R` carries
a `GoodRegion` with that root and exactly that region: one available type `T` (a type attaining
the mixed coefficient at the root), the `T`-optimizer of every member's coefficient ball as its
model, which attains the mixed coefficient (induction down the chain by adjacent-type
rigidity), and the budget from the chain budget. -/
def RegionTypingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A → ∀ Λ : ℝ, 3 ≤ Λ →
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ →
    ∀ (a : Space n) (R ρ : ℝ), 0 < R → 9 * R ≤ ρ → LocalADR μ k A a ρ →
    ∀ (P : DirectPartition μ.support R) (F : StoppingForest P μ k Λ b a R), ∀ S ∈ F.roots,
      ∃ G : GoodRegion P μ k Λ b, G.root = S ∧ G.members = F.members S

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
