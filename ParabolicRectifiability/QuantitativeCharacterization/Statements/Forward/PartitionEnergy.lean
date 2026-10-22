import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ForwardCovering
import ParabolicRectifiability.Geometry.Neck.Collapse
import ParabolicRectifiability.Geometry.CovarianceComparison

/-! # Partition energy for the forward covering: data and named statements

Definitions and proposition definitions only. This module fixes the statements below
`PartitionEnergyStatement`: the intermediate data of the direct-partition construction and the
named statements of its component estimates.

Two branches:
* **Global direct partitions** of a closed set: nested separated nets built by an extension
  construction that keeps the earlier nets (`NetExtensionStatement`, `NestedNets`), nearest
  parents with the forced-parent property, closed descendant cells and the cover
  (`NestedNets.ClosedCellBasics`), the unique inner cell (`NestedNets.UniqueInner`), the ordered
  parent-intersection Borel assignment with its closure identity and inner inclusion
  (`NestedNets.AssignedCells`), the child count and the protected balls.
* **Local ADR and discrete energy**: coefficient-to-annulus comparison
  (`CoeffAnnulusStatement`), ADR cell masses (`CellMassStatement`), the descendant sum below a
  cell bounded by the integrated square energy (`DescendantIntegralStatement`), and the forest
  estimate (`ForestEnergyStatement`).

**Shared named statements.** They are locally formulated: a local ADR hypothesis
`LocalADR μ k A a ρ` in a buffer `P(a, ρ)`, a testing ball whose four-fold enlargement lies in
that buffer, and no reference to the partition built by the construction (`CellMassStatement`
quantifies over every direct partition of the support):
* `UpperRecenteringStatement` (`A_* = 2^k A`);
* `PointToFitStatement`;
* `CovarianceLowerStatement` (horizontal small-error variant),
  in the exact form of the continuation test of the base `ms3_core_comparison`;
* `PlaneComparisonStatement`, including vertical rank zero;
* `FittingGapStatement`;
* `CellMassStatement` (with lower and upper ADR).

Conventions: every beta, fit and covariance source is the original `μ`; the covariance tests are
applied to any finite measure that agrees with `μ` on the tested ball.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

open ParabolicRectifiability.Foundations

section Data

variable {n : ℕ}

/-! ## Nested nets and closed descendant cells -/

/-- **Nested separated nets with nearest parents** of a set `E` from the top
scale `ℓ₀`, ratio `h = 1/10`: countable centre sets `𝒵_j ⊆ E`, nested in `j`,
`ℓ_j`-separated, covering `E` at distance `≤ ℓ_j` (`ℓ_j = coherentScale ℓ₀ j = 10^{-j} ℓ₀`), and
for each `w ∈ 𝒵_{j+1}` a parent `parent j w ∈ 𝒵_j` nearest to `w`. The forced-parent property
and `parent j w = w` for a persisting centre follow from `parent_nearest` and the
separation. -/
structure NestedNets (E : Set (Space n)) (ℓ₀ : ℝ) where
  scale_pos : 0 < ℓ₀
  /-- The centre set `𝒵_j`. -/
  center : ℕ → Set (Space n)
  /-- The nearest parent `parent j w ∈ 𝒵_j` of `w ∈ 𝒵_{j+1}`. -/
  parent : ℕ → Space n → Space n
  center_subset : ∀ j, center j ⊆ E
  center_countable : ∀ j, (center j).Countable
  center_mono : ∀ j, center j ⊆ center (j + 1)
  center_separated : ∀ j, ∀ z ∈ center j, ∀ z' ∈ center j, z ≠ z' →
    coherentScale ℓ₀ j ≤ dist z z'
  center_cover : ∀ j, ∀ x ∈ E, ∃ z ∈ center j, dist x z ≤ coherentScale ℓ₀ j
  parent_mem : ∀ j, ∀ w ∈ center (j + 1), parent j w ∈ center j
  parent_nearest : ∀ j, ∀ w ∈ center (j + 1), ∀ z ∈ center j, dist w (parent j w) ≤ dist w z

namespace NestedNets

variable {E : Set (Space n)} {ℓ₀ : ℝ}

/-- The level-`j` ancestor of a level-`(j + d)` centre: `d` parent steps upward. -/
def ancestor (N : NestedNets E ℓ₀) (j : ℕ) : ℕ → Space n → Space n
  | 0, w => w
  | d + 1, w => ancestor N j d (N.parent (j + d) w)

/-- The children `{w ∈ 𝒵_{j+1} : parent j w = z}` of `(j, z)`. -/
def children (N : NestedNets E ℓ₀) (j : ℕ) (z : Space n) : Set (Space n) :=
  {w | w ∈ N.center (j + 1) ∧ N.parent j w = z}

/-- The descendant centres `D_{j,z}`: centres of every level `j + d` whose
level-`j` ancestor is `z` (equality allowed, `d = 0`). -/
def descendants (N : NestedNets E ℓ₀) (j : ℕ) (z : Space n) : Set (Space n) :=
  {w | ∃ d : ℕ, w ∈ N.center (j + d) ∧ N.ancestor j d w = z}

/-- The closed descendant cell `C_{j,z} = closure D_{j,z}`. -/
def closedCell (N : NestedNets E ℓ₀) (j : ℕ) (z : Space n) : Set (Space n) :=
  closure (N.descendants j z)

/-- **Closed-cell facts**: the closed cells lie in `E` and, by the drift,
in `P(z, 2 ℓ_j)`; each is the finite union of its children's closed cells; every level
of closed cells covers `E`. -/
structure ClosedCellBasics (N : NestedNets E ℓ₀) : Prop where
  closedCell_subset : ∀ j z, N.closedCell j z ⊆ E
  closedCell_subset_ball : ∀ j, ∀ z ∈ N.center j,
    N.closedCell j z ⊆ Metric.ball z (2 * coherentScale ℓ₀ j)
  closedCell_children : ∀ j, ∀ z ∈ N.center j,
    N.closedCell j z = ⋃ w ∈ N.children j z, N.closedCell (j + 1) w
  closedCell_cover : ∀ j, E ⊆ ⋃ z ∈ N.center j, N.closedCell j z

/-- **The unique inner cell**: for distinct level-`j` centres `z ≠ z'`,
`E ∩ P(z, ℓ_j/4)` misses the closed cell `C_{j,z'}`. -/
def UniqueInner (N : NestedNets E ℓ₀) : Prop :=
  ∀ j, ∀ z ∈ N.center j, ∀ z' ∈ N.center j, z ≠ z' →
    E ∩ Metric.ball z (coherentScale ℓ₀ j / 4) ∩ N.closedCell j z' = ∅

/-- **Exact nested Borel cells**: Borel
cells `Q_{j,z}`, `z ∈ 𝒵_j`, pairwise disjoint at each level with union exactly `E`, each with
closure the closed cell `C_{j,z}`, containing `E ∩ P(z, ℓ_j/4)`, and contained in the cell of
its parent. -/
structure AssignedCells (N : NestedNets E ℓ₀) where
  cell : ℕ → Space n → Set (Space n)
  measurable_cell : ∀ j z, MeasurableSet (cell j z)
  cell_disjoint : ∀ j, ∀ z ∈ N.center j, ∀ z' ∈ N.center j, z ≠ z' →
    Disjoint (cell j z) (cell j z')
  cell_cover : ∀ j, (⋃ z ∈ N.center j, cell j z) = E
  closure_cell : ∀ j, ∀ z ∈ N.center j, closure (cell j z) = N.closedCell j z
  inner_subset : ∀ j, ∀ z ∈ N.center j,
    E ∩ Metric.ball z (coherentScale ℓ₀ j / 4) ⊆ cell j z
  cell_subset_parent : ∀ j, ∀ w ∈ N.center (j + 1), cell (j + 1) w ⊆ cell j (N.parent j w)

end NestedNets

end Data

/-! ## Global direct partitions -/

/-- **Net extension**: every `s`-separated subset
`Z₀` of a closed set `E` extends to a countable `s`-separated `Z ⊆ E` with `Z₀ ⊆ Z` covering `E`
at distance `≤ s`. (Greedy retention along a countable dense subset of `E`, starting from all of
`Z₀`; separated sets are locally finite in the proper space.) -/
def NetExtensionStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)), IsClosed E → ∀ s : ℝ, 0 < s →
    ∀ Z₀ : Set (Space n), Z₀ ⊆ E → (∀ z ∈ Z₀, ∀ z' ∈ Z₀, z ≠ z' → s ≤ dist z z') →
      ∃ Z : Set (Space n), Z₀ ⊆ Z ∧ Z ⊆ E ∧ Z.Countable ∧
        (∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → s ≤ dist z z') ∧ ∀ x ∈ E, ∃ z ∈ Z, dist x z ≤ s

/-- **Nested nets with nearest parents exist** for every closed `E` and `ℓ₀ > 0`. -/
def NestedNetsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)), IsClosed E → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → Nonempty (NestedNets E ℓ₀)

/-- **Closed descendant cells** (with the level cover) of any nested
nets of a closed set. -/
def ClosedCellBasicsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (N : NestedNets E ℓ₀), IsClosed E → N.ClosedCellBasics

/-- **Unique inner cell**, from the forced-parent property and the
tails. -/
def UniqueInnerStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (N : NestedNets E ℓ₀), IsClosed E →
    N.ClosedCellBasics → N.UniqueInner

/-- **Child count** (item (iii)): at most `(1 + 3/h)^{n+2} = 31^{n+2}` children,
by disjoint parabolic balls of radius `h ℓ_j / 3` in `P(z, (1 + h/3) ℓ_j)`. -/
def ChildrenCountStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (N : NestedNets E ℓ₀), ∀ j, ∀ z ∈ N.center j,
    {w | w ∈ N.center (j + 1) ∧ N.parent j w = z}.encard ≤ (31 : ℕ∞) ^ (n + 2)

/-- **Exact Borel assignment** (with the lower inclusion of the inner balls). -/
def AssignmentStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (N : NestedNets E ℓ₀), IsClosed E →
    N.ClosedCellBasics → N.UniqueInner → Nonempty N.AssignedCells

/-- **Protected balls** for any assigned cells: if `j ≤ l` and the level-`l`
cell of `w` is not contained in the level-`j` cell of `z`, each open inner ball misses the
closure of the other cell. -/
def ProtectedBallsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (N : NestedNets E ℓ₀), IsClosed E →
    N.ClosedCellBasics → N.UniqueInner → ∀ C : N.AssignedCells,
    ∀ j l, j ≤ l → ∀ z ∈ N.center j, ∀ w ∈ N.center l, ¬ C.cell l w ⊆ C.cell j z →
      E ∩ Metric.ball z (coherentScale ℓ₀ j / 4) ∩ closure (C.cell l w) = ∅ ∧
        E ∩ Metric.ball w (coherentScale ℓ₀ l / 4) ∩ closure (C.cell j z) = ∅

/-- **Direct partitions exist** (ratio `h = 1/10`) for
every closed set `E` and top scale `ℓ₀ > 0`. -/
def DirectPartitionExistsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)), IsClosed E → ∀ ℓ₀ : ℝ, 0 < ℓ₀ → Nonempty (DirectPartition E ℓ₀)

/-! ## Branch E: local ADR and the discrete energy -/

/-- **ADR cell masses.** For every direct partition of the support of
`μ` (any top scale), local ADR in `P(a, ρ)` and a cell `Q` with centre in `P(a, ρ)` and
`2 ℓ_Q ≤ ρ`: `A⁻¹ (ℓ_Q/4)^k ≤ μ(Q) ≤ A (2 ℓ_Q)^k`. -/
def CellMassStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (A : ℝ) (a : Space n) (ρ ℓ₀ : ℝ)
    (P : DirectPartition μ.support ℓ₀), LocalADR μ k A a ρ →
    ∀ Q : ℕ × Space n, P.IsCell Q → Q.2 ∈ Metric.ball a ρ → 2 * P.scale Q.1 ≤ ρ →
      ENNReal.ofReal (A⁻¹ * (P.scale Q.1 / 4) ^ k) ≤ μ (P.cellOf Q) ∧
        μ (P.cellOf Q) ≤ ENNReal.ofReal (A * (2 * P.scale Q.1) ^ k)

/-- **Coefficient-to-annulus comparison**: for `Λ ≥ 1`, `ℓ > 0` and
`d_P(x, z) < 2ℓ`, ball inclusion before the infimum gives
`β_μ(z, Λℓ)² ≤ 2·6^{k+2} ∫_{(Λ+2)ℓ}^{2(Λ+2)ℓ} β_μ(x, r)² dr/r` (any source, any family). -/
def CoeffAnnulusStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (T : FamilyKind) (Λ ℓ : ℝ) (z x : Space n),
    1 ≤ Λ → 0 < ℓ → dist x z < 2 * ℓ →
      betaSq μ k T z (Λ * ℓ) ≤
        ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ r in Ioo ((Λ + 2) * ℓ) (2 * ((Λ + 2) * ℓ)), betaSq μ k T x r ∂scaleMeasure

/-- **Descendant sum versus integrated square energy** (first step of the forest energy estimate): for any
direct partition of any set, any source and `Λ ≥ 1`, every cell `T` has
`∑_{Q ⊂ T} a_Q μ(Q) ≤ 2·6^{k+2} ∫_T S^{2(Λ+2)ℓ_T}_{μ,𝒜_k}(x) dμ(x)`. The annuli of distinct
levels are disjoint (ratio `2 < 10`) and one cell per level contains a point. -/
def DescendantIntegralStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (E : Set (Space n)) (ℓ₀ Λ : ℝ)
    (P : DirectPartition E ℓ₀), 1 ≤ Λ → ∀ T : ℕ × Space n, P.IsCell T →
      P.descendantEnergy μ k Λ T ≤
        ENNReal.ofReal (2 * 6 ^ (k + 2)) *
          ∫⁻ x in P.cellOf T, squareEnergy μ k .mixed (2 * ((Λ + 2) * P.scale T.1)) x ∂μ

/-- **The forest energy**: for every direct partition of the support
from `ℓ₀ = R` (not only the one built by the construction), the local hypotheses in `P(a, B R)` give
`∑_{Q ⊂ T} a_Q μ(Q) ≤ C_E M μ(T)` on the root forest. `C_E, B` depend only on `n, k, A, Λ`. -/
def ForestEnergyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A → ∀ Λ : ℝ, 1 ≤ Λ →
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ B : ℝ, 1 ≤ B ∧
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
      LocalForwardHypotheses μ k A M a (B * R) →
      ∀ P : DirectPartition μ.support R, ∀ T : ℕ × Space n, P.InForest a R T →
        P.descendantEnergy μ k Λ T ≤ ENNReal.ofReal (CE * M) * μ (P.cellOf T)

/-! ## Shared named ADR/fit statements -/

/-- **Upper recentring** (`A_* = 2^k A`; shared): local ADR in `P(a, ρ)` bounds the mass of
every ball `P(y, s) ⊆ P(a, ρ)` with `2s ≤ ρ`, centred anywhere, by `2^k A s^k` (recentre at a
support point with twice the radius; a ball missing the support is null). -/
def UpperRecenteringStatement : Prop :=
  ∀ (n k : ℕ) (μ : Measure (Space n)) (A : ℝ) (a : Space n) (ρ : ℝ), LocalADR μ k A a ρ →
    ∀ (y : Space n) (s : ℝ), 0 < s → Metric.ball y s ⊆ Metric.ball a ρ → 2 * s ≤ ρ →
      μ (Metric.ball y s) ≤ ENNReal.ofReal (2 ^ k * A * s ^ k)

/-- **Point-to-fit:** if a model `L` (any family) has buffered fitting
integral `∫_{P(z,2r)} d_P(·, L)² dμ ≤ e r^{k+2}` with `A e ≤ 1`, then every support point
`y ∈ P(z, r)` has `d_P(y, L) ≤ 2 (A e)^{1/(k+2)} r`. (`A e ≤ 1` excludes distances beyond the
buffer; the weak power is never squared and summed.) -/
def PointToFitStatement : Prop :=
  ∀ (n k : ℕ) (T : FamilyKind) (μ : Measure (Space n)) (A : ℝ) (a : Space n) (ρ : ℝ),
    1 ≤ A → LocalADR μ k A a ρ →
    ∀ (z : Space n) (r : ℝ), 0 < r → Metric.ball z (4 * r) ⊆ Metric.ball a ρ → 4 * r ≤ ρ →
    ∀ (L : Models n k T) (e : ℝ), 0 ≤ e → A * e ≤ 1 →
      fit μ L z (2 * r) ≤ ENNReal.ofReal (e * r ^ (k + 2)) →
      ∀ y ∈ μ.support ∩ Metric.ball z r,
        Metric.infDist y (modelSet L) ≤ 2 * (A * e) ^ ((1 : ℝ) / (k + 2)) * r

/-- **Covariance lower bound**, with the horizontal small-error variant. For `1 ≤ k < n + 2` and `A ≥ 1` there are `a₀ > 0` and `e₀ > 0` such that for
every available type `T`, local ADR in `P(a, ρ)`, a support point `g`, `r > 0` with
`P(g, 4r) ⊆ P(a, ρ)`, `4r ≤ ρ`, and — for the horizontal type only — some horizontal model with
`∫_{P(g,2r)} d_P(·, M)² dμ ≤ e₀ r^{k+2}`: every finite `ν` agreeing with `μ` on `P(g, r)` passes
the continuation test of the base `ms3_core_comparison` at `(g, r)` with constant `a₀`
(positive rank: `λ_m(Q_{ν⌞P(g,r)}) ≥ a₀ r^{k+2}`, `m = T.rank k`; vertical rank zero:
`ν(P(g,r)) ≥ a₀ r²`). The disjunction is that test's hypothesis `hcont`. -/
def CovarianceLowerStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ e₀ : ℝ, 0 < e₀ ∧
    ∀ T : NeckType, T.Available n k →
    ∀ (μ : Measure (Space n)) (a : Space n) (ρ : ℝ), LocalADR μ k A a ρ →
    ∀ g ∈ μ.support, ∀ r : ℝ, 0 < r →
      Metric.ball g (4 * r) ⊆ Metric.ball a ρ → 4 * r ≤ ρ →
      (T = .horizontal → ∃ M : Models n k T.toFamilyKind,
        fit μ M g (2 * r) ≤ ENNReal.ofReal (e₀ * r ^ (k + 2))) →
      ∀ (ν : Measure (Space n)) [IsFiniteMeasure ν],
        ν.restrict (Metric.ball g r) = μ.restrict (Metric.ball g r) →
        (0 < T.rank k ∧ ∃ h : 0 < r,
            a₀ * r ^ (k + 2) ≤ (SpatialSource.ofBall ν g r h).rankEigenvalue (T.rank k)) ∨
          (T.rank k = 0 ∧ ENNReal.ofReal (a₀ * r ^ 2) ≤ ν (Metric.ball g r))

/-- **Same-source plane comparison,** all ranks including vertical
rank zero. Under the hypotheses of `CovarianceLowerStatement` (constant `e₀` for the horizontal
small-error test), any two spatial planes of rank `T.rank k` and any two measures dominating
`μ⌞P(g, r)` satisfy
`d_{x_g, r}(L₁, L₂)² ≤ C r^{-(k+2)} (∫ dist(x, L₁)² dμ₁ + ∫ dist(x, L₂)² dμ₂)`.
Neither plane need minimize on the comparison ball. -/
def PlaneComparisonStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ C : ℝ, 0 < C ∧ ∃ e₀ : ℝ, 0 < e₀ ∧
    ∀ T : NeckType, T.Available n k →
    ∀ (μ : Measure (Space n)) (a : Space n) (ρ : ℝ), LocalADR μ k A a ρ →
    ∀ g ∈ μ.support, ∀ r : ℝ, 0 < r →
      Metric.ball g (4 * r) ⊆ Metric.ball a ρ → 4 * r ≤ ρ →
      (T = .horizontal → ∃ M : Models n k T.toFamilyKind,
        fit μ M g (2 * r) ≤ ENNReal.ofReal (e₀ * r ^ (k + 2))) →
      ∀ (L₁ L₂ : AffineSpatialPlane n (T.rank k)) (μ₁ μ₂ : Measure (Space n)),
        μ.restrict (Metric.ball g r) ≤ μ₁ → μ.restrict (Metric.ball g r) ≤ μ₂ →
        ENNReal.ofReal (planeComparison g.1 r L₁ L₂ ^ 2) ≤
          ENNReal.ofReal (C / r ^ (k + 2)) *
            (spatialFittingIntegral μ₁ L₁ + spatialFittingIntegral μ₂ L₂)

/-- **Fitting gap:** for `1 ≤ k < n + 2`, `A ≥ 1` there is `c > 0`
such that under local ADR every support-centred ball `P(z, r)` with `P(z, 4r) ⊆ P(a, ρ)`,
`4r ≤ ρ` has `∫_{P(z,r)} [d_P(·,H)² + d_P(·,V)²] dμ ≥ c r^{k+2}` for every horizontal `H` and
vertical `V` (written as the sum of the two fits). Vacuous unless both families are available. -/
def FittingGapStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ c : ℝ, 0 < c ∧
    ∀ (μ : Measure (Space n)) (a : Space n) (ρ : ℝ), LocalADR μ k A a ρ →
    ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
      Metric.ball z (4 * r) ⊆ Metric.ball a ρ → 4 * r ≤ ρ →
      ∀ (H : Models n k .horizontal) (V : Models n k .vertical),
        ENNReal.ofReal (c * r ^ (k + 2)) ≤ fit μ H z r + fit μ V z r

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
