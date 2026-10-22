import ParabolicRectifiability.QuantitativeCharacterization.Coverings
import ParabolicRectifiability.Geometry.Neck.Region
import ParabolicRectifiability.Measure.Neck.Selection.ModelFit

/-! # The forward covering: data, interfaces and named statements

Definitions and proposition definitions only. This module fixes the first level of the proof
tree of the forward covering `exists_local_forward_covering`: the data passed between its six
steps (partition energy, stopping and packing, terminal construction, last-witness square
estimate, completion, coverage assembly) and their named statements. The component proofs are
in the `Forward` proof modules, and `d1comp_exists_local_forward_covering` assembles the
forward covering theorem.

The data, in the order of the construction at one support-centred root `P₀ = P(a,R)`:
* `DirectPartition E ℓ₀`: the direct nested Borel partitions of the closed support with ratio
  `h = 1/10` from `ℓ₀ = R`.
  A cell is addressed by `(j, z)` with `z ∈ 𝒵_j`; its side is `ℓ_j = 10^{-j} ℓ₀`
  (`coherentScale`). Tree order is inclusion at deeper levels (`IsBelow`).
* `GoodRegion`: a hereditary good region of the energy stopping, with its single type, its models `Π_Q` (the mixed-coefficient optimizers)
  and the finite-chain budget.
* `StoppingDecomposition`: bad blocks and good regions of the root forest, with root packing,
  same-family local packing of the model balls `P(z_S, 4 ℓ_S)` (`D₁ = 2 C_d = 4`) and the bad
  mass.
* `TerminalNeck`: the terminal construction from one good region, **without** the comparison square sum. Its
  neck fields are those of the base `NeckRegion` except
  `squareBound`, with container `P(q, R_𝒩)`, `q = z_{Q_*}`, `R_𝒩 = 6 ℓ_*`, `r₀ = 48 ℓ_* = 8 R_𝒩`
  (`D = 16 (C_d + 1) = 48`), `c₀ = 1`, `C_d = 1`, `C_* = 8`, `σ = 1/4`, `υ = 1/100`; it adds the
  exact core, the terminal assignment and cutoff, and the fit anchoring of the occurrences used
  by the last witness.

Conventions: every beta, fit and covariance source is the whole original `μ`; energies and
masses are `ℝ≥0∞`; real constants are compared through `ENNReal.ofReal`. Families of cells are
indexed by subsets of `ℕ × Space n`; sums are `tsum` in `ℝ≥0∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

open ParabolicRectifiability.Foundations

section Data

variable {n : ℕ}

/-! ## The local hypotheses -/

/-- Local ADR at a support-centred root: for every
`b ∈ supp μ ∩ P(a, ρ)` and `0 < s ≤ ρ`, `A⁻¹ s^k ≤ μ(P(b,s)) ≤ A s^k`. Used with `ρ = B R`. -/
def LocalADR (μ : Measure (Space n)) (k : ℕ) (A : ℝ) (a : Space n) (ρ : ℝ) : Prop :=
  ∀ b ∈ μ.support ∩ Metric.ball a ρ, ∀ s : ℝ, 0 < s → s ≤ ρ →
    ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k)

/-- The local hypotheses of the forward covering in the buffer `P(a, ρ)`: local
ADR and the local Carleson bound `∫_{P(b,s)} ∫_0^s β_μ² dr/r dμ ≤ M s^k` with the whole
original `μ` and the mixed family. With `ρ = B_loc R` this is the hypothesis of
`exists_local_forward_covering`. -/
def LocalForwardHypotheses (μ : Measure (Space n)) (k : ℕ) (A M : ℝ) (a : Space n)
    (ρ : ℝ) : Prop :=
  ∀ b ∈ μ.support ∩ Metric.ball a ρ, ∀ s : ℝ, 0 < s → s ≤ ρ →
    ENNReal.ofReal (A⁻¹ * s ^ k) ≤ μ (Metric.ball b s) ∧
      μ (Metric.ball b s) ≤ ENNReal.ofReal (A * s ^ k) ∧
      (∫⁻ z in Metric.ball b s, squareEnergy μ k .mixed s z ∂μ) ≤ ENNReal.ofReal (M * s ^ k)

/-! ## Direct partitions -/

/-- **Direct nested Borel partitions** of a closed set `E` with ratio `h = 1/10`, from the top
scale `ℓ₀` (with
`c_d = 1/4`, `C_d = 2`). Level `j` has the countable `ℓ_j`-separated centre set
`𝒵_j ⊆ E` (nested in `j`), `ℓ_j = 10^{-j} ℓ₀`; its cells `cell j z`, `z ∈ 𝒵_j`, are Borel,
pairwise disjoint and cover `E` exactly (boundaries included);
`E ∩ P(z, ℓ_j/4) ⊆ cell j z ⊆ P(z, 2 ℓ_j)`; each level-`(j+1)` cell lies in the cell of its
parent `parent j w ∈ 𝒵_j`, with at most `(1 + 3/h)^{n+2} = 31^{n+2}` children; and the open
inner ball of a cell is disjoint from the closure of every incomparable cell. Only the
generations `j ≥ 0` are used; no measure enters. -/
structure DirectPartition (E : Set (Space n)) (ℓ₀ : ℝ) where
  scale_pos : 0 < ℓ₀
  /-- The centre set `𝒵_j`. -/
  center : ℕ → Set (Space n)
  /-- The cell `Q_{j,z}` (meaningful for `z ∈ 𝒵_j`). -/
  cell : ℕ → Space n → Set (Space n)
  /-- The parent `parent j w ∈ 𝒵_j` of a level-`(j+1)` centre `w`. -/
  parent : ℕ → Space n → Space n
  center_subset : ∀ j, center j ⊆ E
  center_countable : ∀ j, (center j).Countable
  center_mono : ∀ j, center j ⊆ center (j + 1)
  center_separated : ∀ j, ∀ z ∈ center j, ∀ z' ∈ center j, z ≠ z' →
    coherentScale ℓ₀ j ≤ dist z z'
  measurable_cell : ∀ j z, MeasurableSet (cell j z)
  cell_disjoint : ∀ j, ∀ z ∈ center j, ∀ z' ∈ center j, z ≠ z' →
    Disjoint (cell j z) (cell j z')
  cell_cover : ∀ j, (⋃ z ∈ center j, cell j z) = E
  inner_subset : ∀ j, ∀ z ∈ center j, E ∩ Metric.ball z (coherentScale ℓ₀ j / 4) ⊆ cell j z
  cell_subset_ball : ∀ j, ∀ z ∈ center j, cell j z ⊆ Metric.ball z (2 * coherentScale ℓ₀ j)
  parent_mem : ∀ j, ∀ w ∈ center (j + 1), parent j w ∈ center j
  cell_subset_parent : ∀ j, ∀ w ∈ center (j + 1), cell (j + 1) w ⊆ cell j (parent j w)
  children_encard : ∀ j, ∀ z ∈ center j,
    {w | w ∈ center (j + 1) ∧ parent j w = z}.encard ≤ (31 : ℕ∞) ^ (n + 2)
  /-- Protected balls: for `j ≤ l` and incomparable cells (`cell l w ⊄ cell j z`), each open inner
  ball misses the closure of the other cell. -/
  protected_ball : ∀ j l, j ≤ l → ∀ z ∈ center j, ∀ w ∈ center l, ¬ cell l w ⊆ cell j z →
    E ∩ Metric.ball z (coherentScale ℓ₀ j / 4) ∩ closure (cell l w) = ∅ ∧
      E ∩ Metric.ball w (coherentScale ℓ₀ l / 4) ∩ closure (cell j z) = ∅

namespace DirectPartition

variable {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)

/-- The side `ℓ_j = 10^{-j} ℓ₀` of the level-`j` cells. -/
def scale (_ : DirectPartition E ℓ₀) (j : ℕ) : ℝ := coherentScale ℓ₀ j

/-- `(j, z)` addresses a cell: `z ∈ 𝒵_j`. -/
def IsCell (Q : ℕ × Space n) : Prop := Q.2 ∈ P.center Q.1

/-- The cell of an address. -/
def cellOf (Q : ℕ × Space n) : Set (Space n) := P.cell Q.1 Q.2

/-- Tree order (`Q ⊂ T`): `Q` is a cell at a level at least that of `T`, contained in
the cell of `T`. For cells this is exactly descent in the parent tree. -/
def IsBelow (Q T : ℕ × Space n) : Prop :=
  P.IsCell Q ∧ T.1 ≤ Q.1 ∧ P.cellOf Q ⊆ P.cellOf T

/-- The root forest of `P₀ = P(a,R)`: cells below a top cell
(level `0`, side `ℓ₀`) that meets `P₀`. -/
def InForest (a : Space n) (R : ℝ) (Q : ℕ × Space n) : Prop :=
  ∃ z₀ ∈ P.center 0, (P.cell 0 z₀ ∩ Metric.ball a R).Nonempty ∧ P.IsBelow Q (0, z₀)

/-- The energy coefficient `a_Q = β_μ(z_Q, Λ ℓ_Q)²`: natural mixed beta of
the whole original `μ`. -/
def coeff (μ : Measure (Space n)) (k : ℕ) (Λ : ℝ) (Q : ℕ × Space n) : ℝ≥0∞ :=
  betaSq μ k .mixed Q.2 (Λ * P.scale Q.1)

/-- The normalized error `(Λ ℓ_Q)^{-k-2} ∫_{P(z_Q, Λ ℓ_Q)} d_P(y, L)² dμ(y)` of one model `L`
on the coefficient ball of `Q`. For an optimal model it equals `coeff`. -/
def modelCoeff (μ : Measure (Space n)) {k : ℕ} {T : FamilyKind} (Λ : ℝ) (L : Models n k T)
    (Q : ℕ × Space n) : ℝ≥0∞ :=
  (ENNReal.ofReal (Λ * P.scale Q.1))⁻¹ ^ (k + 2) * fit μ L Q.2 (Λ * P.scale Q.1)

/-- The discrete energy below `T`, `∑_{Q ⊂ T} a_Q μ(Q)`. -/
def descendantEnergy (μ : Measure (Space n)) (k : ℕ) (Λ : ℝ) (T : ℕ × Space n) : ℝ≥0∞ :=
  ∑' Q : {Q : ℕ × Space n // P.IsBelow Q T}, P.coeff μ k Λ Q.1 * μ (P.cellOf Q.1)

end DirectPartition

/-! ## Good regions -/

/-- **A good region** of the energy stopping: a root cell `Q_*`, a hereditary set of cells below
it (every cell between a member and the root is a member; siblings need not be retained), one
available type `T` for the whole region, the models `Π_Q` of type `T` attaining the mixed
coefficient (`a_Q = (Λ ℓ_Q)^{-k-2} ∫_{P(z_Q,Λℓ_Q)} d_P(y,Π_Q)² dμ`), and the
finite-chain budget `∑_{Q_* ⊇ Q' ⊇ Q} a_{Q'} ≤ b` (up to the fixed
factor `(Λ/D)^{k+2}`). -/
structure GoodRegion {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (μ : Measure (Space n)) (k : ℕ) (Λ b : ℝ) where
  root : ℕ × Space n
  root_isCell : P.IsCell root
  members : Set (ℕ × Space n)
  root_mem : root ∈ members
  below_root : ∀ Q ∈ members, P.IsBelow Q root
  hereditary : ∀ Q ∈ members, ∀ Q' : ℕ × Space n, P.IsBelow Q Q' → P.IsBelow Q' root →
    Q' ∈ members
  type : NeckType
  type_available : NeckType.Available n k type
  model : ℕ × Space n → Models n k type.toFamilyKind
  model_optimal : ∀ Q ∈ members, P.modelCoeff μ Λ (model Q) Q = P.coeff μ k Λ Q
  budget : ∀ Q ∈ members,
    (∑' Q' : {Q' : ℕ × Space n // Q' ∈ members ∧ P.IsBelow Q Q'},
      P.modelCoeff μ Λ (model Q'.1) Q'.1) ≤ ENNReal.ofReal b

namespace GoodRegion

variable {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b)

/-- The root cell `S = Q_*`. -/
def rootCell : Set (Space n) := P.cellOf 𝒢.root

/-- The root side `ℓ_*`. -/
def rootScale : ℝ := P.scale 𝒢.root.1

/-- `G_j`: the union of the region's cells of depth `j`. -/
def levelSet (j : ℕ) : Set (Space n) :=
  ⋃ (Q : ℕ × Space n) (_ : Q ∈ 𝒢.members ∧ Q.1 = 𝒢.root.1 + j), P.cellOf Q

/-- The limiting core `𝒞₀ = ⋂_j closure G_j`. -/
def limitCore : Set (Space n) := ⋂ j, closure (𝒢.levelSet j)

/-- The stopping scale `ρ(z) = inf_{Q ∈ 𝒯} (ℓ_Q + dist_P(z, Q))`. -/
def stopScale (z : Space n) : ℝ :=
  ⨅ Q : 𝒢.members, (P.scale Q.1.1 + Metric.infDist z (P.cellOf Q.1))

end GoodRegion

/-! ## The stopping decomposition -/

open scoped Classical in
/-- **The stopping decomposition of the root forest** with packing constant `K`: bad blocks (`a_Q > b/2`) and good regions indexed by their
roots, every forest cell bad or in exactly one region; model balls `P(z_S, 4 ℓ_S)` of the good
roots (`D₁ = 2 C_d = 4`) with root packing `∑_S (4 ℓ_S)^k ≤ K R^k` and same-family local
packing `∑_{z_S ∈ P(w,s), 4 ℓ_S ≤ s} (4 ℓ_S)^k ≤ K s^k` for every `w ∈ X`, `s > 0` (one family,
no reselection per test); and bad mass `∑_{Q bad} μ(Q) ≤ K R^k`. -/
structure StoppingDecomposition {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (μ : Measure (Space n)) (k : ℕ) (Λ b : ℝ) (a : Space n) (R K : ℝ) where
  bad : Set (ℕ × Space n)
  roots : Set (ℕ × Space n)
  region : roots → GoodRegion P μ k Λ b
  region_root : ∀ S, (region S).root = S.1
  bad_forest : ∀ Q ∈ bad, P.InForest a R Q
  roots_forest : ∀ S ∈ roots, P.InForest a R S
  bad_coeff : ∀ Q ∈ bad, ENNReal.ofReal (b / 2) < P.coeff μ k Λ Q
  classify : ∀ Q, P.InForest a R Q →
    (Q ∈ bad ∧ ∀ S, Q ∉ (region S).members) ∨ (Q ∉ bad ∧ ∃! S, Q ∈ (region S).members)
  root_packing : (∑' S : roots, ENNReal.ofReal (4 * P.scale S.1.1) ^ k) ≤
    ENNReal.ofReal (K * R ^ k)
  local_packing : ∀ (w : Space n) (s : ℝ), 0 < s →
    (∑' S : roots, if S.1.2 ∈ Metric.ball w s ∧ 4 * P.scale S.1.1 ≤ s then
        ENNReal.ofReal (4 * P.scale S.1.1) ^ k else 0) ≤ ENNReal.ofReal (K * s ^ k)
  bad_mass : (∑' Q : bad, μ (P.cellOf Q.1)) ≤ ENNReal.ofReal (K * R ^ k)

/-! ## The terminal construction (without the square sum) -/

/-- **The terminal construction from a good region** (without the comparison square sum), with
tolerances `δ` (coherence), `κ` (centre heights), `θ` (stop tubes), `γ` (horizontal time).

Neck fields (those of the base `NeckRegion` except `squareBound`; container `P(q, R_𝒩)` with
`q = z_{Q_*}`, `R_𝒩 = 6 ℓ_*`, `C_d = 1`, `C_* = 8`, `c₀ = 1`, `σ = 1/4`, `r₀ = 48 ℓ_*`): the
nonempty compact centre set `𝒞 ⊆ closure S` with radii, core `𝒞₀ = {d = 0}` equal to the
limiting core `⋂_j closure G_j`, separations `d_P(c,c') ≥ max(d_c,d_{c'})`
and `d_P(c,𝒞₀) ≥ d_c/υ`, one infinite coherent family with initial plane and point, centre
heights, core limits, stop parents, horizontal record time compatibility.

Assignment fields: Borel disjoint `A_c ⊆ S ∩ P(c,d_c)` with
`S = (S ∩ 𝒞₀) ∪ ⋃_{c ∈ 𝒞₊} A_c`, and `d_c ≤ υ ρ(c)`, `υ = 1/100`.

Fit anchoring, used by the last witness: level zero is the artificial
root with the root model's plane `L_*`; every occurrence of level `j ≥ 1` is a genuine
candidate `g ∈ S` with `ρ(g) < 10 r_j/υ` whose plane is the spatial plane of a `T`-model
minimizing `∫_{P(g, 40 r_j)} d_P(y,·)² dμ` over the whole original `μ`. Planes of models are the
base `NeckSelection.modelPlane`. -/
structure TerminalNeck {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀}
    {μ : Measure (Space n)} {k : ℕ} {Λ b : ℝ} (𝒢 : GoodRegion P μ k Λ b)
    (δ κ θ γ : ℝ) where
  tolerance_nonneg : 0 ≤ δ ∧ 0 ≤ κ ∧ 0 ≤ θ ∧ 0 ≤ γ
  centers : Set (Space n)
  isCompact_centers : IsCompact centers
  centers_nonempty : centers.Nonempty
  centers_subset_closure : centers ⊆ closure 𝒢.rootCell
  centers_subset : centers ⊆ Metric.closedBall 𝒢.root.2 (6 * 𝒢.rootScale)
  radius : Space n → ℝ
  radius_nonneg : ∀ c ∈ centers, 0 ≤ radius c
  radius_le : ∀ c ∈ centers, radius c ≤ 6 * 𝒢.rootScale
  core_eq : {c | c ∈ centers ∧ radius c = 0} = 𝒢.limitCore
  stop_separation : ∀ c ∈ centers, ∀ c' ∈ centers, 0 < radius c → 0 < radius c' → c ≠ c' →
    max (radius c) (radius c') ≤ dist c c'
  core_separation : ∀ c ∈ centers, 0 < radius c → ∀ z ∈ centers, radius z = 0 →
    100 * radius c ≤ dist c z
  cutoff : ∀ c ∈ centers, 0 < radius c → 100 * radius c ≤ 𝒢.stopScale c
  assignment : Space n → Set (Space n)
  measurable_assignment : ∀ c, MeasurableSet (assignment c)
  assignment_subset : ∀ c ∈ centers, 0 < radius c →
    assignment c ⊆ 𝒢.rootCell ∩ Metric.ball c (radius c)
  assignment_disjoint : ∀ c ∈ centers, ∀ c' ∈ centers, 0 < radius c → 0 < radius c' →
    c ≠ c' → Disjoint (assignment c) (assignment c')
  source_eq : 𝒢.rootCell =
    (𝒢.rootCell ∩ 𝒢.limitCore) ∪ ⋃ c ∈ {c | c ∈ centers ∧ 0 < radius c}, assignment c
  family : CoherentFamily n (𝒢.type.rank k) (Space n)
  initialRadius_eq : family.initialRadius = 48 * 𝒢.rootScale
  initialPoint : Spatial n
  initialPoint_mem : initialPoint ∈ family.initialPlane.toSet
  initialPoint_near : ‖initialPoint - 𝒢.root.2.1‖ ≤ 48 * 𝒢.rootScale
  center_mem : ∀ j, ∀ a ∈ family.index j,
    family.center j a ∈ Metric.ball 𝒢.root.2 (48 * 𝒢.rootScale)
  coherent : ∀ N : ℕ, family.IsCoherentUpTo (1 / 4) δ N
  centerHeight : family.HasCenterHeight κ
  core_limit : ∀ z ∈ centers, radius z = 0 → family.IsLevelLimit z
  stoppingParent : Space n → Option (ℕ × Space n)
  stoppingParent_spec : ∀ c ∈ centers, 0 < radius c →
    family.IsStoppingParent θ c (radius c) (stoppingParent c)
  timeCompatible : 𝒢.type = .horizontal → RecordsTimeCompatible family centers radius γ
  level_zero_plane : ∀ a ∈ family.index 0, family.plane 0 a = family.initialPlane
  initialPlane_fit : family.initialPlane = NeckSelection.modelPlane 𝒢.type (𝒢.model 𝒢.root)
  genuine_mem : ∀ j, ∀ a ∈ family.index (j + 1), family.center (j + 1) a ∈ 𝒢.rootCell
  genuine_scale : ∀ j, ∀ a ∈ family.index (j + 1),
    𝒢.stopScale (family.center (j + 1) a) < 1000 * family.scale (j + 1)
  genuine_fit : ∀ j, ∀ a ∈ family.index (j + 1),
    ∃ M : Models n k 𝒢.type.toFamilyKind,
      family.plane (j + 1) a = NeckSelection.modelPlane 𝒢.type M ∧
      ∀ M' : Models n k 𝒢.type.toFamilyKind,
        fit μ M (family.center (j + 1) a) (40 * family.scale (j + 1)) ≤
          fit μ M' (family.center (j + 1) a) (40 * family.scale (j + 1))

end Data

/-! ## The six named statements -/

/-- **Direct partitions and the original-source discrete energy**. For `1 ≤ k < n + 2`, `A ≥ 1` and every coefficient dilation `Λ ≥ 1` there
are `C_E ≥ 0` and a buffer `B ≥ 1` such that, at every support-centred root `P(a,R)` of a
locally Radon `μ` satisfying the local hypotheses in `P(a, B R)`, the direct partitions of
`supp μ` from `ℓ₀ = R` exist and every cell `T` of the root forest has
`∑_{Q ⊂ T} a_Q μ(Q) ≤ C_E M μ(T)`, `a_Q = β_μ(z_Q, Λ ℓ_Q)²`. -/
def PartitionEnergyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A → ∀ Λ : ℝ, 1 ≤ Λ →
    ∃ CE : ℝ, 0 ≤ CE ∧ ∃ B : ℝ, 1 ≤ B ∧
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
      LocalForwardHypotheses μ k A M a (B * R) →
      ∃ P : DirectPartition μ.support R, ∀ T : ℕ × Space n, P.InForest a R T →
        P.descendantEnergy μ k Λ T ≤ ENNReal.ofReal (CE * M) * μ (P.cellOf T)

/-- **Stopping, the first-entrance inequality, root and same-family local packing**. For `1 ≤ k < n + 2`, `A ≥ 1` there is `Λ₀` such
that for every `Λ ≥ Λ₀` there are `C ≥ 1`, a buffer `B ≥ 1` and `b₀ > 0` with: for every
`0 < b ≤ b₀`, at a support-centred root with local ADR in `P(a, B R)`, every direct partition
from `ℓ₀ = R` whose forest cells satisfy `∑_{Q ⊂ T} a_Q μ(Q) ≤ M μ(T)` has a stopping
decomposition at threshold `b` with packing constant `C (1 + M/b)`.
Root packing, same-family local packing and bad mass are outputs. -/
def StoppingPackingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ B : ℝ, 1 ≤ B ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
    ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ M : ℝ, 0 ≤ M →
      LocalADR μ k A a (B * R) →
      ∀ P : DirectPartition μ.support R,
        (∀ T : ℕ × Space n, P.InForest a R T →
          P.descendantEnergy μ k Λ T ≤ ENNReal.ofReal M * μ (P.cellOf T)) →
        Nonempty (StoppingDecomposition P μ k Λ b a R (C * (1 + M / b)))

/-- **The terminal construction.** For `1 ≤ k < n + 2`, `A ≥ 1` there is `Λ₀` (after the
fixed lag `J_lag`) such that for every `Λ ≥ Λ₀` there is a buffer `B ≥ 1` with: for every
tolerance `ε > 0` there is `b₀ > 0` such that for `0 < b ≤ b₀`, local ADR in `P(a, B R)` at a
support-centred root, every good region (budget `b`) of a direct partition from `ℓ₀ = R` whose
root is in the root forest has a terminal construction with all four tolerances `ε`. The square
sum is **not** part of this interface. -/
def TerminalConstructionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b),
      P.InForest a R 𝒢.root → Nonempty (TerminalNeck 𝒢 ε ε ε ε)

/-- **The last-witness square estimate**. For `1 ≤ k < n + 2`, `A ≥ 1` there is `Λ₀` such that for every
`Λ ≥ Λ₀` there are a buffer `B ≥ 1`, `C ≥ 0`, a tolerance threshold `ε₀ > 0` and `b₀ > 0` with:
for `0 < b ≤ b₀`, local ADR in `P(a, B R)`, every good region (budget `b`) in the root forest
and every terminal construction from it with tolerances at most `ε₀`, the comparison square
bound of the region's type holds for its coherent family with `E_neck = C b`. The bound is
uniform in the truncation and the witness; no square bound is assumed. -/
def LastWitnessStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
    ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b),
      P.InForest a R 𝒢.root →
    ∀ δ κ θ γ : ℝ, δ ≤ ε₀ → κ ≤ ε₀ → θ ≤ ε₀ → γ ≤ ε₀ →
    ∀ TN : TerminalNeck 𝒢 δ κ θ γ, 𝒢.type.SquareBound TN.family (C * b)

/-- **Generic charts and smooth attachments; the whole completed reference**, applied to the
constructed neck. For `1 ≤ k < n + 2`,
`c₀ > 0` and `σ ∈ (0,1]` there are `L ≥ 1` and `ε₀ > 0` such that every neck region (base
`NeckRegion`) with separation constants `c₀, σ` and tolerances `δ, E, κ, θ, γ ≤ ε₀` has an
`L`-reference of its own type whose carrier contains every core and stopping centre:
vertically the smooth-attachment completion `Φ = (F, t)` (2-bi-Lipschitz, whole-map
half-time BMO by the direct affine-to-BMO route), horizontally the Whitney plateau completion
of the compact trace. -/
def ForwardCompletionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ c₀ σ : ℝ, 0 < c₀ → 0 < σ → σ ≤ 1 →
    ∃ L : ℝ, 1 ≤ L ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (T : NeckType) (ι : Type) (q : Space n) (R Cd Cs δ E κ θ γ : ℝ),
      δ ≤ ε₀ → E ≤ ε₀ → κ ≤ ε₀ → θ ≤ ε₀ → γ ≤ ε₀ →
      ∀ N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ,
        ∃ ρ : Reference n k L, ρ.kind = T.toFamilyKind ∧ N.centers ⊆ ρ.carrier

/-- **Good-slab coverage and the final covering assembly.** For `1 ≤ k < n + 2` there are `C ≥ 1` and
`L₀ ≥ 1` such that for every `L ≥ L₀`: at a support-centred root `P(a,R)`, a direct partition
from `ℓ₀ = R`, a stopping decomposition with packing constant `K ≥ 0`, a terminal construction
for every good region and an `L`-reference for every good region whose carrier contains that
region's centres give a `(C K, L)`-regular mixed covering of `P(a,R)`: bad slabs form `𝓑`,
good slabs `(Q ∩ P₀) × [ℓ_Q/10, ℓ_Q)` go to their region's reference with ball
`P(z_S, 4 ℓ_S)`. -/
def CoverageAssemblyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → ∀ Λ b K : ℝ, 0 ≤ K →
    ∀ (P : DirectPartition μ.support R) (SD : StoppingDecomposition P μ k Λ b a R K)
      (δ κ θ γ : ℝ) (tn : ∀ S : SD.roots, TerminalNeck (SD.region S) δ κ θ γ)
      (ref : SD.roots → Reference n k L),
      (∀ S, (tn S).centers ⊆ (ref S).carrier) →
      Nonempty (RegularMixedCovering k (C * K) L μ a R)

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
