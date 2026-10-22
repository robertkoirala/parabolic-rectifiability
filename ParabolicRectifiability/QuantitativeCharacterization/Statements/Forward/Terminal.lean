import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.ForwardCovering

/-! # Terminal construction for the forward covering: data and named statements

Definitions, proposition definitions and one positivity lemma. This module fixes the statements
below `TerminalConstructionStatement`: the internal record of the terminal construction from one
good region and the named statements of its component estimates.

Fixed constants (with the partition constant `C_d = 2`):
`D = 16 (C_d + 1) = 48`, `R_𝒩 = 6 ℓ_*`, `r₀ = 48 ℓ_*`, `r_j = 10^{-j} r₀` (`stageScale`),
`υ = 1/100`, `κ_net = 1/4` (horizontal) and `1` (vertical) (base `NeckType.sourceSeparation`),
`J_lag = 8 = 2 + ⌈log₁₀(40 D/υ)⌉`.

The internal record, at one good region `𝒢` with root cell `S = Q_*`:
* the stopping scale `ρ = 𝒢.stopScale` (first level) and the cutoff `f = stageCutoff 𝒢`, defined, not chosen;
* `LocalFits 𝒢`: for every level `j` and point `g` a full `T`-model minimizing the
  **original-source** fit `∫_{P(g, 40 r_j)} d_P(·, M)² dμ` (for the horizontal type the plane and
  the time jointly); the planes of the genuine occurrences, their fitted times, and the full
  parabolic tube tests (`ThinnessStatement`) are read from these models;
* `Choice`: the raw choices of the terminal selection (terminal centres in decreasing cutoff, the
  continuing nets); everything else is defined from them: the surviving sets `S_j` (`kept`), the
  Borel terminal assignments, the centre set `𝒞 = 𝒞₀ ∪ 𝒞₊`, the radii, the stored parents, the
  artificial root, the coherent family indexed by physical points, the stop parents;
* `Choice.IsSelection`: the selection rules (no covariance or tube test: every candidate continues
  and every point passes its tube, which `ThinnessStatement` and the plane comparison
  of the partition-energy step prove).

Two named statements are consumed by other steps: `OwnerStatement` (used by the last-witness
square estimate) and `StopScaleLipschitzStatement` (used by the coverage assembly). They are written with the plain expressions
`coherentScale (48 * 𝒢.rootScale) j` and `P.scale Q.1`, so that later statements need no definition of
this module beyond the statement constant.

Conventions: every fit, beta and plane comparison uses the original `μ` on its stated ball; the
assigned measure `μ⌞S` never enters a fit. Tolerances are uniform: each estimate statement has the
shape `∃ Λ₀, ∀ Λ ≥ Λ₀, ∃ B, ∀ η > 0, ∃ b₀ > 0, ∀ b ∈ (0, b₀]` of `TerminalConstructionStatement`, with local ADR in
`P(a, B R)` at a support-centred root and a good region of the root forest.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section Data

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The root side `ℓ_*` of a good region is positive. -/
theorem d1c_rootScale_pos (𝒢 : GoodRegion P μ k Λ b) : 0 < 𝒢.rootScale := by
  unfold GoodRegion.rootScale DirectPartition.scale coherentScale
  exact div_pos P.scale_pos (pow_pos (by norm_num) _)

/-- The construction scales `r_j = 10^{-j} r₀`, `r₀ = D ℓ_* = 48 ℓ_*`. -/
def stageScale (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : ℝ :=
  coherentScale (48 * 𝒢.rootScale) j

/-- **Admissible pairs** `(j, g)`: `g ∈ S` and `ρ(g) < 10 r_j/υ = 1000 r_j`. Every
genuine occurrence of level `j` and every comparison point of the last witness is admissible. -/
def Admissible (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) (g : Space n) : Prop :=
  g ∈ 𝒢.rootCell ∧ 𝒢.stopScale g < 1000 * stageScale 𝒢 j

/-- **The cutoff**: `f = 0` on `{ρ = 0}`; otherwise `f(z) = r_j` for the
least `j ≥ 1` with `r_j ≤ υ ρ(z)` (rounding down on the ten-adic grid, `υ = 1/100`). On `closure S`
(where `ρ ≤ ℓ_*`) this is the unique `j ≥ 1` with `r_j ≤ υ ρ(z) < 10 r_j` (`CutoffStatement`). -/
def stageCutoff (𝒢 : GoodRegion P μ k Λ b) (z : Space n) : ℝ :=
  if 𝒢.stopScale z = 0 then 0
  else stageScale 𝒢 (sInf {j : ℕ | 1 ≤ j ∧ stageScale 𝒢 j ≤ 𝒢.stopScale z / 100})

/-- The initial plane `L_*`: the spatial plane of the prescribed root optimizer `Π_{Q_*}`. -/
def rootPlane (𝒢 : GoodRegion P μ k Λ b) : AffineSpatialPlane n (𝒢.type.rank k) :=
  NeckSelection.modelPlane 𝒢.type (𝒢.model 𝒢.root)

/-- **The artificial root**: `(π_{L_*} x_q, τ_*)` with the fitted time `τ_*` of
`Π_{Q_*}` (horizontal), `(π_{L_*} x_q, t_q)` (vertical). -/
def rootCenter (𝒢 : GoodRegion P μ k Λ b) : Space n :=
  if 𝒢.type = .horizontal then
    point ((rootPlane 𝒢).projection 𝒢.root.2.1)
      (NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root))
  else ((rootPlane 𝒢).projection 𝒢.root.2.1, 𝒢.root.2.2)

/-- **Local original-source fits**: for every level `j` and point `g` a full model of
the region's type minimizing `∫_{P(g, 40 r_j)} d_P(·, M)² dμ` over all such models, with the
original `μ` (horizontal: plane and time jointly, not a covariance fit plus a median). The planes
and fitted times of the genuine occurrences are those of these models. -/
structure LocalFits (𝒢 : GoodRegion P μ k Λ b) where
  model : ℕ → Space n → Models n k 𝒢.type.toFamilyKind
  minimal : ∀ (j : ℕ) (g : Space n) (M : Models n k 𝒢.type.toFamilyKind),
    fit μ (model j g) g (40 * stageScale 𝒢 j) ≤ fit μ M g (40 * stageScale 𝒢 j)

/-- **The raw choices of the terminal selection**: at each stage `j ≥ 1`, the
terminal centres `term j 0, …, term j (termCount j - 1)` in selection order and the continuing net
`cand j 0, …, cand j (candCount j - 1)` in processing order. Values at stage `0` and beyond the
counts are never used. Everything else is defined below. -/
structure Choice (n : ℕ) where
  termCount : ℕ → ℕ
  term : ℕ → ℕ → Space n
  candCount : ℕ → ℕ
  cand : ℕ → ℕ → Space n

namespace Choice

variable (C : Choice n) (𝒢 : GoodRegion P μ k Λ b)

/-- The part of `E'` outside the terminal holes `P(c, f(c))` of stage `j`. -/
def afterTerm (j : ℕ) (E' : Set (Space n)) : Set (Space n) :=
  E' \ ⋃ (i : ℕ) (_ : i < C.termCount j), Metric.ball (C.term j i) (stageCutoff 𝒢 (C.term j i))

/-- The surviving sets `S_0 = S`, `S_j = S_{j-1} \ (terminal holes of stage j)`. -/
def kept (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) : ℕ → Set (Space n)
  | 0 => 𝒢.rootCell
  | j + 1 => C.afterTerm 𝒢 (j + 1) (kept C 𝒢 j)

/-- The Borel terminal assignment of the `i`-th terminal centre of stage `j`: its first-ball piece
`S_{j-1} ∩ P(c, f(c)) \ ⋃_{l < i} P(c_l, f(c_l))`. -/
def termPiece (j i : ℕ) : Set (Space n) :=
  C.kept 𝒢 (j - 1) ∩
    (Metric.ball (C.term j i) (stageCutoff 𝒢 (C.term j i)) \
      ⋃ (l : ℕ) (_ : l < i), Metric.ball (C.term j l) (stageCutoff 𝒢 (C.term j l)))

/-- `c` is a terminal centre of some stage `j ≥ 1`. -/
def IsTermCenter (c : Space n) : Prop :=
  ∃ j, 1 ≤ j ∧ ∃ i, i < C.termCount j ∧ C.term j i = c

/-- The (first) stage of a terminal centre. -/
def termStage (c : Space n) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ ∃ i, i < C.termCount j ∧ C.term j i = c}

/-- The centre set `𝒞 = 𝒞₀ ∪ 𝒞₊`, with `𝒞₀` the limiting core of the region. -/
def centers : Set (Space n) :=
  𝒢.limitCore ∪ {c | C.IsTermCenter c}

open Classical in
/-- The radii: `d_c = f(c)` at a terminal centre, `0` elsewhere (in particular on `𝒞₀`). -/
def radius (c : Space n) : ℝ :=
  if C.IsTermCenter c then stageCutoff 𝒢 c else 0

/-- The assignment `A_c`: the union of the terminal pieces of `c`. -/
def assignment (c : Space n) : Set (Space n) :=
  ⋃ (j : ℕ) (_ : 1 ≤ j) (i : ℕ) (_ : i < C.termCount j ∧ C.term j i = c), C.termPiece 𝒢 j i

open Classical in
/-- The candidates of stage `j` as a finite set of physical points. -/
def candSet (j : ℕ) : Finset (Space n) :=
  (Finset.range (C.candCount j)).image (C.cand j)

open Classical in
/-- **The stored parent** at level `j`: the first candidate of stage `j` whose open
net ball `P(g, κ_net r_j)` contains `z` (meaningful for `z ∈ S_j`). -/
def parentOf (j : ℕ) (z : Space n) : Space n :=
  if h : ∃ i, i < C.candCount j ∧
      z ∈ Metric.ball (C.cand j i) (𝒢.type.sourceSeparation * stageScale 𝒢 j) then
    C.cand j (Nat.find h)
  else z

/-- **The coherent family**, indexed by physical points: level `0` is the
artificial root with plane `L_*`; level `j ≥ 1` is the continuing net of stage `j`, each occurrence
with the spatial plane of its local fit; parents are the stored parents (the root at level `1`). -/
def family (fits : LocalFits 𝒢) : CoherentFamily n (𝒢.type.rank k) (Space n) where
  initialRadius := 48 * 𝒢.rootScale
  initialRadius_pos := by
    have h := d1c_rootScale_pos 𝒢
    linarith
  index := fun j => if j = 0 then {rootCenter 𝒢} else C.candSet j
  center := fun _ a => a
  plane := fun j a =>
    if j = 0 then rootPlane 𝒢 else NeckSelection.modelPlane 𝒢.type (fits.model j a)
  parent := fun j a => if j ≤ 1 then rootCenter 𝒢 else C.parentOf 𝒢 (j - 1) a
  initialPlane := rootPlane 𝒢

/-- **The stop parent**: for a terminal centre of stage `j ≥ 2`, its stored level-`(j-1)`
parent; at stage `1`, the initial plane (`none`). -/
def stoppingParent (c : Space n) : Option (ℕ × Space n) :=
  if 2 ≤ C.termStage c then some (C.termStage c - 1, C.parentOf 𝒢 (C.termStage c - 1) c)
  else none

/-- **Survival history** of a genuine record `z` with recorded scale `s`: `s > 0`,
`z ∈ S`, and `z ∈ S_l` for every positive level `l` with `s ≤ r_{l+1}`. -/
def HasHistory (z : Space n) (s : ℝ) : Prop :=
  0 < s ∧ z ∈ 𝒢.rootCell ∧ ∀ l : ℕ, 1 ≤ l → s ≤ stageScale 𝒢 (l + 1) → z ∈ C.kept 𝒢 l

/-- **The selection rules**: at each stage `j ≥ 1`, terminal centres are
chosen from `S_{j-1}` in decreasing cutoff, each outside the earlier holes of the stage, with
`f ≥ r_j`, after which `f < r_j` on `S_j`; the continuing net is a maximal `κ_net r_j`-separated
subset of `S_j` whose open balls cover `S_j`. -/
structure IsSelection : Prop where
  term_mem : ∀ j, 1 ≤ j → ∀ i, i < C.termCount j →
    C.term j i ∈ C.kept 𝒢 (j - 1) \
      ⋃ (l : ℕ) (_ : l < i), Metric.ball (C.term j l) (stageCutoff 𝒢 (C.term j l))
  term_large : ∀ j, 1 ≤ j → ∀ i, i < C.termCount j →
    stageScale 𝒢 j ≤ stageCutoff 𝒢 (C.term j i)
  term_max : ∀ j, 1 ≤ j → ∀ i, i < C.termCount j →
    ∀ z ∈ C.kept 𝒢 (j - 1) \
        ⋃ (l : ℕ) (_ : l < i), Metric.ball (C.term j l) (stageCutoff 𝒢 (C.term j l)),
      stageCutoff 𝒢 z ≤ stageCutoff 𝒢 (C.term j i)
  term_done : ∀ j, 1 ≤ j → ∀ z ∈ C.kept 𝒢 j, stageCutoff 𝒢 z < stageScale 𝒢 j
  cand_mem : ∀ j, 1 ≤ j → ∀ i, i < C.candCount j → C.cand j i ∈ C.kept 𝒢 j
  cand_separated : ∀ j, 1 ≤ j → ∀ i, i < C.candCount j → ∀ l, l < C.candCount j → i ≠ l →
    𝒢.type.sourceSeparation * stageScale 𝒢 j ≤ dist (C.cand j i) (C.cand j l)
  cand_cover : ∀ j, 1 ≤ j → C.kept 𝒢 j ⊆
    ⋃ (i : ℕ) (_ : i < C.candCount j),
      Metric.ball (C.cand j i) (𝒢.type.sourceSeparation * stageScale 𝒢 j)

/-- **Stage facts**: the elementary consequences of the selection
rules used by every later statement. -/
structure StageFacts : Prop where
  kept_succ_subset : ∀ j, C.kept 𝒢 (j + 1) ⊆ C.kept 𝒢 j
  kept_subset : ∀ j, C.kept 𝒢 j ⊆ 𝒢.rootCell
  kept_measurable : ∀ j, MeasurableSet (C.kept 𝒢 j)
  term_radius : ∀ j, 1 ≤ j → ∀ i, i < C.termCount j →
    stageCutoff 𝒢 (C.term j i) = stageScale 𝒢 j
  termStage_spec : ∀ c, C.IsTermCenter c →
    1 ≤ C.termStage c ∧ (∃ i, i < C.termCount (C.termStage c) ∧ C.term (C.termStage c) i = c) ∧
      c ∈ C.kept 𝒢 (C.termStage c - 1) ∧ C.radius 𝒢 c = stageScale 𝒢 (C.termStage c)
  term_center : ∀ c, C.IsTermCenter c →
    0 < C.radius 𝒢 c ∧ 100 * C.radius 𝒢 c ≤ 𝒢.stopScale c ∧
      𝒢.stopScale c < 1000 * C.radius 𝒢 c
  cand_admissible : ∀ j, 1 ≤ j → ∀ i, i < C.candCount j → Admissible 𝒢 j (C.cand j i)
  parentOf_spec : ∀ j, 1 ≤ j → ∀ z ∈ C.kept 𝒢 j,
    ∃ i, i < C.candCount j ∧ C.parentOf 𝒢 j z = C.cand j i ∧
      dist z (C.parentOf 𝒢 j z) < 𝒢.type.sourceSeparation * stageScale 𝒢 j
  cand_history : ∀ j, 1 ≤ j → ∀ i, i < C.candCount j →
    C.HasHistory 𝒢 (C.cand j i) (stageScale 𝒢 j)
  term_history : ∀ c, C.IsTermCenter c → C.HasHistory 𝒢 c (C.radius 𝒢 c)

/-- **Centre-set fields** of `TerminalNeck` for the defined centre set. -/
structure CenterSetFields : Prop where
  isCompact_centers : IsCompact (C.centers 𝒢)
  centers_nonempty : (C.centers 𝒢).Nonempty
  centers_subset_closure : C.centers 𝒢 ⊆ closure 𝒢.rootCell
  centers_subset : C.centers 𝒢 ⊆ Metric.closedBall 𝒢.root.2 (6 * 𝒢.rootScale)

/-- **Radius, separation and cutoff fields** of `TerminalNeck`. -/
structure RadiusFields : Prop where
  radius_nonneg : ∀ c ∈ C.centers 𝒢, 0 ≤ C.radius 𝒢 c
  radius_le : ∀ c ∈ C.centers 𝒢, C.radius 𝒢 c ≤ 6 * 𝒢.rootScale
  core_eq : {c | c ∈ C.centers 𝒢 ∧ C.radius 𝒢 c = 0} = 𝒢.limitCore
  stop_separation : ∀ c ∈ C.centers 𝒢, ∀ c' ∈ C.centers 𝒢, 0 < C.radius 𝒢 c →
    0 < C.radius 𝒢 c' → c ≠ c' → max (C.radius 𝒢 c) (C.radius 𝒢 c') ≤ dist c c'
  core_separation : ∀ c ∈ C.centers 𝒢, 0 < C.radius 𝒢 c → ∀ z ∈ C.centers 𝒢,
    C.radius 𝒢 z = 0 → 100 * C.radius 𝒢 c ≤ dist c z
  cutoff : ∀ c ∈ C.centers 𝒢, 0 < C.radius 𝒢 c → 100 * C.radius 𝒢 c ≤ 𝒢.stopScale c

/-- **Assignment fields** of `TerminalNeck`. -/
structure AssignmentFields : Prop where
  measurable_assignment : ∀ c, MeasurableSet (C.assignment 𝒢 c)
  assignment_subset : ∀ c ∈ C.centers 𝒢, 0 < C.radius 𝒢 c →
    C.assignment 𝒢 c ⊆ 𝒢.rootCell ∩ Metric.ball c (C.radius 𝒢 c)
  assignment_disjoint : ∀ c ∈ C.centers 𝒢, ∀ c' ∈ C.centers 𝒢, 0 < C.radius 𝒢 c →
    0 < C.radius 𝒢 c' → c ≠ c' → Disjoint (C.assignment 𝒢 c) (C.assignment 𝒢 c')
  source_eq : 𝒢.rootCell =
    (𝒢.rootCell ∩ 𝒢.limitCore) ∪
      ⋃ c ∈ {c | c ∈ C.centers 𝒢 ∧ 0 < C.radius 𝒢 c}, C.assignment 𝒢 c

/-- **Family fields** of `TerminalNeck` that need no ADR (fit anchoring). -/
structure FamilyFields (fits : LocalFits 𝒢) : Prop where
  initialRadius_eq : (C.family 𝒢 fits).initialRadius = 48 * 𝒢.rootScale
  initialPoint_mem : (rootCenter 𝒢).1 ∈ (C.family 𝒢 fits).initialPlane.toSet
  core_limit : ∀ z ∈ C.centers 𝒢, C.radius 𝒢 z = 0 → (C.family 𝒢 fits).IsLevelLimit z
  level_zero_plane : ∀ a ∈ (C.family 𝒢 fits).index 0,
    (C.family 𝒢 fits).plane 0 a = (C.family 𝒢 fits).initialPlane
  initialPlane_fit :
    (C.family 𝒢 fits).initialPlane = NeckSelection.modelPlane 𝒢.type (𝒢.model 𝒢.root)
  genuine_mem : ∀ j, ∀ a ∈ (C.family 𝒢 fits).index (j + 1),
    (C.family 𝒢 fits).center (j + 1) a ∈ 𝒢.rootCell
  genuine_scale : ∀ j, ∀ a ∈ (C.family 𝒢 fits).index (j + 1),
    𝒢.stopScale ((C.family 𝒢 fits).center (j + 1) a) < 1000 * (C.family 𝒢 fits).scale (j + 1)
  genuine_fit : ∀ j, ∀ a ∈ (C.family 𝒢 fits).index (j + 1),
    ∃ M : Models n k 𝒢.type.toFamilyKind,
      (C.family 𝒢 fits).plane (j + 1) a = NeckSelection.modelPlane 𝒢.type M ∧
      ∀ M' : Models n k 𝒢.type.toFamilyKind,
        fit μ M ((C.family 𝒢 fits).center (j + 1) a) (40 * (C.family 𝒢 fits).scale (j + 1)) ≤
          fit μ M' ((C.family 𝒢 fits).center (j + 1) a) (40 * (C.family 𝒢 fits).scale (j + 1))

/-- **Height, stop-parent and container fields** of `TerminalNeck` at tolerance `η` (centre
heights; stop parents; the artificial root). -/
structure HeightParentFields (fits : LocalFits 𝒢) (η : ℝ) : Prop where
  initialPoint_near : ‖(rootCenter 𝒢).1 - 𝒢.root.2.1‖ ≤ 48 * 𝒢.rootScale
  center_mem : ∀ j, ∀ a ∈ (C.family 𝒢 fits).index j,
    (C.family 𝒢 fits).center j a ∈ Metric.ball 𝒢.root.2 (48 * 𝒢.rootScale)
  centerHeight : (C.family 𝒢 fits).HasCenterHeight η
  stoppingParent_spec : ∀ c ∈ C.centers 𝒢, 0 < C.radius 𝒢 c →
    (C.family 𝒢 fits).IsStoppingParent η c (C.radius 𝒢 c) (C.stoppingParent 𝒢 c)

end Choice

end Data

/-! ## Stopping scale, owners and local fits -/

/-- **Member ancestors**: the only member at the root level is the root, and
every member `Q` has, at each level between the root's and its own, a member ancestor containing
it. (Hereditary members, parent steps of the direct partition, disjointness at the root level.) -/
def AncestorStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b),
    (∀ Q ∈ 𝒢.members, Q.1 = 𝒢.root.1 → Q = 𝒢.root) ∧
    ∀ Q ∈ 𝒢.members, ∀ i : ℕ, 𝒢.root.1 ≤ i → i ≤ Q.1 →
      ∃ Q' ∈ 𝒢.members, Q'.1 = i ∧ P.cellOf Q ⊆ P.cellOf Q'

/-- **The stopping-scale Lipschitz lemma**: the
stopping scale `ρ(z) = inf_{Q ∈ 𝒯} (ℓ_Q + dist_P(z, Q))` of any good region is nonnegative and
`1`-Lipschitz, `ρ(z) ≤ ℓ_Q + dist_P(z, Q)` for every member `Q`, and `ρ ≤ ℓ_Q` on the cell `Q`. -/
def StopScaleLipschitzStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b),
    (∀ z, 0 ≤ 𝒢.stopScale z) ∧
    (∀ z w, 𝒢.stopScale z ≤ 𝒢.stopScale w + dist z w) ∧
    (∀ Q ∈ 𝒢.members, ∀ z, 𝒢.stopScale z ≤ P.scale Q.1 + Metric.infDist z (P.cellOf Q)) ∧
    ∀ Q ∈ 𝒢.members, ∀ z ∈ P.cellOf Q, 𝒢.stopScale z ≤ P.scale Q.1

/-- **The zero set of the stopping scale**: `{ρ = 0} = 𝒞₀ = ⋂_j closure G_j`. -/
def StopScaleZeroStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (z : Space n),
    𝒢.stopScale z = 0 ↔ z ∈ 𝒢.limitCore

/-- **The cutoff**: `0 ≤ f ≤ υ ρ`; `f = 0` on `{ρ = 0}`; every value is `0`
or a scale `r_j`; and for `0 < ρ(z) ≤ ℓ_*` (in particular on `closure S`), `f(z) = r_j` for some
`j ≥ 1` with `r_j ≤ υ ρ(z) < 10 r_j`. -/
def CutoffStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b),
    (∀ z, 0 ≤ stageCutoff 𝒢 z ∧ 100 * stageCutoff 𝒢 z ≤ 𝒢.stopScale z) ∧
    (∀ z, 𝒢.stopScale z = 0 → stageCutoff 𝒢 z = 0) ∧
    (∀ z, stageCutoff 𝒢 z = 0 ∨ ∃ j : ℕ, stageCutoff 𝒢 z = stageScale 𝒢 j) ∧
    ∀ z, 0 < 𝒢.stopScale z → 𝒢.stopScale z ≤ 𝒢.rootScale →
      ∃ j : ℕ, 1 ≤ j ∧ stageCutoff 𝒢 z = stageScale 𝒢 j ∧
        stageScale 𝒢 j ≤ 𝒢.stopScale z / 100 ∧ 𝒢.stopScale z / 100 < 10 * stageScale 𝒢 j

/-- **The owner cell** (used by the last-witness estimate). For any good region, any level `j` and any `g ∈ S` with `ρ(g) < 1000 r_j`
(`r_j = coherentScale (48 ℓ_*) j`) there is a member `O` with
`min(r_j, ℓ_*) ≤ ℓ_O ≤ 2000 r_j`, `dist_P(g, O) ≤ 2000 r_j`, `d_P(g, z_O) ≤ 2000 r_j + 2 ℓ_O`,
depth `depth(O) ≥ j - J_lag` with `J_lag = 8`, and, once `Λ ≥ 4000`, the fitting ball
`P(g, 40 r_j)` inside the coefficient ball `P(z_O, Λ ℓ_O)`. No terminal construction is assumed. -/
def OwnerStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) (g : Space n),
    g ∈ 𝒢.rootCell → 𝒢.stopScale g < 1000 * coherentScale (48 * 𝒢.rootScale) j →
      ∃ O ∈ 𝒢.members,
        min (coherentScale (48 * 𝒢.rootScale) j) 𝒢.rootScale ≤ P.scale O.1 ∧
        P.scale O.1 ≤ 2000 * coherentScale (48 * 𝒢.rootScale) j ∧
        Metric.infDist g (P.cellOf O) ≤ 2000 * coherentScale (48 * 𝒢.rootScale) j ∧
        dist g O.2 ≤ 2000 * coherentScale (48 * 𝒢.rootScale) j + 2 * P.scale O.1 ∧
        j + 𝒢.root.1 ≤ O.1 + 8 ∧
        (4000 ≤ Λ → Metric.ball g (40 * coherentScale (48 * 𝒢.rootScale) j) ⊆
          Metric.ball O.2 (Λ * P.scale O.1))

/-- **Local fits exist**: the original-source fitting infimum on every ball
`P(g, 40 r_j)` is attained, for a measure finite on compacts. -/
def LocalFitsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b),
    IsFiniteMeasureOnCompacts μ → Nonempty (LocalFits 𝒢)

/-- **The local error**: for `Λ ≥ 4000` and every admissible `(j, g)`,
`I(g, j) = ∫_{P(g, 40 r_j)} d_P(·, Π_g)² dμ ≤ I_O ≤ (2000 Λ)^{k+2} b r_j^{k+2}` (test the minimizer
against the owner's model `Π_O`; `I_O ≤ (Λ ℓ_O)^{k+2} b` by the chain budget). -/
def LocalErrorStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢), 4000 ≤ Λ →
    ∀ (j : ℕ) (g : Space n), Admissible 𝒢 j g →
      fit μ (fits.model j g) g (40 * stageScale 𝒢 j) ≤
        ENNReal.ofReal ((2000 * Λ) ^ (k + 2) * b * stageScale 𝒢 j ^ (k + 2))

/-- **Thinness: the full parabolic tube tests**. For
small `b`, every support point `z ∈ P(g, 2 r_j)` of an admissible `(j, g)`, `j ≥ 1`, is within
`η r_j` of the full fitted model `Π_g` in `d_P`; hence within `η r_j` of its spatial plane, and
(horizontal) its time is within `(η r_j)²` of the fitted time. -/
def ThinnessStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (j : ℕ) (g : Space n), 1 ≤ j → Admissible 𝒢 j g →
    ∀ z ∈ μ.support ∩ Metric.ball g (2 * stageScale 𝒢 j),
      Metric.infDist z (modelSet (fits.model j g)) ≤ η * stageScale 𝒢 j ∧
      Metric.infDist z.1 (NeckSelection.modelPlane 𝒢.type (fits.model j g)).toSet ≤
        η * stageScale 𝒢 j ∧
      (𝒢.type = .horizontal →
        |z.2.val - NeckSelection.modelTime 𝒢.type (fits.model j g)| ≤ (η * stageScale 𝒢 j) ^ 2)

/-- **The initial tube and the artificial root**. For small `b`,
every point of `closure S` is within `η ℓ_*` of the root model `Π_{Q_*}` in `d_P` (hence of `L_*`,
and horizontally within `(η ℓ_*)²` of `τ_*` in time), and the artificial root is within `η ℓ_*` of
`q = z_{Q_*}`. -/
def RootThinnessStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
      (∀ z ∈ closure 𝒢.rootCell,
        Metric.infDist z (modelSet (𝒢.model 𝒢.root)) ≤ η * 𝒢.rootScale ∧
        Metric.infDist z.1 (rootPlane 𝒢).toSet ≤ η * 𝒢.rootScale ∧
        (𝒢.type = .horizontal →
          |z.2.val - NeckSelection.modelTime 𝒢.type (𝒢.model 𝒢.root)| ≤
            (η * 𝒢.rootScale) ^ 2)) ∧
      dist (rootCenter 𝒢) 𝒢.root.2 ≤ η * 𝒢.rootScale ∧
      ‖(rootCenter 𝒢).1 - 𝒢.root.2.1‖ ≤ η * 𝒢.rootScale

/-! ## Terminal selection and exact core with parent history -/

/-- **The terminal selection exists**: stage by stage, the greedy terminal selection
in decreasing cutoff inside the compact container `closure S`, then a maximal `κ_net r_j`-separated
net of the remainder. Purely geometric. -/
def SelectionExistsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b), ∃ C : Choice n, C.IsSelection 𝒢

/-- **Stage facts** of every selection. -/
def StageFactsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (C : Choice n),
    C.IsSelection 𝒢 → C.StageFacts 𝒢

/-- **The exact source identity**: Borel disjoint assignments
`A_c ⊆ S ∩ P(c, d_c)` with `S = (S ∩ 𝒞₀) ∪ ⋃_{c ∈ 𝒞₊} A_c`. -/
def AssignmentFieldsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (C : Choice n),
    C.IsSelection 𝒢 → C.AssignmentFields 𝒢

/-- **Core equality and core limits**:
`⋂_j closure S_j = 𝒞₀`, and every point of `𝒞₀` is a limit of continuing candidates at levels
tending to infinity. -/
def CoreEqualityStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (C : Choice n),
    C.IsSelection 𝒢 →
      (⋂ j, closure (C.kept 𝒢 j)) = 𝒢.limitCore ∧
      ∀ z ∈ 𝒢.limitCore, ∃ (level : ℕ → ℕ) (idx : ℕ → ℕ),
        (∀ m, 1 ≤ level m ∧ idx m < C.candCount (level m)) ∧
        Tendsto level atTop atTop ∧ Tendsto (fun m => C.cand (level m) (idx m)) atTop (𝓝 z)

/-- **The centre set is compact, nonempty and in `closure S`**. -/
def CenterSetFieldsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (C : Choice n),
    C.IsSelection 𝒢 → C.CenterSetFields 𝒢

/-- **Radii, separations and the cutoff field**. -/
def RadiusFieldsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (C : Choice n),
    C.IsSelection 𝒢 → C.RadiusFields 𝒢

/-- **The family fields needing no ADR** (fit anchoring, genuine scale, core limits). -/
def FamilyFieldsStatement : Prop :=
  ∀ (n : ℕ) (E : Set (Space n)) (ℓ₀ : ℝ) (P : DirectPartition E ℓ₀) (μ : Measure (Space n))
    (k : ℕ) (Λ b : ℝ) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢) (C : Choice n),
    C.IsSelection 𝒢 → C.FamilyFields 𝒢 fits

/-- **Centre heights, stop parents and the container**, at every
tolerance `η` for small `b`. -/
def HeightParentStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (C : Choice n), C.IsSelection 𝒢 → C.HeightParentFields 𝒢 fits η

/-! ## Coherence and horizontal recorded-time compatibility -/

/-- **Same-level comparison**: two admissible occurrences of one level
`j ≥ 1` within `20 r_j` have `d_{x_g, r_j}(L_g, L_{g'}) ≤ η` for small `b` (common source
`μ⌞P(g, 5 r_j)` inside both radius-`40 r_j` fitting balls). -/
def SameLevelStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (j : ℕ) (g g' : Space n), 1 ≤ j → Admissible 𝒢 j g →
      Admissible 𝒢 j g' → dist g g' ≤ 20 * stageScale 𝒢 j →
      planeComparison g.1 (stageScale 𝒢 j) (NeckSelection.modelPlane 𝒢.type (fits.model j g))
        (NeckSelection.modelPlane 𝒢.type (fits.model j g')) ≤ η

/-- **Adjacent comparison**: an admissible occurrence `g` of level
`j + 1` and an admissible `g'` of level `j ≥ 1` within `20 r_j` have
`d_{x_{g'}, r_j}(L_g, L_{g'}) ≤ η` for small `b` (common source `μ⌞P(g, 5 r_{j+1})`, centred at the
child). -/
def AdjacentLevelStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (j : ℕ) (g g' : Space n), 1 ≤ j → Admissible 𝒢 (j + 1) g →
      Admissible 𝒢 j g' → dist g g' ≤ 20 * stageScale 𝒢 j →
      planeComparison g'.1 (stageScale 𝒢 j)
        (NeckSelection.modelPlane 𝒢.type (fits.model (j + 1) g))
        (NeckSelection.modelPlane 𝒢.type (fits.model j g')) ≤ η

/-- **Root comparison**: an admissible level-`1` occurrence
`g` has `d_{x, r₀}(L_g, L_*) ≤ η` for every anchor `x` with `|x - x_q| ≤ r₀`, for small `b`
(test the local fit against `Π_*` and use the root coefficient on the child-centred source). -/
def RootAdjacentStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (g : Space n), Admissible 𝒢 1 g →
    ∀ x : Spatial n, ‖x - 𝒢.root.2.1‖ ≤ 48 * 𝒢.rootScale →
      planeComparison x (stageScale 𝒢 0) (NeckSelection.modelPlane 𝒢.type (fits.model 1 g))
        (rootPlane 𝒢) ≤ η

/-- **Coherence of the family**: every finite truncation of the family is
coherent with separation `σ = 1/4` and comparison tolerance `η`, for small `b`. -/
def CoherenceStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (C : Choice n), C.IsSelection 𝒢 →
      ∀ N : ℕ, (C.family 𝒢 fits).IsCoherentUpTo (1 / 4) η N

/-- **Fitted-time comparison**: horizontally, two admissible occurrences of one
level `l ≥ 1` within `20 r_l` have fitted times within `η r_l²` for small `b`
(`μ(B) |τ - τ'| ≤ I + I'` on `B = P(g, 5 r_l)`, lower ADR). -/
def FittedTimeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (l : ℕ) (g g' : Space n), 1 ≤ l → Admissible 𝒢 l g →
      Admissible 𝒢 l g' → dist g g' ≤ 20 * stageScale 𝒢 l → 𝒢.type = .horizontal →
      |NeckSelection.modelTime 𝒢.type (fits.model l g) -
          NeckSelection.modelTime 𝒢.type (fits.model l g')| ≤ η * stageScale 𝒢 l ^ 2

/-- **Recorded-time compatibility of genuine records**: horizontally,
for small `b`, any two points with survival histories `(z, s)`, `(w, s')` satisfy
`|t_z - t_w| ≤ η max(|x_z - x_w|², s², s'²)` (deepest positive level `l` with `r_l ≥ 10β`,
`β = max(d_P(z,w), s, s')`; stored parents at level `l`; their fitted times; the two full tube
tests; otherwise the initial tube; absorption of the time term). The conclusion concerns physical
points only; the fitted models enter the proof through `LocalFitsStatement`. -/
def GenuineTimeStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ C : Choice n, C.IsSelection 𝒢 → 𝒢.type = .horizontal →
    ∀ (z w : Space n) (s s' : ℝ), C.HasHistory 𝒢 z s → C.HasHistory 𝒢 w s' →
      |z.2.val - w.2.val| ≤ η * max (‖z.1 - w.1‖ ^ 2) (max (s ^ 2) (s' ^ 2))

/-- **Horizontal recorded-time compatibility of all records**: genuine records, the artificial root (initial tube) and core records (limits of
genuine occurrences with scales tending to zero), for small `b`. -/
def TimeCompatibleStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 → ∀ A : ℝ, 1 ≤ A →
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ η : ℝ, 0 < η → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
    ∀ a ∈ μ.support, ∀ R : ℝ, 0 < R → LocalADR μ k A a (B * R) →
    ∀ (P : DirectPartition μ.support R) (𝒢 : GoodRegion P μ k Λ b), P.InForest a R 𝒢.root →
    ∀ (fits : LocalFits 𝒢) (C : Choice n), C.IsSelection 𝒢 → 𝒢.type = .horizontal →
      RecordsTimeCompatible (C.family 𝒢 fits) (C.centers 𝒢) (C.radius 𝒢) η

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
