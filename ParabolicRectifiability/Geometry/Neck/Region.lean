import ParabolicRectifiability.Geometry.Neck.ComparisonEnergy
import ParabolicRectifiability.Geometry.AdmissibleModels

/-!
# Neck regions

Definitions only: the neck region and the punctured region set.

A neck region is data: the available type with its dimension guard, a compact
center set with radii, one infinite coherent family with its initial plane and
initial point, the stopping parents, and (horizontal case) the time
compatibility of all records. The family is part of the definition and is kept
when one restricts to finitely many scales. No parametrization, content,
packing, graphicality or source-mass statement occurs in the definition; those
are conclusions of the separate structure and measure theorems.

The center set is `centers`; the radius function `radius` is total, but only its
values on `centers` are constrained. The core is `{c ∈ centers | radius c = 0}`
and the stopping centers are `{c ∈ centers | 0 < radius c}`.
-/

noncomputable section

namespace ParabolicRectifiability

open scoped ENNReal

/-- The two neck types. A mixed testing family produces necks of both types, but
each neck itself is horizontal or vertical. -/
inductive NeckType where
  | horizontal
  | vertical
  deriving DecidableEq

namespace NeckType

/-- The spatial rank `m` of the planes: `m = k` (horizontal), `m = k - 2` (vertical).
The vertical value is used only under the guard `2 ≤ k` of `Available`. -/
def rank : NeckType → ℕ → ℕ
  | horizontal, k => k
  | vertical, k => k - 2

/-- Available types and their dimension guards: horizontal with `1 ≤ k ≤ n`,
vertical with `2 ≤ k ≤ n + 2`. In particular no vertical type exists at `k = 1`;
full horizontal rank `k = n`, vertical rank zero `k = 2` and the ambient vertical
dimension `k = n + 2` are retained. -/
def Available (n k : ℕ) : NeckType → Prop
  | horizontal => 1 ≤ k ∧ k ≤ n
  | vertical => 2 ≤ k ∧ k ≤ n + 2

/-- The corresponding admissible model family. -/
def toFamilyKind : NeckType → FamilyKind
  | horizontal => .horizontal
  | vertical => .vertical

/-- The comparison square bound of the neck's type: vertical
functions on `X` or horizontal functions on `ℝ^n`. -/
def SquareBound {n m : ℕ} {ι : Type*} : NeckType → CoherentFamily n m ι → ℝ → Prop
  | horizontal, F, E => F.HorizontalSquareBound E
  | vertical, F, E => F.VerticalSquareBound E

end NeckType

/-- Records for horizontal time compatibility: the disjoint union of the occurrences
`(j, a)` of the coherent family and the actual centers. Distinct records may have
the same physical center. -/
abbrev NeckRecord (n : ℕ) (ι : Type*) := (ℕ × ι) ⊕ Space n

namespace NeckRecord

variable {n m : ℕ} {ι : Type*}

/-- The physical point of a record. -/
def position (F : CoherentFamily n m ι) : NeckRecord n ι → Space n
  | .inl (j, a) => F.center j a
  | .inr c => c

/-- The recorded scale: `r_j` for an occurrence, `d_c` for an actual center
(hence zero for a core record, even if that point also occurs in the family). -/
def scale (F : CoherentFamily n m ι) (d : Space n → ℝ) : NeckRecord n ι → ℝ
  | .inl (j, _) => F.scale j
  | .inr c => d c

/-- Membership of a record: `a ∈ I_j` for an occurrence, `c ∈ 𝒞` for a center. -/
def IsRecord (F : CoherentFamily n m ι) (C : Set (Space n)) : NeckRecord n ι → Prop
  | .inl (j, a) => a ∈ F.index j
  | .inr c => c ∈ C

end NeckRecord

/-- Horizontal time compatibility over all records:
`|t_z - t_w| ≤ γ max{|x_z - x_w|², s_z², s_w²}`. -/
def RecordsTimeCompatible {n m : ℕ} {ι : Type*} (F : CoherentFamily n m ι)
    (C : Set (Space n)) (d : Space n → ℝ) (γ : ℝ) : Prop :=
  ∀ z w : NeckRecord n ι, NeckRecord.IsRecord F C z → NeckRecord.IsRecord F C w →
    |(NeckRecord.position F z).2.val - (NeckRecord.position F w).2.val| ≤
      γ * max (‖(NeckRecord.position F z).1 - (NeckRecord.position F w).1‖ ^ 2)
        (max (NeckRecord.scale F d z ^ 2) (NeckRecord.scale F d w ^ 2))

/-- The standing parameter conditions of a neck region:
`R, c₀, C_d, C_* > 0`, `σ ∈ (0,1]`, nonnegative `δ, E, κ, θ`, and `γ ≥ 0` in the
horizontal case (in the vertical case `γ` is unused). -/
structure NeckParameters (T : NeckType) (R c₀ Cd Cs σ δ E κ θ γ : ℝ) : Prop where
  R_pos : 0 < R
  c₀_pos : 0 < c₀
  Cd_pos : 0 < Cd
  Cs_pos : 0 < Cs
  σ_pos : 0 < σ
  σ_le_one : σ ≤ 1
  δ_nonneg : 0 ≤ δ
  E_nonneg : 0 ≤ E
  κ_nonneg : 0 ≤ κ
  θ_nonneg : 0 ≤ θ
  γ_nonneg : T = .horizontal → 0 ≤ γ

/-- A neck region of type `T` and dimension `k` in
`X = ℝ^n × ℝ`, with container `P(q, R)`, constants `c₀, C_d, C_*` (`Cd`, `Cs`),
separation `σ` and parameters `δ, E, κ, θ, γ`. The plane rank is `T.rank k`. -/
structure NeckRegion (n k : ℕ) (T : NeckType) (ι : Type*) (q : Space n)
    (R c₀ Cd Cs σ δ E κ θ γ : ℝ) where
  /-- The type is available, with its dimension guard. -/
  available : T.Available n k
  /-- The standing parameter conditions. -/
  parameters : NeckParameters T R c₀ Cd Cs σ δ E κ θ γ
  /-- Item 1: the compact center set `𝒞 ⊆ closure P(q,R)`. -/
  centers : Set (Space n)
  isCompact_centers : IsCompact centers
  centers_subset : centers ⊆ Metric.closedBall q R
  /-- Item 1: radii `d : 𝒞 → [0, C_d R]`. -/
  radius : Space n → ℝ
  radius_nonneg : ∀ c ∈ centers, 0 ≤ radius c
  radius_le : ∀ c ∈ centers, radius c ≤ Cd * R
  /-- Stopping separation: `d_P(c,c') ≥ c₀ max(d_c, d_{c'})` for distinct
  stopping centers. -/
  stop_separation : ∀ c ∈ centers, ∀ c' ∈ centers, 0 < radius c → 0 < radius c' →
    c ≠ c' → c₀ * max (radius c) (radius c') ≤ dist c c'
  /-- Core separation: `d_P(c,z) ≥ d_c` for a stopping center `c` and a core
  point `z`; vacuous when the core is empty. -/
  core_separation : ∀ c ∈ centers, 0 < radius c → ∀ z ∈ centers, radius z = 0 →
    radius c ≤ dist c z
  /-- Item 2: the one infinite coherent family, of rank `T.rank k`. Its
  `initialRadius` is `r₀`, its `initialPlane` is `L_*`. -/
  family : CoherentFamily n (T.rank k) ι
  initialRadius_le : family.initialRadius ≤ Cs * R
  /-- Item 2: a point `x_* ∈ L_*` with `|x_* - x_q| ≤ C_* R`. -/
  initialPoint : Spatial n
  initialPoint_mem : initialPoint ∈ family.initialPlane.toSet
  initialPoint_near : ‖initialPoint - q.1‖ ≤ Cs * R
  /-- Item 2: every center occurrence lies in `P(q, C_* R)`. -/
  center_mem : ∀ j, ∀ a ∈ family.index j, family.center j a ∈ Metric.ball q (Cs * R)
  /-- Item 2: every finite truncation satisfies the root, same-level and adjacent comparisons with the
  separation constant `σ` and `r_j = 10^{-j} r₀`. -/
  coherent : ∀ N : ℕ, family.IsCoherentUpTo σ δ N
  /-- Item 2: the center-height bound at every level. -/
  centerHeight : family.HasCenterHeight κ
  /-- Item 2: the comparison square bound for the neck's type. -/
  squareBound : T.SquareBound family E
  /-- Item 3: every core point is a limit of centers at levels tending to infinity. -/
  core_limit : ∀ z ∈ centers, radius z = 0 → family.IsLevelLimit z
  /-- Item 3: the specified stopping parent of each stopping center
  (`none` denotes the initial plane `L_*`). -/
  stoppingParent : Space n → Option (ℕ × ι)
  stoppingParent_spec : ∀ c ∈ centers, 0 < radius c →
    family.IsStoppingParent θ c (radius c) (stoppingParent c)
  /-- Item 4: horizontal time compatibility over all occurrence and center records. -/
  timeCompatible : T = .horizontal → RecordsTimeCompatible family centers radius γ

namespace NeckRegion

variable {n k : ℕ} {T : NeckType} {ι : Type*} {q : Space n}
  {R c₀ Cd Cs σ δ E κ θ γ : ℝ}

/-- The core `𝒞₀ = {c ∈ 𝒞 : d_c = 0}`. -/
def core (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) : Set (Space n) :=
  {c | c ∈ N.centers ∧ N.radius c = 0}

/-- The stopping centers `𝒞₊ = {c ∈ 𝒞 : d_c > 0}`. -/
def stopping (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) : Set (Space n) :=
  {c | c ∈ N.centers ∧ 0 < N.radius c}

/-- The punctured region `𝒩 = P(q,R) \ (𝒞₀ ∪ ⋃_{c ∈ 𝒞₊} closure P(c, d_c))`
A reference to a neck region means the whole structure, not
only this set. -/
def regionSet (N : NeckRegion n k T ι q R c₀ Cd Cs σ δ E κ θ γ) : Set (Space n) :=
  Metric.ball q R \ (N.core ∪ ⋃ c ∈ N.stopping, Metric.closedBall c (N.radius c))

end NeckRegion

end ParabolicRectifiability
