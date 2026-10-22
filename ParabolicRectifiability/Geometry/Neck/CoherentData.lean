import ParabolicRectifiability.Geometry.AffinePlane

/-!
# Coherent centers and planes

This file contains definitions only: the plane comparison `d_{x,r}(L,L')` and
the coherent data.

One structure `CoherentFamily` carries centers, spatial planes and parent maps
at *every* level `j ≥ 0`. Finite coherent data through level `N` are the
predicate `CoherentFamily.IsCoherentUpTo σ δ N`, which constrains only levels
`0, …, N`; the data at later levels are ignored. Infinite coherent data are
`CoherentFamily.IsCoherent σ δ`, the statement that *every* finite truncation of
the *same* family is coherent. There is therefore no separate existence
assertion for each truncation.

Indices form a fixed type `ι`; level `j` uses the finite set `index j : Finset ι`.
The level-`j` planes are `plane j : ι → AffineSpatialPlane n m`, which is the
representation consumed by the finite weighted projection maps
(`CoherentProjection.sigma (index j) (plane j) θ`). Values of `center`, `plane`
and `parent` at indices outside `index j` are irrelevant: every predicate below
quantifies over `index j` only. Different occurrences, at different levels or
with different indices, may have the same physical center.

The center-height bound is a separate predicate with its own parameter `κ`;
it is not part of coherence. Horizontal time compatibility of the occurrences
is also a separate predicate, with recorded scales `r_j`. No chart, packing or
graph conclusion appears in these definitions.
-/

noncomputable section

namespace ParabolicRectifiability

open Filter Topology

variable {n m : ℕ} {ι : Type*}

/-- The plane comparison `d_{x,r}(L,L') = ‖P_L - P_{L'}‖ + r⁻¹ |π_L x - π_{L'} x|`
`P_L` is the linear orthogonal projection onto the
direction and `π_L` the affine nearest-point projection; the norm of the
difference of projections is the operator norm. Both planes have rank `m`. -/
def planeComparison (x : Spatial n) (r : ℝ) (L L' : AffineSpatialPlane n m) : ℝ :=
  ‖L.linearProjection - L'.linearProjection‖ + r⁻¹ * ‖L.projection x - L'.projection x‖

/-- The scales `r_j = 10^{-j} r₀` (`h = 1/10`). -/
def coherentScale (r₀ : ℝ) (j : ℕ) : ℝ := r₀ / 10 ^ j

/-- Centers, spatial planes and parent maps at every level.

* `initialRadius` is `r₀ > 0`;
* `index j` is the finite index set `I_j`;
* `center j a = z_{j,a} = (x_{j,a}, t_{j,a})` is the center of occurrence `(j,a)`;
* `plane j a = L_{j,a}` is an affine spatial plane of rank `m`;
* `parent (j+1) a = p_{j+1}(a)` is the chosen parent of `a ∈ I_{j+1}`
  (the value `parent 0` is never used);
* `initialPlane = L_*` is the initial affine spatial plane of rank `m`. -/
structure CoherentFamily (n m : ℕ) (ι : Type*) where
  initialRadius : ℝ
  initialRadius_pos : 0 < initialRadius
  index : ℕ → Finset ι
  center : ℕ → ι → Space n
  plane : ℕ → ι → AffineSpatialPlane n m
  parent : ℕ → ι → ι
  initialPlane : AffineSpatialPlane n m

namespace CoherentFamily

variable (F : CoherentFamily n m ι)

/-- The level-`j` scale `r_j = 10^{-j} r₀`. -/
def scale (j : ℕ) : ℝ := coherentScale F.initialRadius j

/-- Finite coherent data through level `N`:
`σ r_j`-separated centers at each level `j ≤ N`, parents within `r_{j-1}`, and the
root, same-level and adjacent comparisons bounded by `δ`. All distances between
centers are parabolic. The adjacent comparison is required for *every* preceding
center within `20 r_{j-1}`, not only for the chosen parent. -/
structure IsCoherentUpTo (F : CoherentFamily n m ι) (σ δ : ℝ) (N : ℕ) : Prop where
  /-- Distinct indices at one level have `σ r_j`-separated centers. -/
  separated : ∀ j ≤ N, ∀ a ∈ F.index j, ∀ b ∈ F.index j, a ≠ b →
    σ * F.scale j ≤ dist (F.center j a) (F.center j b)
  /-- The parent of a level-`(j+1)` index is a level-`j` index. -/
  parent_mem : ∀ j, j + 1 ≤ N → ∀ a ∈ F.index (j + 1), F.parent (j + 1) a ∈ F.index j
  /-- `d_P(z_{j+1,a}, z_{j,p_{j+1}(a)}) ≤ r_j`. -/
  parent_dist : ∀ j, j + 1 ≤ N → ∀ a ∈ F.index (j + 1),
    dist (F.center (j + 1) a) (F.center j (F.parent (j + 1) a)) ≤ F.scale j
  /-- Root comparison: `d_{x_{0,a},r_0}(L_{0,a}, L_*) ≤ δ`. -/
  root : ∀ a ∈ F.index 0,
    planeComparison (F.center 0 a).1 (F.scale 0) (F.plane 0 a) F.initialPlane ≤ δ
  /-- Same-level comparison, for centers within `20 r_j`. -/
  same : ∀ j ≤ N, ∀ a ∈ F.index j, ∀ b ∈ F.index j,
    dist (F.center j a) (F.center j b) ≤ 20 * F.scale j →
      planeComparison (F.center j a).1 (F.scale j) (F.plane j a) (F.plane j b) ≤ δ
  /-- Adjacent comparison with every level-`j` center within `20 r_j`
  of a level-`(j+1)` center, anchored at the preceding center. -/
  adjacent : ∀ j, j + 1 ≤ N → ∀ a ∈ F.index (j + 1), ∀ b ∈ F.index j,
    dist (F.center (j + 1) a) (F.center j b) ≤ 20 * F.scale j →
      planeComparison (F.center j b).1 (F.scale j) (F.plane (j + 1) a) (F.plane j b) ≤ δ

/-- Infinite coherent data: every finite truncation of this one family is coherent. -/
def IsCoherent (σ δ : ℝ) : Prop := ∀ N : ℕ, F.IsCoherentUpTo σ δ N

/-- The center-height bound through level `N`:
`dist(x_{j,a}, L_{j,a}) ≤ κ r_j`. -/
def HasCenterHeightUpTo (κ : ℝ) (N : ℕ) : Prop :=
  ∀ j ≤ N, ∀ a ∈ F.index j,
    Metric.infDist (F.center j a).1 (F.plane j a).toSet ≤ κ * F.scale j

/-- The center-height bound at every level. -/
def HasCenterHeight (κ : ℝ) : Prop :=
  ∀ j : ℕ, ∀ a ∈ F.index j,
    Metric.infDist (F.center j a).1 (F.plane j a).toSet ≤ κ * F.scale j

/-- `z` is the limit of centers `z_{j_i,a_i}` whose levels `j_i` tend to infinity. -/
def IsLevelLimit (z : Space n) : Prop :=
  ∃ (level : ℕ → ℕ) (idx : ℕ → ι), (∀ i, idx i ∈ F.index (level i)) ∧
    Tendsto level atTop atTop ∧
    Tendsto (fun i => F.center (level i) (idx i)) atTop (𝓝 z)

/-- A stopping parent of a point `c` with stopping radius `d` and tube tolerance `θ`.
`some (j, a)` is an
occurrence with `d_P(c, z_{j,a}) ≤ r_j`, `dist(x_c, L_{j,a}) ≤ θ r_j` and
`d ≥ r_j/10`; `none` is the initial plane, with `dist(x_c, L_*) ≤ θ r_0` and
`d ≥ r_0/10`. The initial alternative assigns no physical time to `L_*`. -/
def IsStoppingParent (θ : ℝ) (c : Space n) (d : ℝ) : Option (ℕ × ι) → Prop
  | some (j, a) => a ∈ F.index j ∧ dist c (F.center j a) ≤ F.scale j ∧
      Metric.infDist c.1 (F.plane j a).toSet ≤ θ * F.scale j ∧ F.scale j / 10 ≤ d
  | none => Metric.infDist c.1 F.initialPlane.toSet ≤ θ * F.initialRadius ∧
      F.initialRadius / 10 ≤ d

/-- Horizontal time compatibility of the occurrences through level `N`, with recorded
scales `s_{j,a} = r_j`:
`|t_z - t_w| ≤ γ max{|x_z - x_w|², s_z², s_w²}`. The times are the recorded center
times, not fitted plane times. -/
def IsTimeCompatibleUpTo (γ : ℝ) (N : ℕ) : Prop :=
  ∀ i ≤ N, ∀ j ≤ N, ∀ a ∈ F.index i, ∀ b ∈ F.index j,
    |(F.center i a).2.val - (F.center j b).2.val| ≤
      γ * max (‖(F.center i a).1 - (F.center j b).1‖ ^ 2)
        (max (F.scale i ^ 2) (F.scale j ^ 2))

/-- Horizontal time compatibility of the occurrences at all levels. -/
def IsTimeCompatible (γ : ℝ) : Prop := ∀ N : ℕ, F.IsTimeCompatibleUpTo γ N

end CoherentFamily

end ParabolicRectifiability
