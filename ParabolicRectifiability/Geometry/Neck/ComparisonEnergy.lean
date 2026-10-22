import ParabolicRectifiability.Geometry.Neck.CoherentData

/-!
# The comparison square function

Definitions only. The comparison functions `E_j` are defined once, for a position map
`pos : Space n → W` into a metric space `W` of reference points:

* vertical case: `W = Space n`, `pos = id`, all distances parabolic;
* horizontal case: `W = Spatial n`, `pos = Prod.fst`, all distances between
  spatial coordinates are Euclidean.

In both cases the planes and the comparison `d_{x,r}` remain spatial. All
incidence conditions use closed balls of radius `12 r`; pair ranges are `20 r`.
Each `E_j(w)` is a supremum in `ℝ≥0∞` over a finite list of finite values, i.e.
their maximum, and an empty maximum is `0`. The comparison square bound is the
pointwise bound `∑' j, E_j(w)^2 ≤ E` at every reference point `w`, an extended
nonnegative series which may a priori be infinite. Plane comparisons are
nonnegative because all scales are positive, so `ENNReal.ofReal` loses nothing.
-/

noncomputable section

namespace ParabolicRectifiability

open scoped ENNReal

variable {n m : ℕ} {ι : Type*} {W : Type*} [PseudoMetricSpace W]

namespace CoherentFamily

variable (pos : Space n → W) (F : CoherentFamily n m ι)

/-- Level zero: the maximum of `d_{x_{0,a},r_0}(L_{0,a}, L_*)` over centers within
`12 r_0` of `w`. -/
def rootComparisonTerm (w : W) : ℝ≥0∞ :=
  ⨆ a ∈ F.index 0, ⨆ (_ : dist (pos (F.center 0 a)) w ≤ 12 * F.scale 0),
    ENNReal.ofReal (planeComparison (F.center 0 a).1 (F.scale 0) (F.plane 0 a) F.initialPlane)

/-- Item 1 of `E_{j+1}`: same-level comparisons `d_{x_{j,a},r_j}(L_{j,a}, L_{j,b})`
for pairs at distance at most `20 r_j`, both within `12 r_j` of `w`. -/
def sameLevelComparisonTerm (j : ℕ) (w : W) : ℝ≥0∞ :=
  ⨆ a ∈ F.index j, ⨆ b ∈ F.index j,
    ⨆ (_ : dist (pos (F.center j a)) (pos (F.center j b)) ≤ 20 * F.scale j ∧
        dist (pos (F.center j a)) w ≤ 12 * F.scale j ∧
        dist (pos (F.center j b)) w ≤ 12 * F.scale j),
      ENNReal.ofReal (planeComparison (F.center j a).1 (F.scale j) (F.plane j a) (F.plane j b))

/-- Item 2 of `E_{j+1}`: adjacent comparisons `d_{x_{j,b},r_j}(L_{j+1,a}, L_{j,b})`
for a level-`(j+1)` center and a level-`j` center at distance at most `20 r_j`,
both within `12 r_j` of `w`. -/
def adjacentComparisonTerm (j : ℕ) (w : W) : ℝ≥0∞ :=
  ⨆ a ∈ F.index (j + 1), ⨆ b ∈ F.index j,
    ⨆ (_ : dist (pos (F.center (j + 1) a)) (pos (F.center j b)) ≤ 20 * F.scale j ∧
        dist (pos (F.center (j + 1) a)) w ≤ 12 * F.scale j ∧
        dist (pos (F.center j b)) w ≤ 12 * F.scale j),
      ENNReal.ofReal
        (planeComparison (F.center j b).1 (F.scale j) (F.plane (j + 1) a) (F.plane j b))

/-- The comparison function `E_j(w)`, for the distances determined by `pos`. -/
def comparisonEnergy : ℕ → W → ℝ≥0∞
  | 0, w => F.rootComparisonTerm pos w
  | j + 1, w => max (F.sameLevelComparisonTerm pos j w) (F.adjacentComparisonTerm pos j w)

/-- The comparison square bound `sup_w ∑_{j ≥ 0} E_j(w)^2 ≤ E`. -/
def SquareBound (E : ℝ) : Prop :=
  ∀ w : W, ∑' j, F.comparisonEnergy pos j w ^ 2 ≤ ENNReal.ofReal E

/-- The same bound for the levels `0, …, N` of a finite truncation. -/
def SquareBoundUpTo (E : ℝ) (N : ℕ) : Prop :=
  ∀ w : W, ∑ j ∈ Finset.range (N + 1), F.comparisonEnergy pos j w ^ 2 ≤ ENNReal.ofReal E

end CoherentFamily

namespace CoherentFamily

variable (F : CoherentFamily n m ι)

/-- Vertical comparison functions `E_j(w)`, `w ∈ X`, with parabolic distances. -/
def verticalEnergy (j : ℕ) (w : Space n) : ℝ≥0∞ :=
  F.comparisonEnergy (fun z : Space n => z) j w

/-- Horizontal comparison functions `E_j^H(w)`, `w ∈ ℝ^n`, with Euclidean distances
between spatial coordinates. -/
def horizontalEnergy (j : ℕ) (w : Spatial n) : ℝ≥0∞ :=
  F.comparisonEnergy (fun z : Space n => z.1) j w

/-- Vertical comparison square bound `sup_{w ∈ X} ∑_j E_j(w)^2 ≤ E`. -/
def VerticalSquareBound (E : ℝ) : Prop :=
  F.SquareBound (fun z : Space n => z) E

/-- Horizontal comparison square bound `sup_{w ∈ ℝ^n} ∑_j E_j^H(w)^2 ≤ E`. -/
def HorizontalSquareBound (E : ℝ) : Prop :=
  F.SquareBound (fun z : Space n => z.1) E

/-- Vertical square bound for the levels `0, …, N`. -/
def VerticalSquareBoundUpTo (E : ℝ) (N : ℕ) : Prop :=
  F.SquareBoundUpTo (fun z : Space n => z) E N

/-- Horizontal square bound for the levels `0, …, N`. -/
def HorizontalSquareBoundUpTo (E : ℝ) (N : ℕ) : Prop :=
  F.SquareBoundUpTo (fun z : Space n => z.1) E N

end CoherentFamily

end ParabolicRectifiability
