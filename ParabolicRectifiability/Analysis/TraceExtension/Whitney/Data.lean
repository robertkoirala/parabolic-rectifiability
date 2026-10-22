import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Metric.Measure

/-! # Whitney cells, nodes, weights and the Whitney filling

Definitions for the regular trace extension, on ordinary coordinates `Space m = ℝ^m × Time` with
the parabolic volume. Here `k = m + 2`, so `k + 2 = m + 4`.

* `ParabolicDyadicBox`: half-open boxes of spatial side `2^(-j)` and time side
  `4^(-j)`, their centers, parents and open enlargements; `whitneyBoxes F₀` are
  the maximal eligible boxes with `whitneyA m = 10^4 whitneyD m`.
* `WhitneyData m ι F₀ D a`: a disjoint measurable family of cells
  covering `F₀ᶜ`, with centers in the cells, positive radii, `|Q_j| = r_j^k`,
  `Q_j ⊆ closedBall(p_j, D r_j)` and `dist(q, F₀) ≥ a r_j` on `Q_j`. Local
  finiteness of the node measure is a theorem to prove, not a field.
* The node set `C = F₀ ∪ {p_j}` and the full node measure
  `ν = vol⌞F₀ + Σ_j r_j^k δ_{p_j}`; cell incidence `J(y,s)` (cells meeting the
  open ball) and the cube-defect integrand `s^(-k-2) Σ_{j ∈ J(y,s)} r_j^(k+2)`;
  the node Carleson integral with lower scale `ρ = 0` on `F₀` and `ρ = r_j` at
  `p_j`.
* `WhitneyWeights W H`: nonnegative measurable weights, locally finite and
  summing to one off `F₀`, with the elementary locality `dist(p_i,p_j) ≤ H r_j`
  whenever `φ_i` is nonzero on `Q_j`; `whitneyFilling` is `g` on `F₀` and
  `Σ_i φ_i g(p_i)` off `F₀`. No transfer inequality is a field.
* `HasParabolicDerivBounds φ K r` and `WhitneyPartition`: the smooth
  partition bounds `|∇_u φ| ≤ K/r`, `|∇_u² φ| ≤ K/r²` and `|∂_t φ| ≤ K/r²`,
  comparable overlapping scales, bounded overlap and the upper center distance.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability

/-! ## Parabolic dyadic boxes -/

/-- A parabolic dyadic box: level `j`, spatial integer corner `κ`, time integer
corner `τ`. Its set is `Π_i [κ_i r, (κ_i+1) r) × [τ r², (τ+1) r²)`, `r = 2^(-j)`. -/
structure ParabolicDyadicBox (m : ℕ) where
  level : ℤ
  space : Fin m → ℤ
  time : ℤ

namespace ParabolicDyadicBox

variable {m : ℕ}

instance : Countable (ParabolicDyadicBox m) := by
  have hinj : Function.Injective
      (fun Q : ParabolicDyadicBox m => (Q.level, Q.space, Q.time)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  exact hinj.countable

/-- The side length `r_Q = 2^(-level)`. -/
def radius (Q : ParabolicDyadicBox m) : ℝ := (2 : ℝ) ^ (-Q.level)

/-- The half-open box itself. -/
def toSet (Q : ParabolicDyadicBox m) : Set (Space m) :=
  {z | (∀ i, (Q.space i : ℝ) * Q.radius ≤ z.1 i ∧ z.1 i < ((Q.space i : ℝ) + 1) * Q.radius) ∧
    (Q.time : ℝ) * Q.radius ^ 2 ≤ z.2.val ∧ z.2.val < ((Q.time : ℝ) + 1) * Q.radius ^ 2}

/-- The center `p_Q`. -/
def center (Q : ParabolicDyadicBox m) : Space m :=
  point (WithLp.toLp 2 (fun i : Fin m => ((Q.space i : ℝ) + 1 / 2) * Q.radius) : Spatial m)
    (((Q.time : ℝ) + 1 / 2) * Q.radius ^ 2)

/-- The unique box of the previous level containing `Q` (floor division by `2`
in space and by `4` in time). -/
def parent (Q : ParabolicDyadicBox m) : ParabolicDyadicBox m where
  level := Q.level - 1
  space := fun i => Q.space i / 2
  time := Q.time / 4

/-- The open box with the same center and spatial and temporal side lengths
`θ r_Q` and `θ r_Q²`. -/
def enlarged (Q : ParabolicDyadicBox m) (θ : ℝ) : Set (Space m) :=
  {z | (∀ i, |z.1 i - Q.center.1 i| < θ * Q.radius / 2) ∧
    |z.2.val - Q.center.2.val| < θ * Q.radius ^ 2 / 2}

end ParabolicDyadicBox

/-- The dimensional constant `D_m = max(1, √m)`: every box lies in the closed ball
of radius `D_m r_Q` about its center. -/
def whitneyD (m : ℕ) : ℝ := max 1 (Real.sqrt m)

/-- The eligibility constant `A_W = 10^4 D_m`. -/
def whitneyA (m : ℕ) : ℝ := 10 ^ 4 * whitneyD m

/-- A box is eligible if its center is farther than `A_W r_Q` from `F₀`. -/
def IsWhitneyEligible {m : ℕ} (F₀ : Set (Space m)) (Q : ParabolicDyadicBox m) : Prop :=
  whitneyA m * Q.radius < Metric.infDist Q.center F₀

/-- The maximal eligible boxes: eligible boxes whose parent is not eligible. -/
def whitneyBoxes {m : ℕ} (F₀ : Set (Space m)) : Set (ParabolicDyadicBox m) :=
  {Q | IsWhitneyEligible F₀ Q ∧ ¬ IsWhitneyEligible F₀ Q.parent}

/-! ## Abstract Whitney data -/

/-- Whitney cell data for a retained set `F₀`, with geometric parameters `D ≥ 1`
and `a > 0`. The index type may be empty, finite or countably infinite. -/
structure WhitneyData (m : ℕ) (ι : Type*) (F₀ : Set (Space m)) (D a : ℝ) where
  cell : ι → Set (Space m)
  center : ι → Space m
  radius : ι → ℝ
  one_le_D : 1 ≤ D
  a_pos : 0 < a
  radius_pos : ∀ j, 0 < radius j
  measurableSet_cell : ∀ j, MeasurableSet (cell j)
  center_mem : ∀ j, center j ∈ cell j
  pairwise_disjoint : Pairwise fun i j => Disjoint (cell i) (cell j)
  iUnion_cell : ⋃ j, cell j = F₀ᶜ
  volume_cell : ∀ j, parabolicVolume m (cell j) = ENNReal.ofReal (radius j ^ (m + 2))
  cell_subset : ∀ j, cell j ⊆ Metric.closedBall (center j) (D * radius j)
  le_infDist : ∀ j, ∀ q ∈ cell j, a * radius j ≤ Metric.infDist q F₀

namespace WhitneyData

variable {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}

/-- The node set `C = F₀ ∪ {p_j}`. -/
def nodeSet (W : WhitneyData m ι F₀ D a) : Set (Space m) := F₀ ∪ Set.range W.center

/-- The full node measure `ν = vol⌞F₀ + Σ_j r_j^k δ_{p_j}`. -/
def nodeMeasure (W : WhitneyData m ι F₀ D a) : Measure (Space m) :=
  (parabolicVolume m).restrict F₀ +
    Measure.sum fun j => ENNReal.ofReal (W.radius j ^ (m + 2)) • Measure.dirac (W.center j)

/-- Cell incidence `J(y,s)`: the cells meeting the open ball `P(y,s)`. -/
def incidence (W : WhitneyData m ι F₀ D a) (y : Space m) (s : ℝ) : Set ι :=
  {j | (W.cell j ∩ Metric.ball y s).Nonempty}

/-- The cube-defect integrand `s^(-k-2) Σ_{j ∈ J(y,s)} r_j^(k+2)`, `k = m + 2`,
as an extended nonnegative countable sum. -/
def cubeDefect (W : WhitneyData m ι F₀ D a) (y : Space m) (s : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal s)⁻¹ ^ (m + 4) *
    ∑' j, (W.incidence y s).indicator (fun j => ENNReal.ofReal (W.radius j ^ (m + 4))) j

/-- The node Carleson integral `∫_{C ∩ P(z,R)} ∫_{ρ(p)}^R α(p,s)^2 ds/s dν(p)`,
with `ρ = 0` on `F₀` and `ρ(p_j) = r_j`; an empty scale range contributes zero.
`α` is the constrained error for the full node measure `ν` and slope bound `L`. -/
def nodeCarlesonIntegral {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (W : WhitneyData m ι F₀ D a) (g : Space m → Y) (L : ℝ≥0) (z : Space m) (R : ℝ) :
    ℝ≥0∞ :=
  (∫⁻ p in F₀ ∩ Metric.ball z R, ∫⁻ s in Ioo 0 R,
      constrainedAffineErrorSq W.nodeMeasure g L p s ∂scaleMeasure ∂parabolicVolume m) +
    ∑' j, (Metric.ball z R).indicator (fun _ => ENNReal.ofReal (W.radius j ^ (m + 2)))
        (W.center j) *
      ∫⁻ s in Ioo (W.radius j) R,
        constrainedAffineErrorSq W.nodeMeasure g L (W.center j) s ∂scaleMeasure

end WhitneyData

/-! ## Weights, smooth partitions and the filling -/

/-- Partition weights for Whitney data, with the elementary locality constant `H`. -/
structure WhitneyWeights {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}
    (W : WhitneyData m ι F₀ D a) (H : ℝ) where
  weight : ι → Space m → ℝ
  nonneg : ∀ i q, 0 ≤ weight i q
  measurable : ∀ i, Measurable (weight i)
  locallyFinite : ∀ q ∉ F₀, ∃ U ∈ 𝓝 q, {i | ∃ x ∈ U, weight i x ≠ 0}.Finite
  hasSum_one : ∀ q ∉ F₀, HasSum (fun i => weight i q) 1
  center_dist_le : ∀ i j, ∀ q ∈ W.cell j, weight i q ≠ 0 →
    dist (W.center i) (W.center j) ≤ H * W.radius j

/-- Parabolic `C^{2,1}` bounds at scale `r`: `C²` in ordinary coordinates,
`|∇_u φ| ≤ K/r`, `|∇_u² φ| ≤ K/r²` and `|∂_t φ| ≤ K/r²`. -/
structure HasParabolicDerivBounds {m : ℕ} (φ : Space m → ℝ) (K r : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun y : Coordinates m => φ (point y.1 y.2))
  spatial_le : ∀ (u : Spatial m) (t : ℝ), ‖fderiv ℝ (fun v => φ (point v t)) u‖ ≤ K / r
  spatial₂_le : ∀ (u : Spatial m) (t : ℝ),
    ‖fderiv ℝ (fun v => fderiv ℝ (fun w => φ (point w t)) v) u‖ ≤ K / r ^ 2
  time_le : ∀ (u : Spatial m) (t : ℝ), |deriv (fun s => φ (point u s)) t| ≤ K / r ^ 2

/-- A smooth Whitney partition: weights with derivative bounds `K` at their own
scale, comparable scales on overlaps, at most `N` nonzero weights at a point,
and the upper center distance `dist(p_j, F₀) ≤ b r_j`. -/
structure WhitneyPartition {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a : ℝ}
    (W : WhitneyData m ι F₀ D a) (H b K : ℝ) (N : ℕ) extends WhitneyWeights W H where
  radius_comparable : ∀ i j, ∀ q ∈ W.cell j, weight i q ≠ 0 →
    W.radius i ≤ 4 * W.radius j ∧ W.radius j ≤ 4 * W.radius i
  overlap_le : ∀ q, {i | weight i q ≠ 0}.encard ≤ N
  infDist_center_le : ∀ j, Metric.infDist (W.center j) F₀ ≤ b * W.radius j
  derivBounds : ∀ i, HasParabolicDerivBounds (weight i) K (W.radius i)

open Classical in
/-- The Whitney filling `F = g` on `F₀` and `F(q) = Σ_i φ_i(q) g(p_i)` off `F₀`. -/
def whitneyFilling {m : ℕ} {ι : Type*} {F₀ : Set (Space m)} {D a H : ℝ}
    {W : WhitneyData m ι F₀ D a} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (φ : WhitneyWeights W H) (g : Space m → Y) (q : Space m) : Y :=
  if q ∈ F₀ then g q else ∑' i, φ.weight i q • g (W.center i)

end ParabolicRectifiability
