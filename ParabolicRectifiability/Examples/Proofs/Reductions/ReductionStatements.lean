import ParabolicRectifiability.Examples.Proofs.Reductions.TimeSliceStatements

/-! # Named statements of the stationary reductions

Definitions and proposition definitions only; the proofs are given separately.

Target: `Examples.reductions_bundle : ReductionsStatement`, the conjunction
`TimeSliceStatement ∧ TimeSliceTubeStatement ∧ StationaryProductStatement ∧
StationaryGraphExtensionStatement`. The first two conjuncts come from the shared time-slice
statements; this file states the stationary ones.

Stationary product (`μ = ν ⊗ L¹⌊[-1,1]`, `k = m + 2`, `ℓ = |(t-r², t+r²) ∩ [-1,1]|`):
* `E2StationaryLengthStatement`: `r²/2 ≤ ℓ ≤ 2r²` for `t ∈ [-1,1]`, `0 < r ≤ 2`.
* `E2StationaryVerticalStatement`: the vertical identity `β²_V = (ℓ/r²) b^E` (Tonelli).
* `E2StationaryHorizontalStatement`: the horizontal lower bound `(1/16) b^E ≤ β²_H`
  (implication form over `E2StationaryLengthStatement`).
* `E2StationaryAssemblyStatement`: the three comparisons of `StationaryProductStatement`
  (implication form over the three previous statements).

Stationary graphs (`W ⊆ ℝⁿ`, `m = dim W`):
* `E2OrthogonalExtensionStatement`: coordinatewise McShane extension with bound
  `√(n-m) L`.
* `E2TimeIndependentHalfTimeStatement`: a time-independent parabolic Lipschitz function has
  the zero half-time derivative representative with BMO seminorm zero.
The graph assembly (parabolic Lipschitz bound, general regular predicate, full graph and its
image) is carried out in `e2_stationaryGraphExtension`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.Foundations

/-! ## Stationary product -/

/-- The stationary source `μ = ν ⊗ (L¹⌊[-1,1])` on `Space n`, literally the measure of
`StationaryProductStatement`. -/
abbrev e2_stationarySource {n : ℕ} (ν : Measure (Spatial n)) : Measure (Space n) :=
  Measure.map (fun q : Spatial n × ℝ => point q.1 q.2) (ν.prod (volume.restrict (Icc (-1 : ℝ) 1)))

/-- **Interval length.** For `t ∈ [-1,1]` and `0 < r ≤ 2`,
`r²/2 ≤ |(t-r², t+r²) ∩ [-1,1]| ≤ 2r²`. -/
def E2StationaryLengthStatement : Prop :=
  ∀ t r : ℝ, t ∈ Icc (-1 : ℝ) 1 → 0 < r → r ≤ 2 →
    ENNReal.ofReal (r ^ 2 / 2) ≤ volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) ∧
      volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal (2 * r ^ 2)

/-- **Vertical identity.** The first clause of
`StationaryProductStatement`: `β²_{V,μ,m+2}((x,t),r) = (ℓ/r²) b^E_{2,ν,m}(x,r)` (the vertical
distance depends only on space, so Tonelli gives the identity). -/
def E2StationaryVerticalStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m + 1 ≤ n →
  ∀ ν : Measure (Spatial n), IsFiniteMeasureOnCompacts ν → ν.InnerRegular →
  ∀ (x : Spatial n) (t r : ℝ), t ∈ Icc (-1 : ℝ) 1 → 0 < r → r ≤ 2 →
    betaSq (e2_stationarySource ν) (m + 2) .vertical (point x t) r =
      volume (Ioo (t - r ^ 2) (t + r ^ 2) ∩ Icc (-1 : ℝ) 1) / ENNReal.ofReal r ^ 2 *
        euclideanBetaPow ν m 2 x r

/-- **Horizontal lower bound.** Every horizontal model has squared
distance at least `|s - τ|`, whose integral over an interval of length `ℓ ≥ r²/2` is at least
`ℓ²/4`; with a plane through `x` (`b^E ≤ r^{-m} ν(B(x,r))`) this gives
`(1/16) b^E ≤ β²_{H,μ,m+2}`. An unavailable horizontal family gives `⊤`.
Implication form over the interval length. -/
def E2StationaryHorizontalStatement : Prop :=
  E2StationaryLengthStatement →
  ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m + 1 ≤ n →
  ∀ ν : Measure (Spatial n), IsFiniteMeasureOnCompacts ν → ν.InnerRegular →
  ∀ (x : Spatial n) (t r : ℝ), t ∈ Icc (-1 : ℝ) 1 → 0 < r → r ≤ 2 →
    ENNReal.ofReal (1 / 16) * euclideanBetaPow ν m 2 x r ≤
      betaSq (e2_stationarySource ν) (m + 2) .horizontal (point x t) r

/-- **Assembly of the stationary comparisons.** The three clauses of
`StationaryProductStatement` from the interval length, the vertical identity and the horizontal lower bound: the mixed square is the minimum of the
horizontal and vertical ones (`iInf_sum`), `ℓ/r² ∈ [1/2, 2]`. -/
def E2StationaryAssemblyStatement : Prop :=
  E2StationaryLengthStatement → E2StationaryVerticalStatement →
    E2StationaryHorizontalStatement → StationaryProductStatement

/-! ## Stationary graphs -/

/-- **Orthogonal Lipschitz extension.** Every `L`-Lipschitz map
`g : E → W^⊥` on an arbitrary subset `E ⊆ W` (empty allowed) extends to `g' : W → W^⊥` with
Lipschitz bound `√(n - dim W) L` (coordinatewise McShane in an orthonormal basis of `W^⊥`). -/
def E2OrthogonalExtensionStatement : Prop :=
  ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (E : Set W) (g : E → Wᗮ) (L : ℝ≥0),
    LipschitzWith L g →
    ∃ g' : W → Wᗮ, (∀ u : E, g' u = g u) ∧
      LipschitzWith (NNReal.sqrt ((n - Module.finrank ℝ W : ℕ) : ℝ≥0) * L) g'

/-- **Time-independent functions have zero half-time derivative.** For a
Lipschitz `h : W → W^⊥`, the time-independent `G(u,t) = h(u)` on `W × ℝ` is represented by the
zero half-time derivative, and the zero function has parabolic BMO bound `0`. -/
def E2TimeIndependentHalfTimeStatement : Prop :=
  ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (h : W → Wᗮ) (K : ℝ≥0), LipschitzWith K h →
    RepresentsGeneralHalfTimeDerivative W (fun q : SubspaceSpace W => h q.1) (fun _ => 0) ∧
      HasParabolicBMOBound W (fun _ => 0) 0

end ParabolicRectifiability.Examples
