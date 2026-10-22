import ParabolicRectifiability.Foundations.EuclideanBeta
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Planar densities, pure unrectifiability and the time slice

Definitions only, used for the direct witnesses of the failure examples
(`DirectWitnessMinusStatement`, `DirectWitnessPlusStatement`) and the transfer of energies
through the time slice (`TimeSliceTransferStatement`).

For a measure `ν` on the Euclidean plane `ℝ² = EuclideanSpace ℝ (Fin 2) = Spatial 2`:
```
(β_{p,ν}^E(x,r))^p = r^{-1-p} inf_{L affine line} ∫_{B(x,r)} dist(w,L)^p dν(w),
S_{p,ν}^{a,E}(x)   = ∫_0^a (β_{p,ν}^E(x,r))^2 dr/r.
```
These are the shared Foundations definitions at `n = 2`, `m = 1`:
`(β_{p,ν}^E(x,r))^p = Foundations.euclideanBetaPow ν 1 p x r` and
`S_{p,ν}^{a,E}(x) = Foundations.euclideanEnergyS ν 1 p a x`.
Affine lines are `AffineSpatialPlane 2 1`, the ball is the open Euclidean ball, there is no
division by ball mass, values are extended and nonpositive radii give `0`. These agree with the
planar definitions using affine lines as `AffineSubspace`s of `finrank` one.

The definitions below are specific to the `BetaP` development.
* Arclength-normalized `H¹` is mathlib's `μH[1]` on the plane (diameter-power cost, which gives a
  segment its length).
* Pure one-unrectifiability: `H¹(E ∩ f(A)) = 0` for every `A ⊆ ℝ` and every
  map `f` that is Lipschitz on `A`. This is the standard (Federer, Mattila) notion; it is equivalent
  to the same condition for globally Lipschitz `f : ℝ → ℝ²` and `A = ℝ`, by Lipschitz extension of
  each coordinate.
* The constant-time embedding `x ↦ (x,0)` of `ℝ²` into `X = ℝ² × ℝ` is
  `timeSlice`; it is an isometry onto the time-zero slice.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.BetaP

/-- The Euclidean plane `ℝ²` (reducibly `Spatial 2`). -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The planar one-dimensional ball ratio `ν(B(z,r))/r`, in `ℝ≥0∞`. -/
def planarDensityRatio (ν : Measure Plane) (z : Plane) (r : ℝ) : ℝ≥0∞ :=
  ν (Metric.ball z r) / ENNReal.ofReal r

/-- The planar upper one-density `limsup_{r↓0} ν(B(z,r))/r`. -/
def planarUpperDensity (ν : Measure Plane) (z : Plane) : ℝ≥0∞ :=
  limsup (planarDensityRatio ν z) (𝓝[>] (0 : ℝ))

/-- The planar lower one-density `liminf_{r↓0} ν(B(z,r))/r`. -/
def planarLowerDensity (ν : Measure Plane) (z : Plane) : ℝ≥0∞ :=
  liminf (planarDensityRatio ν z) (𝓝[>] (0 : ℝ))

/-- Pure one-unrectifiability in `ℝ²`: `E` meets every Lipschitz image
`f(A)`, `A ⊆ ℝ`, in an `H¹`-null set. -/
def IsPurelyUnrectifiable (E : Set Plane) : Prop :=
  ∀ (A : Set ℝ) (f : ℝ → Plane) (K : ℝ≥0), LipschitzOnWith K f A → μH[1] (E ∩ f '' A) = 0

/-- The closed horizontal segment `[u,v] × {b}` of `ℝ²` (first coordinate horizontal). -/
def horizontalSegment (u v b : ℝ) : Set Plane :=
  {x | u ≤ x 0 ∧ x 0 ≤ v ∧ x 1 = b}

/-- The constant-time embedding `x ↦ (x,0)` of `ℝ²` into `X = ℝ² × ℝ` at `n = 2`. -/
def timeSlice (x : Plane) : Space 2 :=
  point x 0

end ParabolicRectifiability.BetaP
