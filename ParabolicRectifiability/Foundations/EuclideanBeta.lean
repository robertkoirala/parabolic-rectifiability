import ParabolicRectifiability.Geometry.AffinePlane
import ParabolicRectifiability.Measure.ScaleEnergy

/-! # Euclidean spatial beta-`p` numbers and energies (shared)

Definitions only. They are used in the reductions of the examples (time slices and stationary
sources) and, at `n = 2`, `m = 1`, in the direct witnesses for the beta-`p` quantities. For a
measure `λ` on `ℝⁿ`, an integer `m` and a real exponent `p > 0`,
```
b^E_{p,λ,m}(x,r) = r^{-m-p} inf_{U^m} ∫_{B(x,r)} dist(y,U)^p dλ(y),
```
where `U^m` ranges over all affine `m`-planes of `ℝⁿ` (single points when `m = 0`) and
`B(x,r)` is the open Euclidean ball. The scale energies are
`S^{a,E}_p = ∫_{(0,a)} (b^E_p)^{2/p} dr/r` and `T^{a,E}_p = ∫_{(0,a)} b^E_p dr/r`.

The conventions are those of `Foundations.betaPow`: the distance is `Metric.infEDist` raised
to the `ℝ≥0∞` real power `p`, there is no division by ball mass, values are extended, and the
value is `0` at nonpositive radii. Affine planes are the existing `AffineSpatialPlane n m`
(direction of rank `m` and the anchor closest to the origin), which represents each affine
`m`-plane exactly once. For `m > n` there are no planes and the value is `⊤` at positive radii;
no statement uses that range.

The planar Euclidean `β_p^E` (affine lines of `ℝ²` as `AffineSubspace`s with direction of
`finrank` one) is the same formula at `n = 2`, `m = 1`, on
`EuclideanSpace ℝ (Fin 2) = Spatial 2`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The Euclidean beta-`p` quantity
`b^E_{p,λ,m}(x,r) = r^{-m-p} inf_{U^m} ∫_{B(x,r)} dist(y,U)^p dλ(y)` for `r > 0`, and `0`
for `r ≤ 0`. -/
def euclideanBetaPow {n : ℕ} (ν : Measure (Spatial n)) (m : ℕ) (p : ℝ) (x : Spatial n)
    (r : ℝ) : ℝ≥0∞ :=
  if 0 < r then
    (ENNReal.ofReal r)⁻¹ ^ ((m : ℝ) + p) *
      ⨅ U : AffineSpatialPlane n m, ∫⁻ y in Metric.ball x r, Metric.infEDist y U.toSet ^ p ∂ν
  else 0

/-- The Euclidean quadratic energy `S^{a,E}_p(x) = ∫_{(0,a)} b^E_p(x,r)^{2/p} dr/r`. -/
def euclideanEnergyS {n : ℕ} (ν : Measure (Spatial n)) (m : ℕ) (p a : ℝ) (x : Spatial n) :
    ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 a, euclideanBetaPow ν m p x r ^ (2 / p) ∂scaleMeasure

/-- The Euclidean `p`-power energy `T^{a,E}_p(x) = ∫_{(0,a)} b^E_p(x,r) dr/r`. -/
def euclideanEnergyT {n : ℕ} (ν : Measure (Spatial n)) (m : ℕ) (p a : ℝ) (x : Spatial n) :
    ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 a, euclideanBetaPow ν m p x r ∂scaleMeasure

end ParabolicRectifiability.Foundations
