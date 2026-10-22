import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.ModelDistance
import Spec.Measure.Beta
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.EuclideanBeta` used by the headline statements. -/

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
