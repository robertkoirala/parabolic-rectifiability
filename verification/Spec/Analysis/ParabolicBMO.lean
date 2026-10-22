import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Basic
import Spec.Geometry.SubspaceCoordinates
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Analysis.ParabolicBMO` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace ParabolicRectifiability
variable {n : ℕ}
/-- The vector average on an intrinsic parabolic ball. Only positive radii
are used in the BMO bound below. -/
def parabolicBallAverage (W : Submodule ℝ (Spatial n))
    (g : SubspaceSpace W → W.orthogonal) (p : SubspaceSpace W) (r : ℝ) : W.orthogonal :=
  ((intrinsicParabolicVolume W (Metric.ball p r)).toReal)⁻¹ •
    ∫ q in Metric.ball p r, g q ∂intrinsicParabolicVolume W

/-- A bound on vector-valued mean oscillation, with local integrability stated
explicitly. The norm inside the integral is the Euclidean normal-space norm. -/
def HasParabolicBMOBound (W : Submodule ℝ (Spatial n))
    (g : SubspaceSpace W → W.orthogonal) (B : ℝ) : Prop :=
  0 ≤ B ∧ LocallyIntegrable g (intrinsicParabolicVolume W) ∧
    ∀ p r, 0 < r →
      (∫ q in Metric.ball p r, ‖g q - parabolicBallAverage W g p r‖
        ∂intrinsicParabolicVolume W) /
          (intrinsicParabolicVolume W (Metric.ball p r)).toReal ≤ B

/-- One scalar normal component in ordinary Fourier coordinates. -/
def normalFourierComponent (W : Submodule ℝ (Spatial n))
    (H : SubspaceSpace W → W.orthogonal) (i : Fin (Module.finrank ℝ W.orthogonal))
    (x : FourierSpace (Module.finrank ℝ W)) : ℝ :=
  normalCoordinates W (H (subspaceFourierToParabolic W x)) i

/-- Representation of the half-time derivative in every orthonormal normal
component. `RepHalf` tests the actual L2 distribution against all real smooth
compactly supported tests. This is not an assumed analytic estimate. -/
def RepresentsHalfTimeDerivative (W : Submodule ℝ (Spatial n))
    (H g : SubspaceSpace W → W.orthogonal) : Prop :=
  ∀ i : Fin (Module.finrank ℝ W.orthogonal),
    ∃ hH : MemLp (normalFourierComponent W H i) 2 volume,
      HalfTimeDerivative.RepHalf hH (normalFourierComponent W g i) Set.univ

/-- The constructed regular class: `G = c + H` with compactly supported
`H`, a parabolic Lipschitz bound `L`, and a vector-valued representative `g`
of the half-time derivative of `H` with BMO bound `B`, where `L + B ≤ ε`.
The scalar `L²` conditions concern `H`, not the constant at infinity. BMO
is tested on every intrinsic parabolic ball of positive radius. For the
general growth class and its homogeneous derivative convention, see
`GeneralRegularVerticalGraph`. -/
def IsRegularVerticalFunction (W : Submodule ℝ (Spatial n))
    (G : SubspaceSpace W → W.orthogonal) (ε : ℝ) : Prop :=
  ∃ (c : W.orthogonal) (H g : SubspaceSpace W → W.orthogonal)
      (L B : ℝ≥0),
    G = (fun p => c + H p) ∧ HasCompactSupport H ∧
    LipschitzWith L G ∧ HasParabolicBMOBound W g (B : ℝ) ∧
    RepresentsHalfTimeDerivative W H g ∧ (L : ℝ) + (B : ℝ) ≤ ε

end ParabolicRectifiability
