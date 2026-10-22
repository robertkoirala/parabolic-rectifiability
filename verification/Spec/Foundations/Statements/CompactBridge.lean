import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.SubspaceCoordinates
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.Statements.CompactBridge` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace ParabolicRectifiability.Foundations
/-- Representative identification: if `g` represents
the existing `L²` half derivative of `H` in every normal component, then, for every
constant `c`, the same `g` represents the general homogeneous half derivative of
`G = c + H` on zero-mean tests, including the ordered-integrability clauses.

This is stronger than the natural statement: it drops the hypotheses that `H` has compact
support and that `c + H` is parabolic Lipschitz, which the
argument does not use. It stays true with the integrability clauses of
`RepresentsHomogeneousHalfTimeDerivative`. For a compact smooth test `φ` and a normal
component `i`: `H_i ∈ L²` (part of `RepresentsHalfTimeDerivative`), `|D_t|^{1/2}φ ∈ L¹ ∩ L²`,
so `(c_i + H_i) |D_t|^{1/2}φ` is integrable on the product. Fubini then gives a.e. inner
integrability and integrability of the bracket on all of `ℝ`, hence on every window;
`c_i |D_t|^{1/2}φ(·,t)` also has compact spatial support. The windows converge to
`c_i ∫ |D_t|^{1/2}φ + ∫ H_i |D_t|^{1/2}φ = 0 + ∫ g_i φ`. -/
def CompactBridgeRepresentativeStatement : Prop :=
  ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (c : W.orthogonal)
    (H g : SubspaceSpace W → W.orthogonal),
    RepresentsHalfTimeDerivative W H g →
      RepresentsGeneralHalfTimeDerivative W (fun p => c + H p) g

/-- Function inclusion at the same tolerance: every function of the existing
compact-perturbation class with `Lip_P G + [g]_BMO ≤ ε` is general regular with the same
bound `ε`. -/
def CompactBridgeFunctionStatement : Prop :=
  ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (G : SubspaceSpace W → W.orthogonal) (ε : ℝ),
    IsRegularVerticalFunction W G ε → IsGeneralRegularVerticalFunction W G ε

/-- Cover inclusion without loss of tolerance: every countable cover modulo
`H_P^k` by core regular vertical graphs of norm at most `ε` is a cover by full general
regular vertical graphs of norm at most `ε`. -/
def CompactBridgeCoverStatement : Prop :=
  ∀ (n k : ℕ) (K : Set (Space n)) (ε : ℝ),
    HasRegularVerticalGraphCover k K ε → HasGeneralRegularVerticalGraphCover k K ε

end ParabolicRectifiability.Foundations
