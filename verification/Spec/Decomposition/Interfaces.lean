import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.ModelDistance
import Spec.Geometry.SubspaceCoordinates
import Spec.Measure.Beta
import Spec.Measure.BetaLaws
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Hausdorff
import Spec.Metric.Measure
import Spec.Metric.Similarity
import Spec.Metric.Space
import Spec.Specifications.Rectifiability

/-! Specification: the definitions of `ParabolicRectifiability.Decomposition.Interfaces` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace ParabolicRectifiability
/-- Final family-specific output, with genuine measures and supports. -/
def HasFamilyDecomposition {n : ℕ} (k : ℕ) (T : FamilyKind) (C M Γ : ℝ)
    (μ : Measure (Space n)) : Prop :=
  ∃ D : RetainedSets n, IsRectifiabilityDecomposition k C M Γ μ D ∧
    (T = .horizontal → D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅) ∧
    (T = .vertical → D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅)

end ParabolicRectifiability
