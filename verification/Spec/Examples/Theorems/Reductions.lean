import Mathlib
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UnitInterval
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.Examples.DenseAtoms
import Spec.Examples.Lacunary
import Spec.Examples.Statements.DensityExamples
import Spec.Examples.Statements.Lacunary
import Spec.Examples.Statements.Reductions
import Spec.Foundations.ADR
import Spec.Foundations.BetaPow
import Spec.Foundations.Carriers
import Spec.Foundations.Density
import Spec.Foundations.EuclideanBeta
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Foundations.Statements.Ambient
import Spec.Foundations.Statements.CompactBridge
import Spec.Foundations.Statements.Measurability
import Spec.Foundations.SupportBounds
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
import Spec.QuantitativeCharacterization.Coverings
import Spec.QuantitativeCharacterization.References
import Spec.QuantitativeCharacterization.Statements.Geometry

/-! Specification: the definitions of `ParabolicRectifiability.Examples.Theorems.Reductions` used by the headline statements. -/

namespace ParabolicRectifiability.Examples
/-- The exact Euclidean reductions: constant-time pushforwards
preserve horizontal and mixed beta-`p` energies; slice tubes have time factor `2r²`;
stationary products have the vertical identity and mixed comparison for `0 < r ≤ 2`;
and spatial subset graphs extend to full stationary general regular vertical graphs.
The four specifications and their dimension ranges are in `ReductionsStatement`. -/
theorem exact_reductions : ReductionsStatement := by
  sorry

end ParabolicRectifiability.Examples
