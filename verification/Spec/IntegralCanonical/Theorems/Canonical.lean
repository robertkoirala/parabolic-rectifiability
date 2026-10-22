import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UnitInterval
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.BetaP.Proofs.Counterexamples.Euclidean
import Spec.BetaP.Statements.Failures
import Spec.BetaP.Statements.Laws
import Spec.BetaP.Statements.Main
import Spec.Characterization.Carriers
import Spec.Characterization.Partitions
import Spec.Characterization.Statements.Branches
import Spec.Characterization.Statements.Main
import Spec.Characterization.Statements.SourceTransfer
import Spec.Decomposition.Interfaces
import Spec.Decomposition.ZeroThresholdAndAmbientBranches
import Spec.Enhancements.Decomposition
import Spec.Enhancements.Statements.GraphDomains
import Spec.Enhancements.Statements.MainTheorem
import Spec.Enhancements.Statements.ScaledCore
import Spec.Enhancements.Statements.ScalingRates
import Spec.Enhancements.Theorems.ScaledCore
import Spec.Examples.Lacunary
import Spec.Foundations.ADR
import Spec.Foundations.BetaPow
import Spec.Foundations.Carriers
import Spec.Foundations.Density
import Spec.Foundations.DensityConditions
import Spec.Foundations.EuclideanBeta
import Spec.Foundations.GraphDomainCover
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
import Spec.Foundations.Statements.Ambient
import Spec.Foundations.Statements.CompactBridge
import Spec.Foundations.Statements.DensityBridges
import Spec.Foundations.Statements.Measurability
import Spec.Foundations.SupportBounds
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.Graphs
import Spec.Geometry.ModelDistance
import Spec.Geometry.SubspaceCoordinates
import Spec.IntegralCanonical.Defs
import Spec.IntegralCanonical.Statements.Canonical
import Spec.Main
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
import Spec.Specifications.Rectifiability

/-! Specification: the definitions of `ParabolicRectifiability.IntegralCanonical.Theorems.Canonical` used by the headline statements. -/

namespace ParabolicRectifiability.IntegralCanonical
/-- Positive finite upper `k`-density almost everywhere implies `μ ≪ H_P^k` and a Borel
sigma-finite `H_P^k` carrier for a locally Radon source in `1 ≤ k ≤ n + 2`.
No square-energy hypothesis is needed. -/
theorem isIntrinsicSource_of_upperDensity : IntrinsicSourceOfDensityStatement := by
  sorry

/-- The full canonical decomposition for a locally Radon intrinsic source, or one with
positive finite upper density almost everywhere.
At every `R > 0`, the full-source energy sets define pairwise singular restrictions
`μ_H`, `μ_V`, `μ_+`, with typed rectifiability, graph purity, endpoint independence, and
uniqueness as recorded in `IsCanonicalDecomposition`. -/
theorem canonical_decomposition : CanonicalDecompositionStatement := by
  sorry

/-- For `2 ≤ k ≤ n`, an ordinary vertical graph of Lipschitz bound `L` and a horizontal
graph of slope `ε ≤ 1` with `L ε ≤ 1/2` have `H_P^k`-null intersection. Spatial projection
onto the vertical base is injective there, with inverse bound
`d_P(p,q) ≤ 2(1+L) |P_W p - P_W q|`; at `k = 2` the intersection has at most one point. -/
theorem type_separation : TypeSeparationStatement := by
  sorry

/-- Boundary cases of the canonical sets: `E_V = ∅` at
`k = 1`, `E_H = ∅` at `k = n + 1`, and for intrinsic sources the ambient decomposition
is `(0, μ, 0)`. For `μ = 0` the overlap is source-null, although when both types are
available its literal finite-energy overlap is the whole space. -/
theorem canonical_guards : CanonicalGuardsStatement := by
  sorry

end ParabolicRectifiability.IntegralCanonical
