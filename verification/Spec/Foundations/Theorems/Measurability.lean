import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact
import Spec.Analysis.Coordinates
import Spec.Analysis.HalfTimeDerivative.Basic
import Spec.Analysis.HalfTimeDerivative.LocalRepresentation
import Spec.Analysis.ParabolicBMO
import Spec.Basic
import Spec.BetaP.Proofs.Counterexamples.Euclidean
import Spec.BetaP.Statements.Failures
import Spec.BetaP.Statements.Laws
import Spec.BetaP.Statements.Main
import Spec.Decomposition.Interfaces
import Spec.Examples.Lacunary
import Spec.Foundations.BetaPow
import Spec.Foundations.Density
import Spec.Foundations.EuclideanBeta
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
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
import Spec.Specifications.Rectifiability

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.Theorems.Measurability` used by the headline statements. -/

namespace ParabolicRectifiability.Foundations
/-- Borel measurability of both densities for a locally Radon source. Proved by
`fmeas1_density_measurability`. -/
theorem measurable_densities : DensityMeasurabilityStatement := by
  sorry

/-- Borel restrictions of a locally Radon source are locally Radon. Proved by
`restrict_isFiniteMeasureOnCompacts_innerRegular_proof`. -/
theorem restrict_locallyRadon : RestrictLocallyRadonStatement := by
  sorry

/-- `ν ≤ c μ` gives `b_ν ≤ c b_μ` and `S_ν ≤ c S_μ`. -/
theorem betaSq_squareEnergy_le_of_le_smul : BetaEnergyDominationStatement := by
  sorry

/-- The finite-annulus bound. Proved by `lintegral_betaSq_Ioo_le_annulus_proof`. -/
theorem lintegral_betaSq_annulus_le : AnnulusBoundStatement := by
  sorry

/-- Square finiteness is independent of the finite positive endpoint. Proved by
`squareEnergy_lt_top_iff_of_endpoints_proof`. -/
theorem squareEnergy_lt_top_iff_of_pos : SquareFinitenessEndpointStatement := by
  sorry

/-- The dilation identity `S_{μ_{q,R}}^A(z) = S_μ^{RA}(q + δ_R z)`. -/
theorem squareEnergy_rescaledSource : SquareEnergyRescalingStatement := by
  sorry

/-- `S_{cμ}^A = c S_μ^A` for real `c > 0` and every family. -/
theorem squareEnergy_ofReal_smul : SquareEnergySmulStatement := by
  sorry

/-- `B_2 = betaSq`. -/
theorem betaPow_two_eq_betaSq : BetaPowTwoStatement := by
  sorry

/-- `S_2^a = T_2^a = squareEnergy`. -/
theorem energyS_energyT_two_eq_squareEnergy : EnergyTwoStatement := by
  sorry

/-- The amplitude laws `S_{p,cμ} = c^{2/p} S_{p,μ}` and `T_{p,cμ} = c T_{p,μ}`. -/
theorem energyS_energyT_ofReal_smul : EnergyPowSmulStatement := by
  sorry

end ParabolicRectifiability.Foundations
