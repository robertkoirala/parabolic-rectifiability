import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas
import Spec.Basic
import Spec.Foundations.EuclideanBeta
import Spec.Geometry.AdmissibleModels
import Spec.Geometry.AffinePlane
import Spec.Geometry.ModelDistance
import Spec.Measure.Beta
import Spec.Measure.CountableFitting
import Spec.Measure.ScaleEnergy
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.BetaP.Proofs.Counterexamples.Euclidean` used by the headline statements. -/

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
