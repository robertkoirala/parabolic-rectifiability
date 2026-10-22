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
import Spec.Foundations.ADR
import Spec.Foundations.BetaPow
import Spec.Foundations.Graphs
import Spec.Foundations.HalfTimeDerivative
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

/-! Specification: the definitions of `ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry` used by the headline statements. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.QuantitativeCharacterization
open ParabolicRectifiability.Foundations
/-- **The scaling identity.** For `S_{a,R}(z) = δ_{1/R}(z - a)` and
`μ_{a,R} = R^{-k} (S_{a,R})_# μ`, which is the existing `rescaledSource μ k a R hR`,
`β_{μ_{a,R}}(z,r)² = β_μ(a + δ_R z, R r)²` for the mixed family, every centre `z` and every
positive radius `r`. The point `a + δ_R z` is `(similarity a R hR).symm z`
(`similarity_symm_apply`). As in the cited sentence, no regularity of `μ` is assumed and
`a` is arbitrary. (The identity at a moved centre for every family is the existing
`betaSq_rescaledSource`.) -/
def BetaScalingStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), ∀ (a : Space n) (R : ℝ) (hR : 0 < R),
  ∀ (z : Space n) (r : ℝ), 0 < r →
    betaSq (rescaledSource μ k a R hR) k .mixed z r =
      betaSq μ k .mixed ((similarity a R hR).symm z) (R * r)

/-- **Monotonicity**: increasing either constant preserves the
`(K,L)`-quantitative mixed parabolic rectifiability of a locally Radon measure. -/
def QuantitativeRectifiabilityMonoStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
  ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
  ∀ K K' L L' : ℝ, 1 ≤ K → K ≤ K' → 1 ≤ L → L ≤ L' →
    IsQuantitativelyMixedRectifiable k K L μ → IsQuantitativelyMixedRectifiable k K' L' μ

end ParabolicRectifiability.QuantitativeCharacterization
