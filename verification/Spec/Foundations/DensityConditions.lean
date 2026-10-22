import Spec.Basic
import Spec.Foundations.Density
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.DensityConditions` used by the headline statements. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ParabolicRectifiability.Foundations
/-- Structural condition (a) of the integral criterion: `Θ^{k,*}(μ,·) > 0` and
`Θ_*^k(μ,·) < ∞` at `μ`-almost every point. -/
def HasPositiveUpperFiniteLowerDensity {n : ℕ} (k : ℕ) (μ : Measure (Space n)) : Prop :=
  ∀ᵐ z ∂μ, 0 < upperDensity μ k z ∧ lowerDensity μ k z < ⊤

/-- Structural condition (b) of the integral criterion: `0 < Θ^{k,*}(μ,·) < ∞` at
`μ`-almost every point. This is also the density hypothesis of the density bridge, of the
canonical decomposition and of the classification for the beta-`p` quantities. -/
def HasPositiveFiniteUpperDensity {n : ℕ} (k : ℕ) (μ : Measure (Space n)) : Prop :=
  ∀ᵐ z ∂μ, 0 < upperDensity μ k z ∧ upperDensity μ k z < ⊤

end ParabolicRectifiability.Foundations
