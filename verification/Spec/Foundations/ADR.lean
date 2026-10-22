import Spec.Basic
import Spec.Metric.Hausdorff
import Spec.Metric.Space

/-! Specification: the definitions of `ParabolicRectifiability.Foundations.ADR` used by the headline statements. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ParabolicRectifiability.Foundations
/-- The reference carrier of the source-transfer argument:
`Γ ⊆ X` is nonempty and closed, `σ` is a Radon measure (finite on compacts and inner
regular, the project's convention) with `supp σ = Γ`, and
`c r^k ≤ σ(P(z,r)) ≤ C r^k` for every `z ∈ Γ` and every `r > 0`, with `k > 0`.

The dimension `k` is the natural number of the ambient setting: the transfer proposition
measures `σ` and the source against `k`-dimensional admissible models through
`squareEnergy`, whose dimension is a natural number. The ADR constants `c, C` are real and
positive. The support is the topological support `Measure.support`. -/
structure IsADRCarrier {n : ℕ} (k : ℕ) (c C : ℝ) (Γ : Set (Space n))
    (σ : Measure (Space n)) : Prop where
  dimension_pos : 0 < k
  lower_pos : 0 < c
  upper_pos : 0 < C
  nonempty : Γ.Nonempty
  isClosed : IsClosed Γ
  finiteOnCompacts : IsFiniteMeasureOnCompacts σ
  innerRegular : σ.InnerRegular
  support_eq : σ.support = Γ
  lower : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → ENNReal.ofReal (c * r ^ k) ≤ σ (Metric.ball z r)
  upper : ∀ z ∈ Γ, ∀ r : ℝ, 0 < r → σ (Metric.ball z r) ≤ ENNReal.ofReal (C * r ^ k)

/-- Global `A`-Ahlfors–David regularity in dimension `k`:
`A⁻¹ r^k ≤ μ(P(z,r)) ≤ A r^k` for every `z ∈ E = supp μ` and every `r > 0`. -/
def IsADR {n : ℕ} (A : ℝ) (k : ℕ) (μ : Measure (Space n)) : Prop :=
  ∀ z ∈ μ.support, ∀ r : ℝ, 0 < r →
    ENNReal.ofReal (A⁻¹ * r ^ k) ≤ μ (Metric.ball z r) ∧
      μ (Metric.ball z r) ≤ ENNReal.ofReal (A * r ^ k)

end ParabolicRectifiability.Foundations
