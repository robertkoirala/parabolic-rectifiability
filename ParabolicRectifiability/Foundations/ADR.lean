import ParabolicRectifiability.Metric.Hausdorff

/-! # Ahlfors–David regularity

Two notions of Ahlfors–David regularity in the parabolic space, used by the
characterization and the quantitative characterization respectively.

* `IsADRCarrier k c C Γ σ`: a closed Ahlfors–David regular reference carrier `Γ` with
  measure `σ`, the setting of the source-transfer argument.
* `IsADR A k μ`: global `A`-Ahlfors–David regularity of a measure on its support.

The two predicates are kept separate: `IsADRCarrier` fixes a set and
a measure with two positive constants `c, C`, a positive dimension and Radon hypotheses;
`IsADR` is a single-constant condition `A⁻¹ r^k ≤ μ(P(z,r)) ≤ A r^k` on `supp μ` with no
further hypotheses.

Conventions. `P(z,r)` is the open parabolic ball `Metric.ball z r`, real constants are
compared through `ENNReal.ofReal`, and the support is the topological support
`Measure.support`.
-/

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
