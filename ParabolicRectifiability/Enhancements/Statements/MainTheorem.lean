import ParabolicRectifiability.Enhancements.Decomposition

/-! # Statement of the parabolic rectifiable Reifenberg theorem

Proposition definition `RectifiableReifenbergTheoremStatement`, proved as `rectifiable_reifenberg_theorem`.
It strengthens `MainRectifiabilityStatement`, `FixedFamilyRectifiabilityStatement` and
`AmbientRectifiabilityStatement` in the following respects:

* vertical covers are in the general regular class (`HasGeneralRegularVerticalGraphCover`,
  through `Foundations.HasRegularSupportBounds`);
* the global bound `H_P^k(K) ≤ C` is added (`HasRegularSupportBounds.hausdorff_total`);
* one constant `C` serves the mixed, fixed-family and ambient clauses.

Conventions are those of the main statements: "locally Radon" is
`IsFiniteMeasureOnCompacts μ` with `μ.InnerRegular`; `P(0,1)` is
`Metric.ball (point 0 0) 1`; the mixed exceptional set is `exceptionalSet`;
real constants are compared through `ENNReal.ofReal`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-- **The parabolic rectifiable Reifenberg theorem.**

For each `n ≥ 1` there is one constant `C > 0` such that:

* **mixed**: for every integer `1 ≤ k ≤ n+2`, every locally Radon `μ` and
  all real `M, Γ ≥ 0` with `μ(P(0,1) ∩ {S²_{μ,A_k} > M}) ≤ Γ`, there are retained
  sets `D` with all conclusions `IsRectifiableReifenbergDecomposition k C M Γ μ D`;
* **fixed family**: for every available fixed family `T` (horizontal or
  vertical, `Nonempty (Models n k T)`), the fixed-energy threshold
  `μ(P(0,1) ∩ {S²_{μ,T} > M}) ≤ Γ` gives the same conclusions, with zero measure and
  empty support of the other type;
* **ambient**: at `k = n+2`, with no energy hypothesis, the same
  conclusions hold with `M = Γ = 0` and remainder exactly `0` on `P(0,1)`.

The retained sets and actual supports are chosen before every graph tolerance (the
covers are quantified inside the decomposition). `C` is chosen before `k`, `T`, `μ`, `M`,
`Γ` and every tolerance. -/
def RectifiableReifenbergTheoremStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (exceptionalSet μ k M) ≤ ENNReal.ofReal Γ →
        ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition k C M Γ μ D) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, T ≠ .mixed → Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M Γ : ℝ, 0 ≤ M → 0 ≤ Γ →
        μ (Metric.ball (point 0 0) 1 ∩
          {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
        ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition k C M Γ μ D ∧
          (T = .horizontal → D.verticalMeasure μ = 0 ∧ D.verticalSupport μ = ∅) ∧
          (T = .vertical → D.horizontalMeasure μ = 0 ∧ D.horizontalSupport μ = ∅)) ∧
    (∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∃ D : RetainedSets n, IsRectifiableReifenbergDecomposition (n + 2) C 0 0 μ D ∧
        D.remainderMeasure μ (Metric.ball (point 0 0) 1) = 0)

end ParabolicRectifiability.Enhancements
