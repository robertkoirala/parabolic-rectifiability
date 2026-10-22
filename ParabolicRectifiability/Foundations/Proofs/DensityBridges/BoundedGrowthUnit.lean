import ParabolicRectifiability.Foundations.Statements.DensityBridges
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Specifications.Rectifiability

/-! # Retained-mass control at unit scale

Proof of `fbgrowth_unit_ball_le`, as `fbgrowth_unit_ball_le_proof`.

Route: `K = supp(μ⌊H) ∪ supp(μ⌊V)` (overlap allowed). Support conullness
gives `μ(H \ K) = μ(V \ K) = 0`; the retained sets are measurable and disjoint, so
`μ(B ∩ H) + μ(B ∩ V) = μ(B ∩ (H ∪ V)) ≤ (μ⌊K)(B)` with `B = P(0,1)`. The packing-mass premise
`hpack` is applied to the original `μ` and this `K` (its packing hypothesis is the content field
`finite_packing` with `R₀ = 1`, `C_K = C`), and the remainder bound is added. No absolute
continuity is used; `PackingMassStatement` stays an explicit premise.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- Support conullness of a restriction: `μ(E \ supp(μ⌊E)) = 0`, for any set `E`. -/
theorem fbfb4_measure_diff_support_eq_zero {n : ℕ} (μ : Measure (Space n))
    (E : Set (Space n)) : μ (E \ (μ.restrict E).support) = 0 := by
  have h := Measure.measure_compl_support (μ := μ.restrict E)
  rwa [Measure.restrict_apply Measure.isClosed_support.isOpen_compl.measurableSet,
    inter_comm, ← sdiff_eq] at h

/-- The support union of the retained restrictions is a measurable (closed) set. -/
theorem fbfb4_measurableSet_supportUnion {n : ℕ} (μ : Measure (Space n))
    (D : RetainedSets n) : MeasurableSet (D.supportUnion μ) :=
  (Measure.isClosed_support.union Measure.isClosed_support).measurableSet

/-- The retained part outside the support union is `μ`-null. -/
theorem fbfb4_retained_diff_supportUnion_null {n : ℕ} (μ : Measure (Space n))
    (D : RetainedSets n) :
    μ ((D.horizontal ∪ D.vertical) \ D.supportUnion μ) = 0 := by
  refine measure_mono_null ?_ (measure_union_null
    (fbfb4_measure_diff_support_eq_zero μ D.horizontal)
    (fbfb4_measure_diff_support_eq_zero μ D.vertical))
  rintro z ⟨hz | hz, hzK⟩
  · exact Or.inl ⟨hz, fun h => hzK (Or.inl h)⟩
  · exact Or.inr ⟨hz, fun h => hzK (Or.inr h)⟩

/-- Retained mass in a measurable set `B` is at most the mass of `μ⌊K` there,
`K = supp(μ⌊H) ∪ supp(μ⌊V)`. -/
theorem fbfb4_retained_le_restrict_supportUnion {n : ℕ} (μ : Measure (Space n))
    (D : RetainedSets n) {B : Set (Space n)} (hB : MeasurableSet B) :
    D.horizontalMeasure μ B + D.verticalMeasure μ B ≤ μ.restrict (D.supportUnion μ) B := by
  have hsum : D.horizontalMeasure μ B + D.verticalMeasure μ B =
      μ.restrict (D.horizontal ∪ D.vertical) B := by
    show μ.restrict D.horizontal B + μ.restrict D.vertical B = _
    rw [Measure.restrict_union D.disjoint D.measurable_vertical, Measure.add_apply]
  rw [hsum, Measure.restrict_apply hB, Measure.restrict_apply hB]
  calc μ (B ∩ (D.horizontal ∪ D.vertical))
      ≤ μ (B ∩ D.supportUnion μ ∪ (D.horizontal ∪ D.vertical) \ D.supportUnion μ) := by
        refine measure_mono ?_
        rintro z ⟨hzB, hz⟩
        by_cases hzK : z ∈ D.supportUnion μ
        · exact Or.inl ⟨hzB, hzK⟩
        · exact Or.inr ⟨hz, hzK⟩
    _ ≤ μ (B ∩ D.supportUnion μ) + μ ((D.horizontal ∪ D.vertical) \ D.supportUnion μ) :=
        measure_union_le _ _
    _ = μ (B ∩ D.supportUnion μ) := by
        rw [fbfb4_retained_diff_supportUnion_null μ D, add_zero]

/-- **Retained-mass control at unit scale.**

For `1 ≤ n`, `1 ≤ k ≤ n+2`, a locally Radon `μ`, reals `C > 0`, `M ≥ 0`,
`A ≥ 0`, and retained sets `D` forming a core decomposition
`IsRectifiabilityDecomposition k C M 0 μ D` (exceptional allowance `Γ = 0`), if
`Θ_*^k(μ,z) ≤ A` for `μ`-a.e. `z`, then `μ(P(0,1)) ≤ C M + 5^k C A`.

Proof (the type of `fbgrowth_unit_ball_le`):
`hD.measure_eq` on `P(0,1)` splits `μ(P(0,1))` into the remainder (`≤ C M + 0`,
`hD.remainder_bound`) and the retained mass, which is `≤ (μ⌊K)(P(0,1))` for
`K = D.supportUnion μ` (`fbfb4_retained_le_restrict_supportUnion`). The premise `hpack`, applied
to the original `μ`, this closed `K`, `R₀ = 1`, `C_K = C` and the content field
`hD.content.finite_packing`, gives `(μ⌊K)(P(0,1)) ≤ 5^k C A`. No absolute continuity is used. -/
theorem fbgrowth_unit_ball_le_proof (hpack : PackingMassStatement) {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) (C M A : ℝ) (hC : 0 < C) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (D : RetainedSets n) (hD : IsRectifiabilityDecomposition k C M 0 μ D)
    (hdens : ∀ᵐ z ∂μ, lowerDensity μ k z ≤ ENNReal.ofReal A) :
    μ (Metric.ball (point 0 0) 1) ≤ ENNReal.ofReal (C * M + 5 ^ k * C * A) := by
  have hBm : MeasurableSet (Metric.ball (point 0 0 : Space n) 1) := measurableSet_ball
  have hsplit : μ (Metric.ball (point 0 0) 1) =
      (D.remainderMeasure μ + D.horizontalMeasure μ + D.verticalMeasure μ)
        (Metric.ball (point 0 0) 1) :=
    congrArg (fun ν : Measure (Space n) => ν (Metric.ball (point 0 0) 1)) hD.measure_eq
  have hP : μ.restrict (D.supportUnion μ) (Metric.ball (point 0 0) 1) ≤
      ENNReal.ofReal (5 ^ k * C * A * 1 ^ k) :=
    hpack n hn k hk hkn (D.supportUnion μ) (fbfb4_measurableSet_supportUnion μ D) 1 C one_pos
      hC.le hD.content.finite_packing μ hμ hreg A hA (hdens.mono fun _ hz _ => hz)
      (point 0 0) 1 one_pos le_rfl
  have hret := fbfb4_retained_le_restrict_supportUnion μ D hBm
  have h5 : 0 ≤ 5 ^ k * C * A :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hC.le) hA
  calc μ (Metric.ball (point 0 0) 1)
      = D.remainderMeasure μ (Metric.ball (point 0 0) 1) +
          (D.horizontalMeasure μ (Metric.ball (point 0 0) 1) +
            D.verticalMeasure μ (Metric.ball (point 0 0) 1)) := by
        rw [hsplit, Measure.add_apply, Measure.add_apply, add_assoc]
    _ ≤ ENNReal.ofReal (C * M + 0) + ENNReal.ofReal (5 ^ k * C * A * 1 ^ k) :=
        add_le_add hD.remainder_bound (hret.trans hP)
    _ = ENNReal.ofReal (C * M + 5 ^ k * C * A) := by
        rw [add_zero, one_pow, mul_one, ← ENNReal.ofReal_add (mul_nonneg hC.le hM) h5]

end ParabolicRectifiability.Foundations
