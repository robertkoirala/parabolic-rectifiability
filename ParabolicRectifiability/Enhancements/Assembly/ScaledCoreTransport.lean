import ParabolicRectifiability.Enhancements.Statements.ScaledCore
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Enhancements.Proofs.Scaling.RescaledCoreDecomposition

/-! # Similarity transport of a unit decomposition, without graph-domain covers

The statement `isLocalCoreDecomposition_of_rescaledSource` is proved by
`ScaledCoreTree.sc2c_isLocalCoreDecomposition_of_rescaledSource`. It is used by
`scaled_rectifiable_reifenberg_core_of_providers` .

It is the statement `isLocalEnhancedDecomposition_of_rescaledSource` with its domain-data part
removed: the hypothesis `hG` (unit graph-domain covers) and the conclusion field
`graph_domains` are dropped, and `IsLocalEnhancedDecomposition` becomes
`IsLocalCoreDecomposition`. The enhanced statement itself cannot be reused, because both its
hypotheses and its conclusion contain graph-domain covers, which the parabolic rectifiable Reifenberg theorem does not
supply.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-- **Similarity transport of a unit decomposition, without domain data.**

Setting: `F(y) = a + δ_R y`, `ν = R^{-k} (F^{-1})_# μ = rescaledSource μ k a R hR`, and
`F^{-1} = similarity a R hR`. Let `D` be unit retained sets for `ν` whose actual supports
satisfy the unit support bundle `HasRegularSupportBounds k C (0) 1` and the unavailable-type
and fixed-family vanishing clauses.

Conclusion: the pulled-back sets `E_T = F(D_T) = (similarity a R hR)⁻¹' D_T` form the
restriction decomposition `IsLocalCoreDecomposition` of `μ` on `P(a,R)` with the **same**
constant `C`, and the loss transforms exactly: `μ⁺(P(a,R)) = R^k ν⁺(P(0,1))`. This is pure
covariance under the parabolic similarity: the pulled-back sets are Borel, disjoint and lie
in `P(a,R)`; restrictions and actual supports are carried by the homeomorphism (and the
positive factor `R^k`), so the vanishing clauses transfer; `H_P^k` and base volumes scale by
`R^k`, ambient volume by `R^{n+2}`, separated nets and packings by the radius factor `R`;
horizontal slopes and the general regular seminorm are invariant under
`G_R(u,t) = R G(u/R, t/R²)`, so the every-tolerance graph covers transfer.

No graph-domain data are assumed or produced. No threshold, energy or regularity
hypothesis on `μ` beyond the stated data is used; the remainder bound of `D` is not an input
(the loss identity is an equality).

It is used by `scaled_rectifiable_reifenberg_core_of_providers`, which supplies `D` from Main
theorem 1 applied to `ν` with threshold allowance `R^{-k} Γ`. -/
theorem isLocalCoreDecomposition_of_rescaledSource {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (a : Space n) (R : ℝ) (hR : 0 < R) (T : FamilyKind) (C : ℝ) (D : RetainedSets n)
    (hunH : ¬ (1 ≤ k ∧ k ≤ n) →
      D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.horizontalSupport (rescaledSource μ k a R hR) = ∅)
    (hunV : ¬ (2 ≤ k ∧ k ≤ n + 2) →
      D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.verticalSupport (rescaledSource μ k a R hR) = ∅)
    (honlyH : T = .horizontal →
      D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.verticalSupport (rescaledSource μ k a R hR) = ∅)
    (honlyV : T = .vertical →
      D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.horizontalSupport (rescaledSource μ k a R hR) = ∅)
    (hS : HasRegularSupportBounds k C (point 0 0) 1
      (D.horizontalSupport (rescaledSource μ k a R hR))
      (D.verticalSupport (rescaledSource μ k a R hR))) :
    IsLocalCoreDecomposition k T C a R μ
        (similarity a R hR ⁻¹' D.horizontal) (similarity a R hR ⁻¹' D.vertical) ∧
      μ.restrict (similarity a R hR ⁻¹' D.horizontal ∪ similarity a R hR ⁻¹' D.vertical)ᶜ
          (Metric.ball a R) =
        ENNReal.ofReal R ^ k *
          D.remainderMeasure (rescaledSource μ k a R hR) (Metric.ball (point 0 0) 1) := by
  exact ScaledCoreTree.sc2c_isLocalCoreDecomposition_of_rescaledSource hn hk hkn μ hμ hreg a R hR T C D
    hunH hunV honlyH honlyV hS

end ParabolicRectifiability.Enhancements
