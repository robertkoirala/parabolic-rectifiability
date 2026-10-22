import ParabolicRectifiability.Enhancements.Assembly.ScalingRates
import ParabolicRectifiability.Enhancements.Assembly.ScaledCoreTransport

/-! # The scaled threshold without graph-domain covers

Main theorem:

`scaled_rectifiable_reifenberg_core_of_providers : RectifiableReifenbergTheoremStatement →
  SquareEnergyRescalingStatement → ScaledRectifiableReifenbergCoreStatement`.

Proof assembly, the same as that of `scaled_and_ambient_of_graphEnhanced` with the unit graph
enhancement replaced by the parabolic rectifiable Reifenberg theorem:

* the scaling identities are `scaling_identities_of_providers` (using
  `betaSq_rescaledSource` and the energy identity at endpoint `2`);
* apply the parabolic rectifiable Reifenberg theorem (mixed or fixed-family clause; consumed as the hypothesis
  `RectifiableReifenbergTheoremStatement`) to `ν = R^{-k} (F^{-1})_# μ` (locally Radon by the helper
  lemmas) with allowance `R^{-k} Γ`, the threshold being transported by the energy identity
  (`rescaledSource_threshold`);
* pull back by `isLocalCoreDecomposition_of_rescaledSource`, a pure similarity-covariance
  statement;
* the loss is `R^k ν⁺(P(0,1)) ≤ R^k (C M + R^{-k} Γ) = C M R^k + Γ` (coefficient one on `Γ`).

The hypotheses are `RectifiableReifenbergTheoremStatement` (the parabolic rectifiable Reifenberg theorem) and
`SquareEnergyRescalingStatement` (the energy identity under rescaling). The second one
is required by the scaling-identity conjunct and by the threshold transport.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-- An enhanced local decomposition is in particular a local decomposition without
graph-domain covers: forget the field `graph_domains`. -/
theorem IsLocalEnhancedDecomposition.toCore {n k : ℕ} {T : FamilyKind} {C : ℝ}
    {a : Space n} {R : ℝ} {μ : Measure (Space n)} {EH EV : Set (Space n)}
    (h : IsLocalEnhancedDecomposition k T C a R μ EH EV) :
    IsLocalCoreDecomposition k T C a R μ EH EV where
  measurable_horizontal := h.measurable_horizontal
  measurable_vertical := h.measurable_vertical
  disjoint := h.disjoint
  horizontal_subset := h.horizontal_subset
  vertical_subset := h.vertical_subset
  measure_eq := h.measure_eq
  horizontal_unavailable := h.horizontal_unavailable
  vertical_unavailable := h.vertical_unavailable
  horizontal_only := h.horizontal_only
  vertical_only := h.vertical_only
  supports := h.supports

/-- The scaled threshold property without graph-domain covers, from the parabolic rectifiable Reifenberg theorem, with the
same constant `C`. The pull-back is `isLocalCoreDecomposition_of_rescaledSource`. -/
theorem scaledThresholdCoreProperty_of_rectifiableReifenberg (hER : SquareEnergyRescalingStatement)
    (hMT1 : RectifiableReifenbergTheoremStatement) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ScaledThresholdCoreProperty n C := by
  obtain ⟨C, hC, hmix, hfix, -⟩ := hMT1 n hn
  refine ⟨C, hC, ?_⟩
  intro k hk hkn μ hμ hreg a R hR T hT M Γ hM hΓ hbad
  have hνc := isFiniteMeasureOnCompacts_rescaledSource μ hμ k a R hR
  have hνr := innerRegular_rescaledSource μ hreg k a R hR
  have hΓ' : 0 ≤ Γ / R ^ k := div_nonneg hΓ (pow_nonneg hR.le k)
  have hbadν := rescaledSource_threshold hER hn hk hkn μ a R hR T M Γ hbad
  obtain ⟨D, hD, hH, hV⟩ : ∃ D : RetainedSets n,
      IsRectifiableReifenbergDecomposition k C M (Γ / R ^ k) (rescaledSource μ k a R hR) D ∧
      (T = .horizontal → D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.verticalSupport (rescaledSource μ k a R hR) = ∅) ∧
      (T = .vertical → D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.horizontalSupport (rescaledSource μ k a R hR) = ∅) := by
    cases T with
    | mixed =>
      obtain ⟨D, hD⟩ := hmix k hk hkn _ hνc hνr M _ hM hΓ' hbadν
      exact ⟨D, hD, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    | horizontal => exact hfix k hk hkn _ (by decide) hT _ hνc hνr M _ hM hΓ' hbadν
    | vertical => exact hfix k hk hkn _ (by decide) hT _ hνc hνr M _ hM hΓ' hbadν
  obtain ⟨hloc, hloss⟩ := isLocalCoreDecomposition_of_rescaledSource hn hk hkn μ hμ hreg
    a R hR T C D hD.horizontal_unavailable hD.vertical_unavailable hH hV hD.supports
  refine ⟨_, _, hloc, ?_⟩
  rw [hloss]
  calc ENNReal.ofReal R ^ k *
        D.remainderMeasure (rescaledSource μ k a R hR) (Metric.ball (point 0 0) 1)
      ≤ ENNReal.ofReal R ^ k * ENNReal.ofReal (C * M + Γ / R ^ k) :=
        mul_le_mul' le_rfl hD.remainder_bound
    _ = ENNReal.ofReal (C * M * R ^ k + Γ) := by
      rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (pow_nonneg hR.le k)]
      congr 1
      have hRk : R ^ k ≠ 0 := (pow_pos hR k).ne'
      field_simp

/-- **Scaled rectifiable Reifenberg theorem without graph-domain covers.** Hypotheses:
`RectifiableReifenbergTheoremStatement` (the parabolic rectifiable Reifenberg theorem) and `SquareEnergyRescalingStatement`. -/
theorem scaled_rectifiable_reifenberg_core_of_providers (hMT1 : RectifiableReifenbergTheoremStatement)
    (hER : SquareEnergyRescalingStatement) : ScaledRectifiableReifenbergCoreStatement :=
  ⟨scaling_identities_of_providers hER,
    fun n hn => scaledThresholdCoreProperty_of_rectifiableReifenberg hER hMT1 n hn⟩

end ParabolicRectifiability.Enhancements
