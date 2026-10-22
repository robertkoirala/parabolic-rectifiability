import ParabolicRectifiability.Decomposition.Local
import ParabolicRectifiability.Measure.BetaTail
import ParabolicRectifiability.Decomposition.ZeroEnergyPlane
import ParabolicRectifiability.Decomposition.ZeroThresholdAssembly

/-! # Loss-free zero threshold and the ambient endpoint

The zero-threshold branch `zero_threshold_family_decomposition` and the ambient
case `ambient_retained_decomposition` of the decomposition theorem. These branches do
not use the positive-threshold density refinement: at zero threshold each localized
source lies in one attained admissible model (`exists_model_containing_support_of_zero_energy`)
and is retained in full (`exists_flat_assembly_constant`); at ambient dimension the
retained sets `ambientRetainedSets` are explicit.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-- Zero all-scale energy forces the actual compact localized support into an
attained admissible plane. This includes the zero source by family availability. -/
theorem exists_model_containing_support_of_zero_energy {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n + 2) (T : FamilyKind)
    (hT : Nonempty (Models n k T)) (ν : Measure (Space n))
    (hν : IsFiniteMeasure ν) (hreg : ν.InnerRegular)
    (c : Space n) (hc : ν.support ⊆ Metric.closedBall c (1 / 64))
    (henergy : ∀ᵐ z ∂ν, allScaleEnergy ν k T z ≤ 0) :
    ∃ L : Models n k T, ν.support ⊆ modelSet L := by
  exact modelContainingSupport_of_zeroEnergy hk hkn T hT ν hν hreg c hc henergy

/-- Finite unions of the attained flat supports, grouped by their actual type.
All localized source mass is retained, so the only remainder cost is `Γ`. -/
theorem exists_flat_assembly_constant (n : ℕ) (hn : 1 ≤ n) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ Γ : ℝ, 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | 0 < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      ∀ S : GoodSourceLocalization μ k T 0 N,
      (∀ i, ∃ L : Models n k T, (μ.restrict (S.region i)).support ⊆ modelSet L) →
      HasFamilyDecomposition k T C 0 Γ μ := by
  exact flatAssemblyConstant_proof n hn N

/-- The zero-threshold branch uses no limiting positive-density argument. -/
theorem zero_threshold_family_decomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ Γ : ℝ, 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | 0 < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      HasFamilyDecomposition k T C 0 Γ μ := by
  classical
  obtain ⟨N, _, hloc⟩ := exists_good_source_localization n hn
  obtain ⟨C, hC, hflat⟩ := exists_flat_assembly_constant n hn N
  refine ⟨C, hC, ?_⟩
  intro k hk hkn T hT μ hμ hreg Γ hΓ hbad
  let S := Classical.choice (hloc k hk hkn T hT μ hμ hreg 0 le_rfl)
  apply hflat k hk hkn T hT μ hμ hreg Γ hΓ hbad S
  intro i
  apply exists_model_containing_support_of_zero_energy hk hkn T hT _
    (S.finite i) (S.innerRegular i) (S.center i) (S.support_small i)
  simpa only [mul_zero, ENNReal.ofReal_zero] using S.energy i

/-- At ambient dimension retain the whole original source inside the unit ball. -/
def ambientRetainedSets (n : ℕ) : RetainedSets n where
  horizontal := ∅
  vertical := Metric.ball (point 0 0) 1
  measurable_horizontal := MeasurableSet.empty
  measurable_vertical := measurableSet_ball
  disjoint := by simp
  horizontal_subset := empty_subset _
  vertical_subset := Subset.rfl

/-- The ambient case, by volume comparison and the full graph of the zero
function. No beta or energy hypothesis
appears. The specified retained sets have exactly zero unit-ball remainder. -/
theorem ambient_retained_decomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : Measure (Space n),
      IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      IsRectifiabilityDecomposition (n + 2) C 0 0 μ (ambientRetainedSets n) ∧
      (ambientRetainedSets n).remainderMeasure μ (Metric.ball (point 0 0) 1) = 0 := by
  exact ambientRetainedDecomposition_proof n hn

end ParabolicRectifiability
