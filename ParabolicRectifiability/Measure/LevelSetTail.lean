import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Continuity

/-! # Small superlevel tails on a set of finite measure

For an almost everywhere finite nonnegative measurable function, its integer
superlevel sets decrease to a null set. Continuity of measure from above makes
their intersections with any measurable set of finite measure arbitrarily small.
This is the common level-selection step used by compact exhaustion and the gauge
series construction.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability

/-- An integer superlevel tail has arbitrarily small measure inside a measurable
set of finite measure when the function is finite almost everywhere. -/
theorem exists_nat_measure_inter_superlevel_lt {X : Type*} [MeasurableSpace X] (μ : Measure X) {S : X → ℝ≥0∞}
    (hS : Measurable S) (hfin : ∀ᵐ z ∂μ, S z < ⊤) {B : Set X} (hBm : MeasurableSet B)
    (hB : μ B ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ a : ℕ, μ (B ∩ {z | (a : ℝ≥0∞) < S z}) < ε := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Set X, D = fun m : ℕ => B ∩ {z | (m : ℝ≥0∞) < S z} := ⟨_, rfl⟩
  have hDm : ∀ m, MeasurableSet (D m) := fun m => by
    subst hD; exact hBm.inter (measurableSet_lt measurable_const hS)
  have hanti : Antitone D := by
    subst hD
    intro i j hij z hz
    exact ⟨hz.1, show (i : ℝ≥0∞) < S z from (Nat.cast_le.2 hij).trans_lt
      (show (j : ℝ≥0∞) < S z from hz.2)⟩
  have hD0 : μ (D 0) ≠ ⊤ := by
    subst hD; exact ne_top_of_le_ne_top hB (measure_mono inter_subset_left)
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun m => (hDm m).nullMeasurableSet)
    hanti ⟨0, hD0⟩
  have hzero : μ (⋂ m, D m) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hfin)
    rw [mem_iInter] at hz
    show ¬ S z < ⊤
    intro hlt
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hlt.ne
    have hzm : z ∈ D m := hz m
    rw [hD] at hzm
    exact lt_asymm hzm.2 hm
  rw [hzero] at hlim
  obtain ⟨a, ha⟩ := ((tendsto_order.1 hlim).2 ε (pos_iff_ne_zero.2 hε)).exists
  refine ⟨a, ?_⟩
  have h : (μ ∘ D) a = μ (B ∩ {z | (a : ℝ≥0∞) < S z}) := by subst hD; rfl
  rw [← h]
  exact ha

end ParabolicRectifiability
