import ParabolicRectifiability.QuantitativeCharacterization.Statements.ApproximantComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.MultiplicityBasics

/-! # The limits of the approximants and of the residual

Proof of `dp2_approximant_limits : dp2_ApproximantLimitsStatement`.

Write `m = 𝒞.multiplicity`, `H_N = {m ≤ N}`, `P₀ = P(a,R)`.

1. Monotonicity: `𝒞.approximant F N = μ⌊(F ∩ H_N)`, and `F ∩ H_N ⊆ F ∩ H_{N+1}`
   (`Measure.restrict_mono`); likewise for the residuals `μ⌊(P₀ ∩ {m > N})`.
2. Convergence: for a Borel `S`, `Measure.restrict_apply` gives
   `𝒞.approximant F N S = μ (S ∩ (F ∩ H_N))`. These sets increase (continuity from below needs no
   measurability, `tendsto_measure_iUnion_atTop`) with union inside `S ∩ F` and a.e. equal to it,
   since `F ⊆ P₀` and `m < ∞` a.e. on `P₀`. So the limit is `μ (S ∩ F) = μ⌊F S`. `F` need not be
   measurable; `H_N` and `S` are Borel (`dp2_measurableSet_multiplicity_le`).
3. Residual mass: `𝒞.residual N univ = μ (P₀ ∩ {m > N})` decreases, the first term is finite
   (`measure_ball_lt_top`), the sets are Borel (`dp2_measurableSet_lt_multiplicity`), so
   `tendsto_measure_iInter_atTop` gives the limit `μ (⋂_N P₀ ∩ {m > N})`, which is `0` since the
   intersection lies in `P₀ ∩ {m = ∞}`, a null set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- A finite multiplicity is bounded by a natural number. -/
theorem dp2_al_exists_le {m : ℕ∞} (h : m < ⊤) : ∃ N : ℕ, m ≤ (N : ℕ∞) := by
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 h.ne
  exact ⟨N, le_of_eq hN.symm⟩

/-- Proof of `dp2_approximant_limits`. -/
theorem dp2_approximant_limits_proof : dp2_ApproximantLimitsStatement := by
  intro n k K L μ a R 𝒞 hμ hae
  have : IsFiniteMeasureOnCompacts μ := hμ
  refine ⟨fun F hF => ⟨?_, ?_⟩, ?_, ?_⟩
  · -- the approximants increase
    intro N M hNM
    refine Measure.restrict_mono (inter_subset_inter_right _ ?_) le_rfl
    intro z hz
    exact le_trans (show 𝒞.multiplicity z ≤ (N : ℕ∞) from hz) (Nat.cast_le.2 hNM)
  · -- convergence on Borel sets
    intro S hS
    set A : ℕ → Set (Space n) := fun N => S ∩ (F ∩ {z | 𝒞.multiplicity z ≤ (N : ℕ∞)}) with hA
    have hmono : Monotone A := by
      intro N M hNM z hz
      exact ⟨hz.1, hz.2.1, le_trans (show 𝒞.multiplicity z ≤ (N : ℕ∞) from hz.2.2)
        (Nat.cast_le.2 hNM)⟩
    have hform : ∀ N, 𝒞.approximant F N S = μ (A N) := fun N =>
      Measure.restrict_apply hS
    have hunion : μ (⋃ N, A N) = μ (S ∩ F) := by
      refine le_antisymm (measure_mono ?_) ?_
      · exact iUnion_subset fun N z hz => ⟨hz.1, hz.2.1⟩
      · refine measure_mono_ae ?_
        filter_upwards [hae] with z hz hzSF
        obtain ⟨N, hN⟩ := dp2_al_exists_le (hz (hF hzSF.2))
        exact mem_iUnion.2 ⟨N, hzSF.1, hzSF.2, hN⟩
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at hlim
    simp only [hform]
    rw [Measure.restrict_apply hS]
    exact hlim
  · -- the residuals decrease
    intro N M hNM
    refine Measure.restrict_mono (inter_subset_inter_right _ ?_) le_rfl
    intro z hz
    exact lt_of_le_of_lt (Nat.cast_le.2 hNM) (show (M : ℕ∞) < 𝒞.multiplicity z from hz)
  · -- the residual mass tends to zero
    set B : ℕ → Set (Space n) :=
      fun N => Metric.ball a R ∩ {z | (N : ℕ∞) < 𝒞.multiplicity z} with hB
    have hBmeas : ∀ N, NullMeasurableSet (B N) μ := fun N =>
      (measurableSet_ball.inter (dp2_measurableSet_lt_multiplicity 𝒞 N)).nullMeasurableSet
    have hBanti : Antitone B := by
      intro N M hNM z hz
      exact ⟨hz.1, lt_of_le_of_lt (Nat.cast_le.2 hNM)
        (show (M : ℕ∞) < 𝒞.multiplicity z from hz.2)⟩
    have hfin : ∃ N, μ (B N) ≠ ⊤ :=
      ⟨0, ne_top_of_le_ne_top (MeasureTheory.measure_ball_lt_top (μ := μ) (x := a) (r := R)).ne
        (measure_mono inter_subset_left)⟩
    have hlim := tendsto_measure_iInter_atTop hBmeas hBanti hfin
    have hnull : μ (⋂ N, B N) = 0 := by
      refine nonpos_iff_eq_zero.1 ((measure_mono_ae (t := (∅ : Set (Space n))) ?_).trans
        (by simp))
      filter_upwards [hae] with z hz hzI
      have hzB := mem_iInter.1 hzI
      obtain ⟨N, hN⟩ := dp2_al_exists_le (hz (hzB 0).1)
      exact absurd (lt_of_lt_of_le (hzB N).2 hN) (lt_irrefl _)
    rw [hnull] at hlim
    have hform : ∀ N, 𝒞.residual N Set.univ = μ (B N) := fun N =>
      Measure.restrict_apply_univ _
    simp only [hform]
    exact hlim

end ParabolicRectifiability.QuantitativeCharacterization
