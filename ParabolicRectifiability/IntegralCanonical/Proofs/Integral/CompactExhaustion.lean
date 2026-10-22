import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements
import ParabolicRectifiability.Measure.LevelSetTail

/-! # Compact exhaustion

Proof of `i2_CompactExhaustionStatement`, the auxiliary statement `i2_compactExhaustion`.

Route, with `ε_j = j⁻¹` in place of `2^{-j}`:
1. `B_j = P(0,j)`, the open ball of radius `j` about `point 0 0`; `μ(B_j) < ∞`.
2. A level `a_j ∈ ℕ` with `μ(B_j ∩ {S > a_j}) < ε_j / 2`: continuity from above of
   `m ↦ μ(B_j ∩ {S > m})` (`tendsto_measure_iInter_atTop`), whose intersection lies in the
   `μ`-null set `{S = ∞}` (`i2_exists_level_lt`).
3. A compact `C_j ⊆ B_j ∩ {S ≤ a_j}` with `μ(B_j \ C_j) < ε_j`, by inner regularity
   (`MeasurableSet.exists_isCompact_sdiff_lt`) on the finite-measure Borel set
   `B_j ∩ {S ≤ a_j}` (`i2_exists_compact_level`).
4. `K_j = ⋃_{i ≤ j} C_i`: compact (finite union) and increasing.
5. `∫_{K_j} S dμ ≤ (∑_{i ≤ j} a_i) μ(K_j) < ∞`.
6. For each `N` and `j ≥ N`, `μ(B_N \ ⋃ K) ≤ μ(B_j \ C_j) < j⁻¹`, so `μ(B_N \ ⋃ K) = 0`; the
   balls `B_N` cover the space, and `measure_iUnion_null` gives `μ((⋃ K)ᶜ) = 0`.

The energy source stays `μ`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- Step 2 (continuity from above). If `S < ∞` almost everywhere and `B` is Borel of finite
measure, then for every `ε ≠ 0` some integer level `a` has `μ(B ∩ {S > a}) < ε`. -/
theorem i2_exists_level_lt {X : Type*} [MeasurableSpace X] (μ : Measure X) {S : X → ℝ≥0∞}
    (hS : Measurable S) (hfin : ∀ᵐ z ∂μ, S z < ⊤) {B : Set X} (hBm : MeasurableSet B)
    (hB : μ B ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ a : ℕ, μ (B ∩ {z | (a : ℝ≥0∞) < S z}) < ε := by
  exact ParabolicRectifiability.exists_nat_measure_inter_superlevel_lt μ hS hfin hBm hB hε

/-- Step 3 (inner regularity). Under the hypotheses of `i2_exists_level_lt`, for an inner
regular `μ` there are an integer level `a` and a compact `C ⊆ B` with `S ≤ a` on `C` and
`μ(B \ C) < ε`. -/
theorem i2_exists_compact_level {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] (μ : Measure X) [μ.InnerRegularCompactLTTop]
    {S : X → ℝ≥0∞} (hS : Measurable S) (hfin : ∀ᵐ z ∂μ, S z < ⊤) {B : Set X}
    (hBm : MeasurableSet B) (hB : μ B ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (a : ℕ) (C : Set X), C ⊆ B ∧ IsCompact C ∧ (∀ z ∈ C, S z ≤ a) ∧ μ (B \ C) < ε := by
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨a, ha⟩ := i2_exists_level_lt μ hS hfin hBm hB hε2
  have hFm : MeasurableSet (B ∩ {z | S z ≤ (a : ℝ≥0∞)}) :=
    hBm.inter (measurableSet_le hS measurable_const)
  have hF : μ (B ∩ {z | S z ≤ (a : ℝ≥0∞)}) ≠ ⊤ :=
    ne_top_of_le_ne_top hB (measure_mono inter_subset_left)
  obtain ⟨C, hCF, hCc, hC⟩ := hFm.exists_isCompact_sdiff_lt hF hε2
  refine ⟨a, C, fun z hz => (hCF hz).1, hCc, fun z hz => (hCF hz).2, ?_⟩
  calc μ (B \ C)
      ≤ μ (B ∩ {z | (a : ℝ≥0∞) < S z} ∪ (B ∩ {z | S z ≤ (a : ℝ≥0∞)}) \ C) := by
        refine measure_mono fun z hz => ?_
        by_cases h : S z ≤ (a : ℝ≥0∞)
        · exact Or.inr ⟨⟨hz.1, h⟩, hz.2⟩
        · exact Or.inl ⟨hz.1, not_le.1 h⟩
    _ ≤ μ (B ∩ {z | (a : ℝ≥0∞) < S z}) + μ ((B ∩ {z | S z ≤ (a : ℝ≥0∞)}) \ C) :=
        measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add ha hC
    _ = ε := ENNReal.add_halves ε

/-- **Compact exhaustion** (`i2_compactExhaustion`). -/
theorem i2_compactExhaustion_proof : i2_CompactExhaustionStatement := by
  intro n _ k _ _ μ hμ hreg T _ R _ hfin
  have := hμ
  have := hreg
  have hS : Measurable (squareEnergy μ k T R) := measurable_squareEnergy μ k T R
  -- Step 1: the balls `B_j = P(0,j)`.
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Set (Space n), B = fun j : ℕ => Metric.ball (point 0 0) (j : ℝ) :=
    ⟨_, rfl⟩
  have hBm : ∀ j, MeasurableSet (B j) := fun j => by subst hB; exact measurableSet_ball
  have hBf : ∀ j, μ (B j) ≠ ⊤ := fun j => by subst hB; exact Metric.isBounded_ball.measure_lt_top.ne
  have hBmono : Monotone B := fun i j hij => by
    subst hB; exact Metric.ball_subset_ball (Nat.cast_le.2 hij)
  have hBcov : ∀ z, ∃ N, z ∈ B N := fun z => by
    subst hB
    obtain ⟨N, hN⟩ := exists_nat_gt (dist z (point 0 0))
    exact ⟨N, hN⟩
  -- Steps 2-3: levels `a_j` and compacts `C_j`, with `ε_j = j⁻¹`.
  have hε : ∀ j : ℕ, (j : ℝ≥0∞)⁻¹ ≠ 0 := fun j => ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top j)
  choose a C _ hCc hCa hCμ using fun j => i2_exists_compact_level μ hS hfin (hBm j) (hBf j) (hε j)
  -- Step 4: `K_j = ⋃_{i ≤ j} C_i`.
  obtain ⟨K, hK⟩ : ∃ K : ℕ → Set (Space n), K = fun j => ⋃ i ∈ Finset.range (j + 1), C i :=
    ⟨_, rfl⟩
  have hmemK : ∀ j z, z ∈ K j ↔ ∃ i, i ≤ j ∧ z ∈ C i := fun j z => by
    subst hK; simp
  have hKc : ∀ j, IsCompact (K j) := fun j => by
    subst hK; exact Finset.isCompact_biUnion _ fun i _ => hCc i
  refine ⟨K, hKc, ?_, ?_, ?_⟩
  · intro i j hij z hz
    obtain ⟨l, hl, hzl⟩ := (hmemK i z).1 hz
    exact (hmemK j z).2 ⟨l, hl.trans hij, hzl⟩
  · -- Step 6: `μ(B_N \ ⋃ K) = 0` for every `N`, and the balls cover.
    have hcov : (⋃ j, K j)ᶜ ⊆ ⋃ N, B N ∩ (⋃ j, K j)ᶜ := fun z hz => by
      obtain ⟨N, hN⟩ := hBcov z
      exact mem_iUnion.2 ⟨N, hN, hz⟩
    refine measure_mono_null hcov (measure_iUnion_null fun N => ?_)
    refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hε0 _ => ?_)
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (ENNReal.coe_ne_zero.2 hε0.ne')
    calc μ (B N ∩ (⋃ j, K j)ᶜ)
        ≤ μ (B (max m N) \ C (max m N)) := by
          refine measure_mono fun z hz => ⟨hBmono (le_max_right m N) hz.1, fun hzC => hz.2 ?_⟩
          exact mem_iUnion.2 ⟨max m N, (hmemK _ z).2 ⟨max m N, le_rfl, hzC⟩⟩
      _ ≤ ((max m N : ℕ) : ℝ≥0∞)⁻¹ := (hCμ _).le
      _ ≤ (m : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 (Nat.cast_le.2 (le_max_left m N))
      _ ≤ 0 + ε := by rw [zero_add]; exact hm.le
  · -- Step 5: `∫_{K_j} S dμ ≤ (∑_{i ≤ j} a_i) μ(K_j) < ∞`.
    intro j
    calc ∫⁻ z in K j, squareEnergy μ k T R z ∂μ
        ≤ ∫⁻ _ in K j, (((∑ i ∈ Finset.range (j + 1), a i : ℕ)) : ℝ≥0∞) ∂μ := by
          refine setLIntegral_mono' (hKc j).measurableSet fun z hz => ?_
          obtain ⟨i, hi, hzi⟩ := (hmemK j z).1 hz
          refine (hCa i z hzi).trans (Nat.cast_le.2 ?_)
          exact Finset.single_le_sum (fun l _ => Nat.zero_le (a l))
            (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      _ = (((∑ i ∈ Finset.range (j + 1), a i : ℕ)) : ℝ≥0∞) * μ (K j) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (hKc j).measure_lt_top

end ParabolicRectifiability.IntegralCanonical
