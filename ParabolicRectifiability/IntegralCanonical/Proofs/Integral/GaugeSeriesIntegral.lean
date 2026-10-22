import ParabolicRectifiability.IntegralCanonical.Proofs.Integral.IntegralAuxiliaryStatements
import ParabolicRectifiability.Measure.LevelSetTail

/-! # The gauge-series integral

Proof of `i2_GaugeSeriesIntegralStatement`, the auxiliary statement `i2_gaugeSeries_integral`.

Route, with the thresholds decoupled from the gauge sequence:
1. Levels `a_j ∈ ℕ` with `μ(A ∩ {S > a_j}) < 2^{-j}`: continuity from above of
   `m ↦ μ(A ∩ {S > m})` on the finite-measure set `A`, whose intersection lies in the `μ`-null
   set `{S = ∞}` (`i2_gi_exists_level_lt`).
2. `t_j = 2^j (a_j + 1)`, so `t_j > 0`, `t_j⁻¹ ≤ 2^{-j}` (summable), and `a_j / t_j ≤ 2^{-j}`.
   (The split is made at the level `a_j` itself; only positivity and summable reciprocals of
   the `t_j` are used downstream.)
3. Off the null set `{S = ∞}`, `extendedGauge Φ_t (S) = Σ_j ofReal(min{1, S/t_j})`
   (`ENNReal.ofReal_tsum_of_nonneg`), and termwise
   `ofReal(min{1, S/t_j}) ≤ 1_{S > a_j} + 2^{-j}` (`i2_gi_pointwise`).
4. `lintegral_tsum`: `∫_A Φ_t(S) ≤ Σ_j (μ(A ∩ {S > a_j}) + 2^{-j} μ(A)) ≤ Σ_j 2^{-j}(1 + μ(A))`,
   a geometric series times the finite factor `1 + μ(A)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations

/-- Step 1 (continuity from above). If `S < ∞` almost everywhere and `B` is Borel of finite
measure, then for every `ε ≠ 0` some integer level `a` has `μ(B ∩ {S > a}) < ε`. -/
theorem i2_gi_exists_level_lt {X : Type*} [MeasurableSpace X] (μ : Measure X) {S : X → ℝ≥0∞}
    (hS : Measurable S) (hfin : ∀ᵐ z ∂μ, S z < ⊤) {B : Set X} (hBm : MeasurableSet B)
    (hB : μ B ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ a : ℕ, μ (B ∩ {z | (a : ℝ≥0∞) < S z}) < ε := by
  exact ParabolicRectifiability.exists_nat_measure_inter_superlevel_lt μ hS hfin hBm hB hε

/-- Step 3 (pointwise bound). For `t_j = 2^j (a_j + 1)` with summable reciprocals and a finite
value `x`, `extendedGauge Φ_t x = Σ_j ofReal(min{1, x/t_j}) ≤ Σ_j (1_{x > a_j} + 2^{-j})`. -/
theorem i2_gi_pointwise (a : ℕ → ℕ) (t : ℕ → ℝ) (ht : ∀ j, t j = 2 ^ j * ((a j : ℝ) + 1))
    (hinv : Summable fun j => (t j)⁻¹) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    extendedGauge (i2_gaugeSeries t) x ≤
      ∑' j, ({y : ℝ≥0∞ | (a j : ℝ≥0∞) < y}.indicator 1 x +
        ENNReal.ofReal ((2⁻¹ : ℝ) ^ j)) := by
  have htpos : ∀ j, 0 < t j := fun j => by rw [ht j]; positivity
  have hu : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hnn : ∀ j, 0 ≤ min 1 (x.toReal / t j) := fun j =>
    le_min zero_le_one (div_nonneg hu (htpos j).le)
  have hsum : Summable fun j => min 1 (x.toReal / t j) := by
    refine Summable.of_nonneg_of_le hnn (fun j => min_le_right _ _) ?_
    simpa only [div_eq_mul_inv] using hinv.mul_left x.toReal
  unfold extendedGauge i2_gaugeSeries
  rw [ite_eq_right hx, ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  refine ENNReal.tsum_le_tsum fun j => ?_
  by_cases h : (a j : ℝ≥0∞) < x
  · have h1 : {y : ℝ≥0∞ | (a j : ℝ≥0∞) < y}.indicator (1 : ℝ≥0∞ → ℝ≥0∞) x = 1 :=
      indicator_of_mem (show x ∈ {y : ℝ≥0∞ | (a j : ℝ≥0∞) < y} from h) _
    rw [h1]
    calc ENNReal.ofReal (min 1 (x.toReal / t j)) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = 1 := ENNReal.ofReal_one
      _ ≤ 1 + ENNReal.ofReal ((2⁻¹ : ℝ) ^ j) := le_self_add
  · have h0 : {y : ℝ≥0∞ | (a j : ℝ≥0∞) < y}.indicator (1 : ℝ≥0∞ → ℝ≥0∞) x = 0 :=
      indicator_of_notMem (show x ∉ {y : ℝ≥0∞ | (a j : ℝ≥0∞) < y} from h) _
    rw [h0, zero_add]
    refine ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans ?_)
    have hua : x.toReal ≤ (a j : ℝ) := by
      have := ENNReal.toReal_mono (ENNReal.natCast_ne_top (a j)) (not_lt.1 h)
      simpa using this
    rw [div_le_iff₀ (htpos j), ht j, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero,
      one_pow, one_mul]
    linarith

/-- The main estimate on a general measure space: `S` Borel, `S < ∞` almost everywhere, `A` Borel of
finite measure. -/
theorem i2_gi_main {X : Type*} [MeasurableSpace X] (μ : Measure X) {S : X → ℝ≥0∞}
    (hS : Measurable S) (hfin : ∀ᵐ z ∂μ, S z < ⊤) {A : Set X} (hA : MeasurableSet A)
    (hAf : μ A ≠ ⊤) :
    ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧ Summable (fun j => (t j)⁻¹) ∧
      ∫⁻ z in A, extendedGauge (i2_gaugeSeries t) (S z) ∂μ < ⊤ := by
  have hc : ∀ j : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ j) ≠ 0 := fun j =>
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  choose a ha using fun j => i2_gi_exists_level_lt μ hS hfin hA hAf (hc j)
  have hgeo : Summable fun j : ℕ => (2⁻¹ : ℝ) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun j => 2 ^ j * ((a j : ℝ) + 1) := ⟨_, rfl⟩
  have ht' : ∀ j, t j = 2 ^ j * ((a j : ℝ) + 1) := fun j => by rw [ht]
  have hinv : Summable fun j => (t j)⁻¹ := by
    refine Summable.of_nonneg_of_le (fun j => by rw [ht' j]; positivity) (fun j => ?_) hgeo
    rw [ht' j, inv_pow, mul_inv]
    have h1 : (1 : ℝ) ≤ (a j : ℝ) + 1 := by linarith [(Nat.cast_nonneg (a j) : (0 : ℝ) ≤ a j)]
    exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ h1)
  refine ⟨t, fun j => by rw [ht' j]; positivity, hinv, ?_⟩
  -- the termwise majorants `B_j(z) = 1_{S z > a_j} + 2^{-j}`
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set X, E = fun j => {z | (a j : ℝ≥0∞) < S z} := ⟨_, rfl⟩
  have hEm : ∀ j, MeasurableSet (E j) := fun j => by
    rw [hE]; exact measurableSet_lt measurable_const hS
  have hEind : ∀ j z, {y : ℝ≥0∞ | (a j : ℝ≥0∞) < y}.indicator (1 : ℝ≥0∞ → ℝ≥0∞) (S z) =
      (E j).indicator 1 z := fun j z => by
    subst hE; rfl
  have hBm : ∀ j, Measurable fun z =>
      (E j).indicator (1 : X → ℝ≥0∞) z + ENNReal.ofReal ((2⁻¹ : ℝ) ^ j) := fun j =>
    (measurable_one.indicator (hEm j)).add measurable_const
  have hcsum : ∑' j : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ j) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hgeo]
    exact ENNReal.ofReal_lt_top
  calc ∫⁻ z in A, extendedGauge (i2_gaugeSeries t) (S z) ∂μ
      ≤ ∫⁻ z in A, ∑' j, ((E j).indicator (1 : X → ℝ≥0∞) z +
          ENNReal.ofReal ((2⁻¹ : ℝ) ^ j)) ∂μ := by
        refine lintegral_mono_ae ((ae_restrict_of_ae hfin).mono fun z hz => ?_)
        have hp := i2_gi_pointwise a t ht' hinv hz.ne
        simp only [hEind] at hp
        exact hp
    _ = ∑' j, ∫⁻ z in A, ((E j).indicator (1 : X → ℝ≥0∞) z +
          ENNReal.ofReal ((2⁻¹ : ℝ) ^ j)) ∂μ :=
        lintegral_tsum fun j => (hBm j).aemeasurable
    _ ≤ ∑' j : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ j) * (1 + μ A) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one (hEm j),
          setLIntegral_const, Measure.restrict_apply (hEm j), mul_add, mul_one]
        refine add_le_add ?_ le_rfl
        have hj := (ha j).le
        rw [inter_comm] at hj
        rw [hE]
        exact hj
    _ = (∑' j : ℕ, ENNReal.ofReal ((2⁻¹ : ℝ) ^ j)) * (1 + μ A) := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hcsum (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hAf.lt_top⟩)

/-- **Integral of the gauge series** (`i2_gaugeSeries_integral`). -/
theorem i2_gaugeSeries_integral_proof : i2_GaugeSeriesIntegralStatement := by
  intro n _ k _ _ μ hμ hreg T _ R _ hfin A hA hAb
  have := hμ
  have := hreg
  exact i2_gi_main μ (measurable_squareEnergy μ k T R) hfin hA hAb.measure_lt_top.ne

end ParabolicRectifiability.IntegralCanonical
