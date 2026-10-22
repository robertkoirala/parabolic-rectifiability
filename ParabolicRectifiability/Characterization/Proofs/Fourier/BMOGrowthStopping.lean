import Mathlib

/-! # The abstract one-generation stopping argument

Measure-theoretic stopping step used in the proof of `ba1_bmo_growth_proof`.

This file is measure-theoretic and does not mention parabolic space. A nested family of
countable partitions is given by index maps `idx k : α → ι` (cells are the fibres
`b1bmo_cellOf (idx k) z = {w | idx k w = idx k z}`; nestedness says that equal level-`k+1`
indices give equal level-`k` indices). For a nonnegative function `F` and a threshold `lam`, a
point `z` is *good at level `k`* if `∫_{cell k z} F ≤ lam |cell k z|`.

`b1bmo_stopping` is the Calderón-Zygmund stopping step for one generation:
the maximal bad cells below a good root form a measurable set `U` with
`lam |U| ≤ ∫_Q F`, and `∫_Q F² ≤ lam² |Q| + K |U|` provided that `F ≤ lam` almost everywhere at
points good at every level (the dyadic differentiation step) and that every child of a good
cell carries `∫ F² ≤ K |child|`.

The remaining lemmas convert the analytic inputs (averages, parent bounds and
differentiation) into the two hypotheses of `b1bmo_stopping`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ParabolicRectifiability.Characterization

variable {α ι : Type*} [MeasurableSpace α]

/-- The average of a real function over a set (the convention of `standardBallAverage`). -/
def b1bmo_avg (μ : Measure α) (D : Set α) (g : α → ℝ) : ℝ :=
  (μ D).toReal⁻¹ * ∫ x in D, g x ∂μ

/-- The cell of `z` for an index map: the fibre of `f` through `z`. -/
def b1bmo_cellOf (f : α → ι) (z : α) : Set α := {w | f w = f z}

theorem b1bmo_mem_cellOf_self (f : α → ι) (z : α) : z ∈ b1bmo_cellOf f z := rfl

theorem b1bmo_cellOf_eq {f : α → ι} {z w : α} (h : f w = f z) :
    b1bmo_cellOf f w = b1bmo_cellOf f z := by
  ext v
  simp only [b1bmo_cellOf, mem_ofPred_eq, h]

section Countable

variable [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem b1bmo_measurableSet_cellOf {f : α → ι} (hf : Measurable f) (z : α) :
    MeasurableSet (b1bmo_cellOf f z) :=
  hf (measurableSet_singleton (f z))

/-- A set saturated for the fibres of a measurable countable-valued map is measurable. -/
theorem b1bmo_measurableSet_of_saturated {f : α → ι} (hf : Measurable f) {S : Set α}
    (hS : ∀ z ∈ S, ∀ w, f w = f z → w ∈ S) : MeasurableSet S := by
  have hSeq : S = f ⁻¹' (f '' S) := by
    ext w
    constructor
    · intro hw
      exact ⟨w, hw, rfl⟩
    · rintro ⟨z, hz, hzw⟩
      exact hS z hz w hzw.symm
  rw [hSeq]
  exact hf (Set.Countable.measurableSet (Set.to_countable _))

/-- Cellwise comparison of set integrals over a saturated set. -/
theorem b1bmo_setLIntegral_le_of_saturated (μ : Measure α) {f : α → ι} (hf : Measurable f)
    {S : Set α} (hS : ∀ z ∈ S, ∀ w, f w = f z → w ∈ S) {F G : α → ℝ≥0∞}
    (h : ∀ z ∈ S, ∫⁻ w in b1bmo_cellOf f z, F w ∂μ ≤ ∫⁻ w in b1bmo_cellOf f z, G w ∂μ) :
    ∫⁻ w in S, F w ∂μ ≤ ∫⁻ w in S, G w ∂μ := by
  classical
  let T : ι → Set α := fun j => S ∩ f ⁻¹' {j}
  have hpiece : ∀ j, T j = ∅ ∨ ∃ z ∈ S, T j = b1bmo_cellOf f z := by
    intro j
    by_cases hj : (T j).Nonempty
    · obtain ⟨z, hzS, hzj⟩ := hj
      have hzj' : f z = j := hzj
      right
      refine ⟨z, hzS, ?_⟩
      ext w
      simp only [T, b1bmo_cellOf, mem_inter_iff, mem_preimage, mem_singleton_iff,
        mem_ofPred_eq]
      constructor
      · rintro ⟨_, hw⟩
        rw [hw, hzj']
      · intro hw
        exact ⟨hS z hzS w hw, hw.trans hzj'⟩
    · left
      exact not_nonempty_iff_eq_empty.mp hj
  have hmeas : ∀ j, MeasurableSet (T j) := by
    intro j
    rcases hpiece j with h0 | ⟨z, -, hz⟩
    · rw [h0]
      exact MeasurableSet.empty
    · rw [hz]
      exact b1bmo_measurableSet_cellOf hf z
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro w hwi hwj
    exact hij ((show f w = i from hwi.2).symm.trans (show f w = j from hwj.2))
  have hU : S = ⋃ j, T j := by
    ext w
    simp only [T, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun hw => ⟨f w, hw, rfl⟩, fun ⟨_, hw, _⟩ => hw⟩
  rw [hU, lintegral_iUnion hmeas hdisj, lintegral_iUnion hmeas hdisj]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rcases hpiece j with h0 | ⟨z, hz, hTz⟩
  · simp [h0]
  · rw [hTz]
    exact h z hz

/-- Iterated nestedness: equal level-`k` indices give equal level-`i` indices for `i ≤ k`. -/
theorem b1bmo_idx_eq_of_le {idx : ℕ → α → ι}
    (hnest : ∀ k z w, idx (k + 1) w = idx (k + 1) z → idx k w = idx k z)
    {i k : ℕ} (hik : i ≤ k) {z w : α} : idx k w = idx k z → idx i w = idx i z := by
  induction k, hik using Nat.le_induction with
  | base => exact id
  | succ k _ ih => exact fun h => ih (hnest k z w h)

/-- Goodness of the level-`k` cell of `z` for the function `F` and the threshold `lam`. -/
def b1bmo_good (μ : Measure α) (idx : ℕ → α → ι) (F : α → ℝ≥0∞) (lam : ℝ≥0∞) (k : ℕ)
    (z : α) : Prop :=
  ∫⁻ w in b1bmo_cellOf (idx k) z, F w ∂μ ≤ lam * μ (b1bmo_cellOf (idx k) z)

/-- **One generation of Calderón-Zygmund stopping**. The root is
`Q = cell 0 z₀`; `U` is the union of the maximal bad cells below it. -/
theorem b1bmo_stopping (μ : Measure α) (idx : ℕ → α → ι) (hidx : ∀ k, Measurable (idx k))
    (hnest : ∀ k z w, idx (k + 1) w = idx (k + 1) z → idx k w = idx k z)
    (z₀ : α) (F : α → ℝ≥0∞) (lam K : ℝ≥0∞)
    (hgood0 : b1bmo_good μ idx F lam 0 z₀)
    (hdiff : ∀ᵐ z ∂μ, idx 0 z = idx 0 z₀ → (∀ k, b1bmo_good μ idx F lam k z) → F z ≤ lam)
    (hcell : ∀ k z, idx 0 z = idx 0 z₀ → b1bmo_good μ idx F lam k z →
      ∫⁻ w in b1bmo_cellOf (idx (k + 1)) z, F w ^ 2 ∂μ ≤
        K * μ (b1bmo_cellOf (idx (k + 1)) z)) :
    ∃ U ⊆ b1bmo_cellOf (idx 0) z₀,
      (∫⁻ w in b1bmo_cellOf (idx 0) z₀, F w ^ 2 ∂μ ≤
        lam ^ 2 * μ (b1bmo_cellOf (idx 0) z₀) + K * μ U) ∧
      lam * μ U ≤ ∫⁻ w in b1bmo_cellOf (idx 0) z₀, F w ∂μ := by
  classical
  set Q := b1bmo_cellOf (idx 0) z₀ with hQ
  let S : ℕ → Set α := fun k =>
    {z | idx 0 z = idx 0 z₀ ∧ ¬ b1bmo_good μ idx F lam (k + 1) z ∧
      ∀ i ≤ k, b1bmo_good μ idx F lam i z}
  have hsat : ∀ k, ∀ z ∈ S k, ∀ w, idx (k + 1) w = idx (k + 1) z → w ∈ S k := by
    intro k z hz w hw
    obtain ⟨hz0, hzbad, hzgood⟩ := hz
    have heq : ∀ i ≤ k + 1, b1bmo_good μ idx F lam i w ↔ b1bmo_good μ idx F lam i z := by
      intro i hi
      unfold b1bmo_good
      rw [b1bmo_cellOf_eq (b1bmo_idx_eq_of_le hnest hi hw)]
    refine ⟨(b1bmo_idx_eq_of_le hnest (Nat.zero_le _) hw).trans hz0, ?_, ?_⟩
    · rwa [heq (k + 1) le_rfl]
    · intro i hi
      exact (heq i (hi.trans (Nat.le_succ k))).mpr (hzgood i hi)
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k =>
    b1bmo_measurableSet_of_saturated (hidx (k + 1)) (hsat k)
  have hSQ : ∀ k, S k ⊆ Q := fun k z hz => hz.1
  have hSdisj : Pairwise (Function.onFun Disjoint S) := by
    intro k l hkl
    refine Set.disjoint_left.mpr fun z hzk hzl => ?_
    rcases lt_or_gt_of_ne hkl with h | h
    · exact hzk.2.1 (hzl.2.2 (k + 1) h)
    · exact hzl.2.1 (hzk.2.2 (l + 1) h)
  set U := ⋃ k, S k with hU
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion hSmeas
  have hUQ : U ⊆ Q := iUnion_subset hSQ
  have hQmeas : MeasurableSet Q := b1bmo_measurableSet_cellOf (hidx 0) z₀
  -- outside `U`, every level is good
  have hout : ∀ z, idx 0 z = idx 0 z₀ → z ∉ U → ∀ k, b1bmo_good μ idx F lam k z := by
    intro z hz0 hzU k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases k with _ | k
      · unfold b1bmo_good
        rw [b1bmo_cellOf_eq hz0]
        exact hgood0
      · by_contra hbad
        exact hzU (mem_iUnion.mpr ⟨k, hz0, hbad, fun i hi => ih i (Nat.lt_succ_of_le hi)⟩)
  -- the bad set has small measure
  have hbad : lam * μ U ≤ ∫⁻ w in Q, F w ∂μ := by
    calc lam * μ U = ∑' k, ∫⁻ _ in S k, lam ∂μ := by
          rw [measure_iUnion hSdisj hSmeas, ← ENNReal.tsum_mul_left]
          simp only [setLIntegral_const]
      _ ≤ ∑' k, ∫⁻ w in S k, F w ∂μ := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          refine b1bmo_setLIntegral_le_of_saturated μ (hidx (k + 1)) (hsat k) fun z hz => ?_
          rw [setLIntegral_const]
          exact le_of_lt (not_le.mp hz.2.1)
      _ = ∫⁻ w in U, F w ∂μ := (lintegral_iUnion hSmeas hSdisj F).symm
      _ ≤ ∫⁻ w in Q, F w ∂μ := lintegral_mono_set hUQ
  -- the stopped cells
  have hgoodpart : ∫⁻ w in U, F w ^ 2 ∂μ ≤ K * μ U := by
    rw [lintegral_iUnion hSmeas hSdisj, measure_iUnion hSdisj hSmeas, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [← setLIntegral_const]
    refine b1bmo_setLIntegral_le_of_saturated μ (hidx (k + 1)) (hsat k) fun z hz => ?_
    rw [setLIntegral_const]
    exact hcell k z hz.1 (hz.2.2 k le_rfl)
  -- the complement of the stopped cells
  have hrest : ∫⁻ w in Q \ U, F w ^ 2 ∂μ ≤ lam ^ 2 * μ Q := by
    calc ∫⁻ w in Q \ U, F w ^ 2 ∂μ ≤ ∫⁻ _ in Q \ U, lam ^ 2 ∂μ := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' (hQmeas.diff hUmeas)]
          filter_upwards [hdiff] with z hz hzQU
          have hle : F z ≤ lam := hz hzQU.1 (hout z hzQU.1 hzQU.2)
          gcongr
      _ = lam ^ 2 * μ (Q \ U) := setLIntegral_const _ _
      _ ≤ lam ^ 2 * μ Q := by
          gcongr
          exact sdiff_subset
  have hsplit : ∫⁻ w in Q, F w ^ 2 ∂μ =
      ∫⁻ w in Q \ U, F w ^ 2 ∂μ + ∫⁻ w in U, F w ^ 2 ∂μ := by
    rw [← lintegral_union hUmeas disjoint_sdiff_left, sdiff_union_of_subset hUQ]
  refine ⟨U, hUQ, ?_, hbad⟩
  rw [hsplit]
  exact add_le_add hrest hgoodpart

end Countable

/-! ## Averages -/

theorem b1bmo_enorm_sq (y : ℝ) : ‖y‖ₑ ^ 2 = ENNReal.ofReal (y ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- `(x - a)² ≤ 2 (x - c)² + 2 (c - a)²` in extended form. -/
theorem b1bmo_enorm_sub_sq_le (x a c : ℝ) :
    ‖x - a‖ₑ ^ 2 ≤ 2 * ‖x - c‖ₑ ^ 2 + 2 * ‖c - a‖ₑ ^ 2 := by
  rw [b1bmo_enorm_sq, b1bmo_enorm_sq, b1bmo_enorm_sq]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x + a - 2 * c)])

/-- The distance from the average to any constant is at most the mean deviation. -/
theorem b1bmo_enorm_avg_sub_le (μ : Measure α) {D : Set α} (hD0 : μ D ≠ 0) (hDt : μ D ≠ ∞)
    {g : α → ℝ} (hg : IntegrableOn g D μ) (c : ℝ) :
    ‖b1bmo_avg μ D g - c‖ₑ ≤ (μ D)⁻¹ * ∫⁻ w in D, ‖g w - c‖ₑ ∂μ := by
  have hreal : (μ D).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hD0, hDt⟩
  have hsub : b1bmo_avg μ D g - c = (μ D).toReal⁻¹ * ∫ w in D, (g w - c) ∂μ := by
    rw [integral_sub hg (integrableOn_const hDt), setIntegral_const, smul_eq_mul,
      measureReal_def, b1bmo_avg]
    field_simp
  rw [hsub, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hD0 hDt), ENNReal.ofReal_toReal hDt]
  gcongr
  exact enorm_integral_le_lintegral_enorm _

/-- The square deviation from `a` is at most twice that from `c` plus the square shift. -/
theorem b1bmo_setLIntegral_sq_shift (μ : Measure α) (D : Set α) (g : α → ℝ) (a c : ℝ) :
    ∫⁻ w in D, ‖g w - a‖ₑ ^ 2 ∂μ ≤
      2 * ∫⁻ w in D, ‖g w - c‖ₑ ^ 2 ∂μ + 2 * ‖c - a‖ₑ ^ 2 * μ D := by
  calc ∫⁻ w in D, ‖g w - a‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ w in D, (2 * ‖g w - c‖ₑ ^ 2 + 2 * ‖c - a‖ₑ ^ 2) ∂μ :=
        lintegral_mono fun w => b1bmo_enorm_sub_sq_le _ _ _
    _ = 2 * ∫⁻ w in D, ‖g w - c‖ₑ ^ 2 ∂μ + 2 * ‖c - a‖ₑ ^ 2 * μ D := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
          setLIntegral_const]

/-- The mean oscillation is at most twice the mean deviation from any constant. -/
theorem b1bmo_setLIntegral_osc_le (μ : Measure α) {D : Set α} (hD0 : μ D ≠ 0)
    (hDt : μ D ≠ ∞) {g : α → ℝ} (hg : IntegrableOn g D μ) (c : ℝ) :
    ∫⁻ w in D, ‖g w - b1bmo_avg μ D g‖ₑ ∂μ ≤ 2 * ∫⁻ w in D, ‖g w - c‖ₑ ∂μ := by
  have hmeas : AEMeasurable (fun w => ‖g w - c‖ₑ) (μ.restrict D) :=
    (hg.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm
  calc ∫⁻ w in D, ‖g w - b1bmo_avg μ D g‖ₑ ∂μ
      ≤ ∫⁻ w in D, (‖g w - c‖ₑ + ‖b1bmo_avg μ D g - c‖ₑ) ∂μ := by
        refine lintegral_mono fun w => ?_
        calc ‖g w - b1bmo_avg μ D g‖ₑ = ‖(g w - c) - (b1bmo_avg μ D g - c)‖ₑ := by ring_nf
          _ ≤ ‖g w - c‖ₑ + ‖b1bmo_avg μ D g - c‖ₑ := enorm_sub_le
    _ = ∫⁻ w in D, ‖g w - c‖ₑ ∂μ + ‖b1bmo_avg μ D g - c‖ₑ * μ D := by
        rw [lintegral_add_left' hmeas, setLIntegral_const]
    _ ≤ ∫⁻ w in D, ‖g w - c‖ₑ ∂μ + ((μ D)⁻¹ * ∫⁻ w in D, ‖g w - c‖ₑ ∂μ) * μ D := by
        gcongr
        exact b1bmo_enorm_avg_sub_le μ hD0 hDt hg c
    _ = 2 * ∫⁻ w in D, ‖g w - c‖ₑ ∂μ := by
        rw [mul_comm _ (μ D), ← mul_assoc, ENNReal.mul_inv_cancel hD0 hDt, one_mul, two_mul]

/-- The per-child square bound of the stopping argument (hypothesis `hcell`):
`∫_D |g - c|² ≤ (2 φ + 2 (b lam)²) |D|` for a child `D` of a good cell `D'`. -/
theorem b1bmo_child_sq_le (μ : Measure α) {D D' : Set α} (hDD' : D ⊆ D') (hD0 : μ D ≠ 0)
    (hDt : μ D ≠ ∞) {g : α → ℝ} (hg : IntegrableOn g D μ) (c : ℝ) {φ lam b : ℝ≥0∞}
    (hφ : ∫⁻ w in D, ‖g w - b1bmo_avg μ D g‖ₑ ^ 2 ∂μ ≤ φ * μ D)
    (hgood : ∫⁻ w in D', ‖g w - c‖ₑ ∂μ ≤ lam * μ D')
    (hb : μ D' ≤ b * μ D) :
    ∫⁻ w in D, ‖g w - c‖ₑ ^ 2 ∂μ ≤ (2 * φ + 2 * (b * lam) ^ 2) * μ D := by
  have hshift : ‖b1bmo_avg μ D g - c‖ₑ ≤ b * lam := by
    calc ‖b1bmo_avg μ D g - c‖ₑ ≤ (μ D)⁻¹ * ∫⁻ w in D, ‖g w - c‖ₑ ∂μ :=
          b1bmo_enorm_avg_sub_le μ hD0 hDt hg c
      _ ≤ (μ D)⁻¹ * (lam * (b * μ D)) := by
          gcongr
          exact (lintegral_mono_set hDD').trans (hgood.trans (by gcongr))
      _ = b * lam * ((μ D)⁻¹ * μ D) := by ring
      _ = b * lam := by rw [ENNReal.inv_mul_cancel hD0 hDt, mul_one]
  calc ∫⁻ w in D, ‖g w - c‖ₑ ^ 2 ∂μ
      ≤ 2 * ∫⁻ w in D, ‖g w - b1bmo_avg μ D g‖ₑ ^ 2 ∂μ +
          2 * ‖b1bmo_avg μ D g - c‖ₑ ^ 2 * μ D :=
        b1bmo_setLIntegral_sq_shift μ D g c (b1bmo_avg μ D g)
    _ ≤ 2 * (φ * μ D) + 2 * (b * lam) ^ 2 * μ D := by gcongr
    _ = (2 * φ + 2 * (b * lam) ^ 2) * μ D := by ring

/-- The pointwise differentiation step (hypothesis `hdiff`): if the mean deviation of `g`
from `g z` on the cells of `z` tends to zero and every cell of `z` is good for `|g - c|`,
then `|g z - c| ≤ lam`. -/
theorem b1bmo_le_of_tendsto {μ : Measure α} {D : ℕ → Set α} (hD0 : ∀ k, μ (D k) ≠ 0)
    (hDt : ∀ k, μ (D k) ≠ ∞) {g : α → ℝ} (hmeas : ∀ k, AEStronglyMeasurable g (μ.restrict (D k)))
    (c : ℝ) (z : α) {lam : ℝ≥0∞}
    (hgood : ∀ k, ∫⁻ w in D k, ‖g w - c‖ₑ ∂μ ≤ lam * μ (D k))
    (hlim : Tendsto (fun k => (μ (D k))⁻¹ * ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ) atTop (𝓝 0)) :
    ‖g z - c‖ₑ ≤ lam := by
  have hbound : ∀ k, ‖g z - c‖ₑ ≤ lam + (μ (D k))⁻¹ * ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ := by
    intro k
    have hm : AEMeasurable (fun w => ‖g w - c‖ₑ) (μ.restrict (D k)) :=
      ((hmeas k).sub aestronglyMeasurable_const).enorm
    have h1 : ‖g z - c‖ₑ * μ (D k) ≤
        lam * μ (D k) + ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ := by
      calc ‖g z - c‖ₑ * μ (D k) = ∫⁻ _ in D k, ‖g z - c‖ₑ ∂μ := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ w in D k, (‖g w - c‖ₑ + ‖g w - g z‖ₑ) ∂μ := by
            refine lintegral_mono fun w => ?_
            calc ‖g z - c‖ₑ = ‖(g w - c) - (g w - g z)‖ₑ := by ring_nf
              _ ≤ ‖g w - c‖ₑ + ‖g w - g z‖ₑ := enorm_sub_le
        _ = ∫⁻ w in D k, ‖g w - c‖ₑ ∂μ + ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ :=
            lintegral_add_left' hm _
        _ ≤ lam * μ (D k) + ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ := by gcongr; exact hgood k
    calc ‖g z - c‖ₑ = ‖g z - c‖ₑ * μ (D k) * (μ (D k))⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel (hD0 k) (hDt k), mul_one]
      _ ≤ (lam * μ (D k) + ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ) * (μ (D k))⁻¹ := by gcongr
      _ = lam * (μ (D k) * (μ (D k))⁻¹) +
            (μ (D k))⁻¹ * ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ := by ring
      _ = lam + (μ (D k))⁻¹ * ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ := by
          rw [ENNReal.mul_inv_cancel (hD0 k) (hDt k), mul_one]
  have hlim' : Tendsto (fun k => lam + (μ (D k))⁻¹ * ∫⁻ w in D k, ‖g w - g z‖ₑ ∂μ) atTop
      (𝓝 (lam + 0)) := tendsto_const_nhds.add hlim
  rw [add_zero] at hlim'
  exact ge_of_tendsto' hlim' hbound

end ParabolicRectifiability.Characterization
