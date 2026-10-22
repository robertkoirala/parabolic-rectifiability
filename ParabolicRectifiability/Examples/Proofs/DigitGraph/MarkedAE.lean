import ParabolicRectifiability.Examples.Proofs.DigitGraph.DigitStatements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Almost every parameter has infinitely many marked digits

The set of parameters in `[0,1)` whose digits of generations `m, …, N` are all unmarked has
measure tending to zero as `N → ∞`; hence Lebesgue-almost every `x ∈ [0,1)` lies in infinitely
many marked sets (`e2_sb_markedAE_proof`). -/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Examples

private def avoidance (m n : ℕ) : Set ℝ :=
  {x | ∀ i ∈ Finset.Ico m n, x ∉ e2_sbMarked i}

private def survival (m n : ℕ) : ℝ → ℝ :=
  (avoidance m n).indicator (fun _ => 1)

private theorem avoidance_measurable (hM : E2sbMeasurable) (m n : ℕ) :
    MeasurableSet (avoidance m n) := by
  have hs : avoidance m n = ⋂ i : ℕ, ⋂ (_ : i ∈ Finset.Ico m n),
      (e2_sbMarked i)ᶜ := by
    ext x
    simp [avoidance]
  rw [hs]
  exact MeasurableSet.iInter fun (i : ℕ) =>
    MeasurableSet.iInter fun (_ : i ∈ Finset.Ico m n) => (hM.1 i).compl

private theorem survival_integrable (hM : E2sbMeasurable) (m n : ℕ) (a b : ℝ) :
    IntervalIntegrable (survival m n) volume a b := by
  exact intervalIntegrable_iff.mpr
    ((intervalIntegrable_const (c := (1 : ℝ))).def'.indicator (avoidance_measurable hM m n))

private theorem survival_succ {m n : ℕ} (hmn : m ≤ n) (x : ℝ) :
    survival m (n + 1) x = survival m n x * (1 - e2_sbBit n x) := by
  classical
  have hset : avoidance m (n + 1) = avoidance m n ∩ (e2_sbMarked n)ᶜ := by
    ext x
    simp [avoidance, Nat.Ico_succ_right_eq_insert_Ico hmn, and_comm]
  simp only [survival, hset, e2_sbBit, Set.indicator_apply, Set.mem_inter_iff,
    Set.mem_compl_iff]
  split_ifs <;> simp_all

private theorem survival_constant (hD : E2sbDigit) {m n j : ℕ}
    (hm : 1 ≤ m) (hn : n ≤ j + 1) (k : ℤ) {x y : ℝ}
    (hx : x ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j))
    (hy : y ∈ Ico ((k : ℝ) * e2_sbEll j) (((k : ℝ) + 1) * e2_sbEll j)) :
    survival m n x = survival m n y := by
  classical
  have hbits : ∀ i ∈ Finset.Ico m n, (x ∈ e2_sbMarked i ↔ y ∈ e2_sbMarked i) := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hb := hD.1 j i (hm.trans hi'.1) (by omega) k x y hx hy
    by_cases hx' : x ∈ e2_sbMarked i <;> by_cases hy' : y ∈ e2_sbMarked i <;>
      simp_all [e2_sbBit]
  have ha : x ∈ avoidance m n ↔ y ∈ avoidance m n := by
    simp only [avoidance, Set.mem_ofPred_eq]
    exact forall_congr' fun i => forall_congr' fun hi => not_congr (hbits i hi)
  simp only [survival, Set.indicator_apply]
  simp [ha]

/-- A parent contains an integer number of periods. On the first period precisely
its first child is marked, so its marked integral is exactly its length divided by j+1. -/
private theorem marked_parent_integral (hG : E2sbGrid) (hM : E2sbMeasurable)
    {j : ℕ} (hj : 1 ≤ j) (a : ℝ) :
    (∫ x in a..a + e2_sbEll (j - 1), e2_sbBit j x) =
      e2_sbDelta j * e2_sbEll (j - 1) := by
  classical
  have hl := hG.1 j
  have hp : 0 < e2_sbPeriod j := by unfold e2_sbPeriod; positivity
  have hfi : ∀ a b, IntervalIntegrable (e2_sbBit j) volume a b := fun a b =>
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_const (c := (1 : ℝ))).def'.indicator (hM.1 j))
  have hper : Function.Periodic (e2_sbBit j) (e2_sbPeriod j) := by
    intro x
    have hf : ⌊(x + e2_sbPeriod j) / e2_sbEll j⌋ =
        ⌊x / e2_sbEll j⌋ + ((j + 1 : ℕ) : ℤ) := by
      rw [e2_sbPeriod, add_div, mul_div_cancel_right₀ _ hl.ne']
      exact_mod_cast Int.floor_add_intCast (x / e2_sbEll j) ((j + 1 : ℕ) : ℤ)
    simp [e2_sbBit, Set.indicator_apply, e2_sbMarked, hf, dvd_add_self_right]
  have hfirst : ∀ x ∈ Ico 0 (e2_sbPeriod j),
      x ∈ e2_sbMarked j ↔ x < e2_sbEll j := by
    intro x hx
    have h0 : 0 ≤ ⌊x / e2_sbEll j⌋ := Int.floor_nonneg.mpr (div_nonneg hx.1 hl.le)
    have hq : ⌊x / e2_sbEll j⌋ < ((j + 1 : ℕ) : ℤ) := by
      apply Int.floor_lt.mpr
      simpa [e2_sbPeriod, Nat.cast_add, Nat.cast_one] using (div_lt_iff₀ hl).mpr hx.2
    change ((j + 1 : ℕ) : ℤ) ∣ ⌊x / e2_sbEll j⌋ ↔ _
    constructor
    · intro h
      exact (div_lt_one hl).mp (Int.floor_eq_zero_iff.mp
        (Int.eq_zero_of_dvd_of_nonneg_of_lt h0 hq h)).2
    · intro h
      rw [Int.floor_eq_zero_iff.mpr ⟨div_nonneg hx.1 hl.le, (div_lt_one hl).mpr h⟩]
      exact dvd_zero _
  have hlp : e2_sbEll j ≤ e2_sbPeriod j := by
    unfold e2_sbPeriod
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hmean : (∫ x in 0..e2_sbPeriod j, e2_sbBit j x) = e2_sbEll j := by
    have hleft : (∫ x in 0..e2_sbEll j, e2_sbBit j x) = e2_sbEll j := by
      calc
        _ = ∫ _ in (0 : ℝ)..e2_sbEll j, (1 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hl.le
          intro x hx
          simp [e2_sbBit, (hfirst x ⟨hx.1.le, hx.2.trans_le hlp⟩).mpr hx.2]
        _ = _ := by simp
    have hright : (∫ x in e2_sbEll j..e2_sbPeriod j, e2_sbBit j x) = 0 := by
      calc
        _ = ∫ _ in e2_sbEll j..e2_sbPeriod j, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hlp
          intro x hx
          have hn : x ∉ e2_sbMarked j := by
            rw [hfirst x ⟨hl.le.trans hx.1.le, hx.2⟩]
            exact not_lt.mpr hx.1.le
          simp [e2_sbBit, hn]
        _ = _ := by simp
    linarith [intervalIntegral.integral_add_adjacent_intervals
      (hfi 0 (e2_sbEll j)) (hfi (e2_sbEll j) (e2_sbPeriod j))]
  have hscale := hG.2.2.2.2.2.2.2.1 j hj
  have hz := hper.intervalIntegral_add_zsmul_eq ((2 : ℤ) ^ (j + 30)) a hfi
  rw [hper.intervalIntegral_add_eq a 0, zero_add, hmean] at hz
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_ofNat] at hz
  rw [hscale, hz]
  unfold e2_sbDelta e2_sbPeriod
  field_simp

private theorem survival_parent_step (hG : E2sbGrid) (hD : E2sbDigit)
    (hM : E2sbMeasurable) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (k : ℕ) :
    (∫ x in (k : ℝ) * e2_sbEll (n - 1)..(k + 1 : ℕ) * e2_sbEll (n - 1),
      survival m (n + 1) x) =
    (1 - e2_sbDelta n) *
      ∫ x in (k : ℝ) * e2_sbEll (n - 1)..(k + 1 : ℕ) * e2_sbEll (n - 1),
        survival m n x := by
  have hn : 1 ≤ n := hm.trans hmn
  let L := e2_sbEll (n - 1)
  let a : ℝ := k * L
  have hL : 0 < L := hG.1 _
  have hab : a ≤ a + L := by linarith
  have hconst : ∀ x ∈ Ioo a (a + L), survival m n x = survival m n a := by
    intro x hx
    apply survival_constant hD (j := n - 1) hm (by omega) (k : ℤ)
    · simpa [a, L, add_mul, Nat.cast_add, Nat.cast_one] using And.intro hx.1.le hx.2
    · simp only [Int.cast_natCast]
      dsimp [a, L]
      constructor
      · rfl
      · nlinarith
  have he : ((k + 1 : ℕ) : ℝ) * L = a + L := by simp [a, Nat.cast_add, add_mul]
  change (∫ x in a..((k + 1 : ℕ) : ℝ) * L, survival m (n + 1) x) =
    (1 - e2_sbDelta n) * ∫ x in a..((k + 1 : ℕ) : ℝ) * L, survival m n x
  rw [he]
  have hi : (∫ x in a..a + L, survival m n x) = survival m n a * L := by
    calc
      _ = ∫ _ in a..a + L, survival m n a :=
        intervalIntegral.integral_congr_Ioo_of_le hab hconst
      _ = _ := by simp; ring
  have hf : IntervalIntegrable (e2_sbBit n) volume a (a + L) :=
    intervalIntegrable_iff.mpr
      ((intervalIntegrable_const (c := (1 : ℝ))).def'.indicator (hM.1 n))
  calc
    _ = ∫ x in a..a + L, survival m n a * (1 - e2_sbBit n x) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro x hx
      rw [survival_succ hmn, hconst x hx]
    _ = survival m n a * (L - e2_sbDelta n * L) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub intervalIntegrable_const hf,
        marked_parent_integral hG hM hn]
      simp [L]
    _ = _ := by rw [hi]; ring

private theorem survival_integral_step (hG : E2sbGrid) (hD : E2sbDigit)
    (hM : E2sbMeasurable) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∫ x in (0 : ℝ)..1, survival m (n + 1) x) =
      (1 - e2_sbDelta n) * ∫ x in (0 : ℝ)..1, survival m n x := by
  obtain ⟨c, hc⟩ := hG.2.2.2.2.1 (n - 1)
  have hs (r : ℕ) := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * e2_sbEll (n - 1)) (n := c)
    (fun k _ => survival_integrable hM m r _ _)
  simp only [Nat.cast_zero, zero_mul, hc] at hs
  rw [← hs (n + 1), ← hs n, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => survival_parent_step hG hD hM hm hmn k

/-- Exact finite avoidance probability, with the upper digit index excluded. -/
private theorem survival_integral (hG : E2sbGrid) (hD : E2sbDigit)
    (hM : E2sbMeasurable) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (∫ x in (0 : ℝ)..1, survival m n x) = (m : ℝ) / n := by
  induction n, hmn using Nat.le_induction with
  | base =>
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      simp [survival, avoidance, hm0]
  | succ n hmn ih =>
      rw [survival_integral_step hG hD hM hm hmn, ih]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      unfold e2_sbDelta
      push_cast
      field_simp
      ring

private theorem avoidance_measure (hG : E2sbGrid) (hD : E2sbDigit)
    (hM : E2sbMeasurable) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (volume.restrict (Ico (0 : ℝ) 1)) (avoidance m n) =
      ENNReal.ofReal ((m : ℝ) / n) := by
  have hi : (∫ x in (0 : ℝ)..1, survival m n x) =
      ((volume.restrict (Ico (0 : ℝ) 1)) (avoidance m n)).toReal := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      ← integral_Ico_eq_integral_Ioc]
    rw [survival, integral_indicator (avoidance_measurable hM m n),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (volume.restrict (Ico (0 : ℝ) 1))
    (avoidance m n)), ← hi,
    survival_integral hG hD hM hm hmn]

/-- Almost every parameter has marked digits at arbitrarily large generations. -/
theorem e2_sb_markedAE_proof (hG : E2sbGrid) (hD : E2sbDigit)
    (hM : E2sbMeasurable) : E2sbMarkedAE := by
  have hall : ∀ᵐ x ∂(volume.restrict (Ico (0 : ℝ) 1)),
      ∀ m : ℕ, ∃ j, m ≤ j ∧ x ∈ e2_sbMarked j := by
    rw [ae_all_iff]
    intro m
    rw [ae_iff]
    apply le_antisymm ?_ bot_le
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (((max m 1 : ℕ) : ℝ) / n))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_const_div_atTop_nhds_zero_nat (((max m 1 : ℕ) : ℝ)))
    apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop (max m 1)] with n hn
    rw [← avoidance_measure hG hD hM (le_max_right m 1) hn]
    apply measure_mono
    intro x hx i hi hiMark
    exact hx ⟨i, (le_max_left m 1).trans (Finset.mem_Ico.mp hi).1, hiMark⟩
  filter_upwards [hall] with x hx
  exact frequently_atTop.mpr hx

end ParabolicRectifiability.Examples
