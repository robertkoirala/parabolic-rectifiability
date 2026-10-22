module

public import ParabolicRectifiability.Analysis.FractionalKernel.Multiplier

/-!
# Symmetric scalar truncations

The annulus at index zero is empty. All convergence and multiplier statements
include that index and zero frequency.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace ParabolicRectifiability.FractionalKernel

/-- The exact annuli `1/(n+1) < |h| < n+1`, with ordinary real coordinates. -/
def symmetricAnnulus (n : ℕ) : Set ℝ :=
  {h : ℝ | 1 / ((n : ℝ) + 1) < |h| ∧ |h| < (n : ℝ) + 1}

theorem measurableSet_symmetricAnnulus (n : ℕ) : MeasurableSet (symmetricAnnulus n) :=
  (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

@[simp] theorem mem_symmetricAnnulus_neg (n : ℕ) (h : ℝ) :
    -h ∈ symmetricAnnulus n ↔ h ∈ symmetricAnnulus n := by
  simp [symmetricAnnulus]

@[simp] theorem symmetricAnnulus_zero : symmetricAnnulus 0 = ∅ := by
  ext h
  simp only [symmetricAnnulus, Nat.cast_zero, zero_add, div_one, mem_ofPred_eq, mem_empty_iff_false,
    iff_false, not_and]
  exact fun hh => not_lt_of_ge (le_of_lt hh)

@[simp] theorem zero_not_mem_symmetricAnnulus (n : ℕ) : (0 : ℝ) ∉ symmetricAnnulus n := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  simp only [symmetricAnnulus, mem_ofPred_eq, abs_zero, not_and]
  exact fun h => (not_lt_of_ge (le_of_lt (one_div_pos.mpr hn)) h).elim

theorem monotone_symmetricAnnulus : Monotone symmetricAnnulus := by
  intro n m hnm h hh
  have hcast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  exact ⟨lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hcast) hh.1,
    lt_of_lt_of_le hh.2 hcast⟩

/-- Exhaustion of precisely the nonzero reals. -/
theorem iUnion_symmetricAnnulus : (⋃ n : ℕ, symmetricAnnulus n) = {h : ℝ | h ≠ 0} := by
  ext h
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn⟩ rfl
    exact zero_not_mem_symmetricAnnulus n hn
  · intro hh
    have hpos : 0 < |h| := abs_pos.mpr hh
    obtain ⟨n, hn⟩ := exists_nat_gt (max |h| (1 / |h|))
    refine ⟨n, ?_, ?_⟩
    · apply (one_div_lt (by positivity : 0 < (n : ℝ) + 1) hpos).mpr
      have := lt_of_le_of_lt (le_max_right |h| (1 / |h|)) hn
      linarith
    · have := lt_of_le_of_lt (le_max_left |h| (1 / |h|)) hn
      linarith

/-- The only omitted point has zero ordinary Lebesgue measure. -/
theorem volume_compl_iUnion_symmetricAnnulus :
    volume (⋃ n : ℕ, symmetricAnnulus n)ᶜ = 0 := by
  rw [iUnion_symmetricAnnulus]
  simp

/-- The normalized real multiplier of a finite symmetric truncation. -/
def truncatedMultiplier (n : ℕ) (τ : ℝ) : ℝ :=
  kappa * ∫ h in symmetricAnnulus n, frequencyIntegrand τ h

@[simp] theorem truncatedMultiplier_zero_index (τ : ℝ) : truncatedMultiplier 0 τ = 0 := by
  simp [truncatedMultiplier]

@[simp] theorem truncatedMultiplier_zero_frequency (n : ℕ) : truncatedMultiplier n 0 = 0 := by
  simp [truncatedMultiplier]

theorem truncatedMultiplier_nonneg (n : ℕ) (τ : ℝ) : 0 ≤ truncatedMultiplier n τ := by
  exact mul_nonneg kappa_pos.le (integral_nonneg (frequencyIntegrand_nonneg τ))

theorem truncatedMultiplier_le (n : ℕ) (τ : ℝ) :
    truncatedMultiplier n τ ≤ |τ| ^ (1 / 2 : ℝ) := by
  rw [← kappa_mul_integral_frequencyIntegrand τ]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_le_integral (integrable_frequencyIntegrand τ)
      (Eventually.of_forall (frequencyIntegrand_nonneg τ))) kappa_pos.le

theorem monotone_truncatedMultiplier (τ : ℝ) : Monotone (fun n => truncatedMultiplier n τ) := by
  intro n m hnm
  exact mul_le_mul_of_nonneg_left
    (setIntegral_mono_set (integrable_frequencyIntegrand τ).integrableOn
      (Eventually.of_forall (frequencyIntegrand_nonneg τ))
      (Eventually.of_forall (monotone_symmetricAnnulus hnm))) kappa_pos.le

/-- Exhausting the annuli recovers the full real integral; the integrand is zero at the omitted point. -/
theorem integral_iUnion_symmetricAnnulus (τ : ℝ) :
    (∫ h in ⋃ n : ℕ, symmetricAnnulus n, frequencyIntegrand τ h) =
      ∫ h : ℝ, frequencyIntegrand τ h := by
  rw [← integral_indicator (MeasurableSet.iUnion measurableSet_symmetricAnnulus)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  rw [iUnion_symmetricAnnulus]
  by_cases hh : h = 0 <;> simp [hh]

theorem tendsto_truncatedMultiplier (τ : ℝ) :
    Tendsto (fun n => truncatedMultiplier n τ) atTop (𝓝 (|τ| ^ (1 / 2 : ℝ))) := by
  have ht := tendsto_setIntegral_of_monotone measurableSet_symmetricAnnulus
    monotone_symmetricAnnulus (integrable_frequencyIntegrand τ).integrableOn
  rw [integral_iUnion_symmetricAnnulus] at ht
  have hm := ht.const_mul kappa
  rw [kappa_mul_integral_frequencyIntegrand] at hm
  exact hm

/-- The finite complex Fourier integral is integrable, including the empty initial annulus. -/
theorem integrableOn_complexFrequencyIntegrand_symmetricAnnulus (n : ℕ) (τ : ℝ) :
    IntegrableOn (complexFrequencyIntegrand τ) (symmetricAnnulus n) volume :=
  (integrable_complexFrequencyIntegrand τ).integrableOn

/-- The finite symmetric complex integral is exactly the real multiplier used against Fourier tests. -/
theorem kappa_mul_integral_complexFrequencyIntegrand_symmetricAnnulus (n : ℕ) (τ : ℝ) :
    (kappa : ℂ) * (∫ h in symmetricAnnulus n, complexFrequencyIntegrand τ h) =
      (truncatedMultiplier n τ : ℂ) := by
  rw [integral_complexFrequencyIntegrand_of_symmetric τ (measurableSet_symmetricAnnulus n)
    (mem_symmetricAnnulus_neg n)]
  exact (Complex.ofReal_mul _ _).symm

end ParabolicRectifiability.FractionalKernel
