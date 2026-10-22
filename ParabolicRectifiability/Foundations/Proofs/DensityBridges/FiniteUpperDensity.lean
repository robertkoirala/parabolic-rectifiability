import ParabolicRectifiability.Foundations.Proofs.DensityBridges.FiniteUpperDensityStatement
import ParabolicRectifiability.Foundations.Proofs.UpperGrowth
import ParabolicRectifiability.Measure.Beta

/-! # Finite upper density a.e. gives `μ ≪ H_P^k`

Proof of `f2i_absolutelyContinuous_of_upperDensity_lt_top_proof : f2i_UpperDensityACStatement`.
Route (global classes):
1. the local upper-density bound (the hypothesis of the statement, never reproved) puts every
   point of finite
   upper density into an integer class `F a j` (`f2i_mem_class_of_upperDensity_lt_top`);
2. `μ.restrict (F a j)` has all-centre growth at small radii (`f2i_restrict_class_growth`);
3. that restriction is locally Radon, so `fgac_absolutelyContinuous_hausdorffP_of_growth_proof`
   gives absolute continuity with respect to `H_P^k`;
4. a countable union over the classes plus the `μ`-null bad set.

Helper prefix `f2i_`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Foundations

/-- The integer class `F a j`: radii below `1/(j+1)` carry mass at most `(a+1) r^k`. -/
def f2i_acClass {n : ℕ} (μ : Measure (Space n)) (k a j : ℕ) : Set (Space n) :=
  {z | ∀ r : ℝ, 0 < r → r < 1 / ((j : ℝ) + 1) →
    μ (Metric.ball z r) ≤ ENNReal.ofReal ((a : ℝ) + 1) * ENNReal.ofReal r ^ k}

/-- Step 1: the C2-D bound places a point of finite upper density in some class. -/
theorem f2i_mem_class_of_upperDensity_lt_top {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (z : Space n) {A : ℝ≥0∞} {ρ : ℝ} (hA : A ≠ ⊤) (hρ : 0 < ρ)
    (hb : ∀ r : ℝ, 0 < r → r < ρ → densityRatio μ k z r ≤ A) :
    ∃ a j : ℕ, z ∈ f2i_acClass μ k a j := by
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hρ
  refine ⟨⌈A.toReal⌉₊, j, fun r hr hrj => ?_⟩
  have hAa : A ≤ ENNReal.ofReal ((⌈A.toReal⌉₊ : ℝ) + 1) := by
    refine (ENNReal.ofReal_toReal hA).symm.le.trans (ENNReal.ofReal_le_ofReal ?_)
    exact (Nat.le_ceil _).trans (by linarith)
  have h0 : ENNReal.ofReal r ^ k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne'
  have ht : ENNReal.ofReal r ^ k ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.div_le_iff h0 ht).1 ((hb r hr (hrj.trans hj)).trans hAa)

/-- Step 2: all-centre growth of `μ` restricted to a class, for `0 < r ≤ 1/(4(j+1))`. No
measurability of the class is used. -/
theorem f2i_restrict_class_growth {n : ℕ} (μ : Measure (Space n)) (k a j : ℕ)
    (p : Space n) (r : ℝ) (hr : 0 < r) (hrj : r ≤ 1 / (4 * ((j : ℝ) + 1))) :
    μ.restrict (f2i_acClass μ k a j) (Metric.ball p r) ≤
      ENNReal.ofReal (((a : ℝ) + 1) * 2 ^ k * r ^ k) := by
  rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet]
  rcases (Metric.ball p r ∩ f2i_acClass μ k a j).eq_empty_or_nonempty with he | ⟨z, hzb, hzF⟩
  · rw [he, measure_empty]
    exact zero_le
  have hsub : Metric.ball p r ∩ f2i_acClass μ k a j ⊆ Metric.ball z (2 * r) := by
    intro y hy
    have hy' := hy.1
    rw [Metric.mem_ball] at hy' hzb ⊢
    have := dist_triangle y p z
    rw [dist_comm p z] at this
    linarith
  have h2r : 2 * r < 1 / ((j : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)] at hrj
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  refine (measure_mono hsub).trans ((hzF (2 * r) (by linarith) h2r).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow]
  ring

/-- **AC-dens** (`f2i_UpperDensityACStatement`), proved from the C2-D hypothesis. -/
theorem f2i_absolutelyContinuous_of_upperDensity_lt_top_proof : f2i_UpperDensityACStatement := by
  intro hC2 n hn k hk hkn μ hμ hreg hae
  -- Step 3: each class restriction is absolutely continuous with respect to `H_P^k`.
  have hclass : ∀ a j : ℕ, μ.restrict (f2i_acClass μ k a j) ≪ hausdorffP n k := by
    intro a j
    set ν := μ.restrict (f2i_acClass μ k a j)
    have h1 : IsFiniteMeasureOnCompacts ν := inferInstance
    have h2 : Measure.InnerRegularCompactLTTop ν := by
      have : Measure.InnerRegularCompactLTTop μ := inferInstance
      infer_instance
    have h3 : SigmaFinite ν := source_sigmaFinite _
    have h4 : ν.InnerRegular := inferInstance
    exact fgac_absolutelyContinuous_hausdorffP_of_growth_proof n hn k hk hkn ν h1 h4
      (((a : ℝ) + 1) * 2 ^ k) (1 / (4 * ((j : ℝ) + 1))) (by positivity)
      (fun p r hr hrj => f2i_restrict_class_growth μ k a j p r hr hrj)
  -- Step 4: cover by the classes and the null bad set.
  have hbad : μ {z | ¬ upperDensity μ k z < ⊤} = 0 := ae_iff.1 hae
  intro Z hZ
  have hcover : Z ⊆ (⋃ a : ℕ, ⋃ j : ℕ, Z ∩ f2i_acClass μ k a j) ∪
      {z | ¬ upperDensity μ k z < ⊤} := by
    intro z hz
    by_cases hd : upperDensity μ k z < ⊤
    · obtain ⟨A, ρ, hA, hρ, hb⟩ := hC2 μ k z hd
      obtain ⟨a, j, hzF⟩ := f2i_mem_class_of_upperDensity_lt_top μ k z hA hρ hb
      exact Or.inl (mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨j, hz, hzF⟩⟩)
    · exact Or.inr hd
  refine measure_mono_null hcover (measure_union_null ?_ hbad)
  refine measure_iUnion_null fun a => measure_iUnion_null fun j => ?_
  exact le_antisymm ((Measure.le_restrict_apply _ _).trans (le_of_eq (hclass a j hZ))) zero_le

end ParabolicRectifiability.Foundations
