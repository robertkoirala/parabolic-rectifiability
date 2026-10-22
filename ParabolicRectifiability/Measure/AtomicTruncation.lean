import ParabolicRectifiability.Measure.AtomicBarycenterTransfer

/-!
# The truncated atomic convention is harmless

Let `P(c_j, ρ_j)` be pairwise disjoint open balls of positive
radius and `σ = ∑_j a_j δ_{c_j}` a finite atomic measure.

* For `s ≥ ρ_i`, the restrictions to `P(c_i, s)` of `σ` and of the truncated source
  `∑_{ρ_j ≤ s} a_j δ_{c_j}` (`finiteCutoffAtomicMeasure`) coincide.
* For `s < ρ_i`, both natural beta quantities at `c_i` vanish, for every available family:
  the full testing ball contains only the central atom, which lies on a model through
  `c_i`, and the truncated testing ball is empty.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The full finite atomic source `σ = ∑_j a_j δ_{c_j}`. -/
def fullAtomicMeasure (c : ι → Space n) (a : ι → ℝ) : Measure (Space n) :=
  ∑ j, ENNReal.ofReal (a j) • Measure.dirac (c j)

omit [Fintype ι] in
/-- Disjoint open balls of positive radius: each center lies outside every other ball,
so `d(c_i, c_j) ≥ ρ_j`; by symmetry `d(c_i, c_j) ≥ max ρ_i ρ_j`. -/
theorem radius_le_dist_of_pairwise_disjoint_balls (c : ι → Space n) (ρ : ι → ℝ)
    (hρ : ∀ j, 0 < ρ j)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (c i) (ρ i)) (Metric.ball (c j) (ρ j)))
    {i j : ι} (hij : i ≠ j) : ρ j ≤ dist (c i) (c j) := by
  by_contra h
  push Not at h
  have hi : c i ∈ Metric.ball (c i) (ρ i) := Metric.mem_ball_self (hρ i)
  have hj : c i ∈ Metric.ball (c j) (ρ j) := Metric.mem_ball.mpr h
  exact (hdisj hij).ne_of_mem hi hj rfl

omit [Fintype ι] in
theorem max_radius_le_dist_of_pairwise_disjoint_balls (c : ι → Space n) (ρ : ι → ℝ)
    (hρ : ∀ j, 0 < ρ j)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (c i) (ρ i)) (Metric.ball (c j) (ρ j)))
    {i j : ι} (hij : i ≠ j) : max (ρ i) (ρ j) ≤ dist (c i) (c j) := by
  refine max_le ?_ (radius_le_dist_of_pairwise_disjoint_balls c ρ hρ hdisj hij)
  rw [dist_comm]
  exact radius_le_dist_of_pairwise_disjoint_balls c ρ hρ hdisj hij.symm

/-- First claim: for `s ≥ ρ_i` the full and truncated sources have
the same restriction to the testing ball `P(c_i, s)`. -/
theorem restrict_ball_finiteCutoffAtomicMeasure_eq_fullAtomicMeasure (c : ι → Space n)
    (ρ a : ι → ℝ) (hρ : ∀ j, 0 < ρ j)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (c i) (ρ i)) (Metric.ball (c j) (ρ j)))
    {i : ι} {s : ℝ} (hs : ρ i ≤ s) :
    (finiteCutoffAtomicMeasure c ρ a s).restrict (Metric.ball (c i) s) =
      (fullAtomicMeasure c a).restrict (Metric.ball (c i) s) := by
  classical
  ext t ht
  have hm : MeasurableSet (t ∩ Metric.ball (c i) s) := ht.inter measurableSet_ball
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  simp only [finiteCutoffAtomicMeasure, fullAtomicMeasure, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · have hji : i ≠ j := fun h => hj (h ▸ hs)
    have hfar : c j ∉ t ∩ Metric.ball (c i) s := by
      intro hx
      have h1 := radius_le_dist_of_pairwise_disjoint_balls c ρ hρ hdisj hji
      have h2 : dist (c j) (c i) < s := hx.2
      rw [dist_comm] at h2
      linarith [not_le.mp hj]
    rw [Measure.dirac_apply' _ hm, Set.indicator_of_notMem hfar]
    simp

/-- The fitting integral sees only the restriction of the source to the testing ball. -/
theorem fit_eq_of_restrict_ball_eq {k : ℕ} {T : FamilyKind} {μ μ' : Measure (Space n)}
    (L : Models n k T) (z : Space n) (s : ℝ)
    (h : μ.restrict (Metric.ball z s) = μ'.restrict (Metric.ball z s)) :
    fit μ L z s = fit μ' L z s := by
  unfold fit
  rw [h]

/-- Consequence of the first claim: for `s ≥ ρ_i` the full and truncated betas agree. -/
theorem betaSq_finiteCutoffAtomicMeasure_eq_fullAtomicMeasure (c : ι → Space n)
    (ρ a : ι → ℝ) (hρ : ∀ j, 0 < ρ j)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (c i) (ρ i)) (Metric.ball (c j) (ρ j)))
    (k : ℕ) (T : FamilyKind) {i : ι} {s : ℝ} (hs : ρ i ≤ s) :
    betaSq (finiteCutoffAtomicMeasure c ρ a s) k T (c i) s =
      betaSq (fullAtomicMeasure c a) k T (c i) s := by
  have h := restrict_ball_finiteCutoffAtomicMeasure_eq_fullAtomicMeasure c ρ a hρ hdisj hs
  unfold betaSq
  simp only [fit_eq_of_restrict_ball_eq _ (c i) s h]

/-- Second claim for the full source: below `ρ_i` the full testing
ball contains only the central atom, which lies on a member of the available family. -/
theorem betaSq_fullAtomicMeasure_eq_zero (c : ι → Space n) (ρ a : ι → ℝ)
    (hρ : ∀ j, 0 < ρ j)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (c i) (ρ i)) (Metric.ball (c j) (ρ j)))
    {k : ℕ} {T : FamilyKind} (hT : Nonempty (Models n k T)) {i : ι} {s : ℝ} (hs : s < ρ i) :
    betaSq (fullAtomicMeasure c a) k T (c i) s = 0 := by
  by_cases hs0 : s ≤ 0
  · exact betaSq_of_nonpos _ _ _ _ hs0
  push Not at hs0
  obtain ⟨L, hL⟩ := exists_model_mem hT (c i)
  have hterm : ∀ j, (Metric.ball (c i) s).indicator (modelCost L) (c j) = 0 := by
    intro j
    by_cases hji : j = i
    · rw [hji, Set.indicator_of_mem (Metric.mem_ball_self hs0)]
      simp [modelCost, Metric.infEDist_zero_of_mem hL]
    · apply Set.indicator_of_notMem
      intro hx
      have h1 := radius_le_dist_of_pairwise_disjoint_balls c ρ hρ hdisj hji
      have h2 : dist (c j) (c i) < s := hx
      linarith
  have hfit : fit (fullAtomicMeasure c a) L (c i) s = 0 := by
    unfold fit fullAtomicMeasure
    rw [← lintegral_indicator measurableSet_ball, lintegral_finsetSum_measure]
    simp_rw [lintegral_smul_measure, lintegral_dirac]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [hterm j, smul_zero]
  rw [betaSq_of_pos _ _ _ _ hs0]
  exact mul_eq_zero_of_right _ (le_antisymm ((iInf_le _ L).trans hfit.le) zero_le)

/-- Second claim for the truncated source: below `ρ_i` the truncated
testing ball is empty. -/
theorem betaSq_finiteCutoffAtomicMeasure_eq_zero (c : ι → Space n) (ρ a : ι → ℝ)
    (hρ : ∀ j, 0 < ρ j)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (c i) (ρ i)) (Metric.ball (c j) (ρ j)))
    {k : ℕ} {T : FamilyKind} (hT : Nonempty (Models n k T)) {i : ι} {s : ℝ} (hs : s < ρ i) :
    betaSq (finiteCutoffAtomicMeasure c ρ a s) k T (c i) s = 0 := by
  classical
  by_cases hs0 : s ≤ 0
  · exact betaSq_of_nonpos _ _ _ _ hs0
  push Not at hs0
  obtain ⟨L⟩ := hT
  have hfit : fit (finiteCutoffAtomicMeasure c ρ a s) L (c i) s = 0 := by
    rw [fit_finiteCutoffAtomicMeasure]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := (Finset.mem_filter.mp hj).2
    exfalso
    by_cases hji : j = i
    · rw [hji] at hj'
      linarith [hj'.1]
    · have h1 := radius_le_dist_of_pairwise_disjoint_balls c ρ hρ hdisj hji
      have h2 : dist (c j) (c i) < s := hj'.2
      linarith
  rw [betaSq_of_pos _ _ _ _ hs0]
  exact mul_eq_zero_of_right _ (le_antisymm ((iInf_le _ L).trans hfit.le) zero_le)

/-- Second claim: at `s < ρ_i` both beta quantities vanish. -/
theorem betaSq_atomic_eq_zero_of_lt_radius (c : ι → Space n) (ρ a : ι → ℝ)
    (hρ : ∀ j, 0 < ρ j)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (c i) (ρ i)) (Metric.ball (c j) (ρ j)))
    {k : ℕ} {T : FamilyKind} (hT : Nonempty (Models n k T)) {i : ι} {s : ℝ} (hs : s < ρ i) :
    betaSq (fullAtomicMeasure c a) k T (c i) s = 0 ∧
      betaSq (finiteCutoffAtomicMeasure c ρ a s) k T (c i) s = 0 :=
  ⟨betaSq_fullAtomicMeasure_eq_zero c ρ a hρ hdisj hT hs,
    betaSq_finiteCutoffAtomicMeasure_eq_zero c ρ a hρ hdisj hT hs⟩

end ParabolicRectifiability
