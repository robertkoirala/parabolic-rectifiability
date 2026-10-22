import ParabolicRectifiability.BetaP.Proofs.Localization.LocalizationLemmas
import ParabolicRectifiability.Decomposition.SourceLocalization

/-! # Localization of a source for the `p`-energy

`cloc_exists_p_localization` proves `exists_p_localization`: for every `n` there is `N`, depending
only on `n`, such that every locally Radon source decomposes, on the `S_p` good set, into `N`
pieces, each finite, inner regular and with support in a ball of radius `1/64`, with all-scale
`p`-energy bounded by `2M`. The inputs are `cloc_pTail`, `cloc_allScale`,
`cloc_input_measurability` and `cloc_input_restriction`.

Construction, following the quadratic localization `goodSourceLocalization` with the `S_p` good set:
* the fixed cover of `P̄(0,1)` by `localizationCount n` open balls of radius `1/64`, chosen
  from the dimension only, disjointified in the order of `Fin` (`localizationCell`); hence
  `N = localizationCount n + 1` depends on `n` only, before `p`, `k`, `T`, `μ` and `M`;
* the regions are the actual Borel sets `pGoodSet μ k T p M ∩ localizationCell n i` (Borel by
  the input law `BetaPowMeasurabilityStatement`); they are disjoint and cover the good set
  exactly;
* each restriction is finite (its region lies in a ball of radius `1/64`), inner regular, and
  supported in the closed ball of its cell (`support_restrict_subset_closedBall`);
* almost every point of a restricted source lies in its region (so `S_{p,μ}^2 ≤ M` there) and in
  its support, where `cloc_allScale` gives the all-scale bound `2M`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.BetaP

open ParabolicRectifiability.Foundations

/-- The localization regions: the `S_p`-good points of the unit ball in the fixed cells. -/
def clocRegion {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (p M : ℝ)
    (i : Fin (localizationCount n)) : Set (Space n) :=
  pGoodSet μ k T p M ∩ localizationCell n i

theorem cloc_region_subset_ball {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (p M : ℝ) (i : Fin (localizationCount n)) :
    clocRegion μ k T p M i ⊆ Metric.ball (localizationCenter n i) (1 / 64) :=
  inter_subset_right.trans (localizationCell_subset_ball n i)

/-- Exact cover of the `S_p` good set by the regions. -/
theorem cloc_iUnion_region {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (p M : ℝ) : (⋃ i, clocRegion μ k T p M i) = pGoodSet μ k T p M := by
  simp only [clocRegion]
  rw [← inter_iUnion, iUnion_localizationCell]
  exact inter_eq_left.mpr (inter_subset_left.trans
    (Metric.ball_subset_closedBall.trans (closedBall_subset_iUnion_localizationBall n)))

/-- The `S_p` good set of a locally Radon source is Borel (measurability law for `B_p`). -/
theorem cloc_measurableSet_pGoodSet {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    {T : FamilyKind} (hT : Nonempty (Models n k T)) (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) {p : ℝ} (hp : 0 < p) (M : ℝ) :
    MeasurableSet (pGoodSet μ k T p M) :=
  measurableSet_ball.inter (measurableSet_le
    ((cloc_input_measurability n hn k hk hkn T hT μ hμ hreg p hp).2 2 two_pos).1
    measurable_const)

/-- **Localization for the `p`-energy**: the statement `exists_p_localization`. -/
theorem cloc_exists_p_localization (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 0 < N ∧ ∀ p : ℝ, 0 < p → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ M : ℝ, 0 ≤ M → Nonempty (PLocalization μ k T p M N) := by
  refine ⟨localizationCount n + 1, Nat.succ_pos _, ?_⟩
  intro p hp k hk hkn T hT μ hμ hreg M hM
  have := hμ
  have := hreg
  have hgood := cloc_measurableSet_pGoodSet hn hk hkn.le hT μ hμ hreg hp M
  have hmeas : ∀ i, MeasurableSet (clocRegion μ k T p M i) := fun i =>
    hgood.inter (measurableSet_localizationCell n i)
  have hfin : ∀ i, IsFiniteMeasure (μ.restrict (clocRegion μ k T p M i)) := fun i =>
    isFiniteMeasure_restrict.mpr
      ((measure_mono (cloc_region_subset_ball μ k T p M i)).trans_lt
        (measure_ball_lt_top μ _ _)).ne
  have hsupp : ∀ i, (μ.restrict (clocRegion μ k T p M i)).support ⊆
      Metric.closedBall (localizationCenter n i) (1 / 64) := fun i =>
    support_restrict_subset_closedBall μ (cloc_region_subset_ball μ k T p M i)
  exact ⟨{
    count := localizationCount n
    count_le := Nat.le_succ _
    region := clocRegion μ k T p M
    measurable := hmeas
    disjoint := fun _ _ hij =>
      (localizationCell_disjoint n hij).mono inter_subset_right inter_subset_right
    cover := cloc_iUnion_region μ k T p M
    center := localizationCenter n
    support_small := hsupp
    finite := hfin
    innerRegular := fun i => by
      have := hfin i
      infer_instance
    energy := fun i => by
      filter_upwards [ae_restrict_mem (hmeas i), Measure.support_mem_ae] with z hzG hzs
      exact cloc_allScale cloc_input_restriction cloc_pTail hn hk hkn.le hT μ hp hM
        (hsupp i) hzs hzG.1.2 }⟩

end ParabolicRectifiability.BetaP
