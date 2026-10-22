import ParabolicRectifiability.Decomposition.Interfaces
import ParabolicRectifiability.Measure.BetaTail

/-! # Good-source localization

Proof of `exists_good_source_localization` (as `goodSourceLocalization_exists`) in
two steps.

* A fixed finite cover of the closed unit ball by open balls of radius
  `1/64`, chosen from the dimension only (before the source, the rank, the family
  and the threshold). It is disjointified in the order of `Fin` and intersected
  with the actual Borel set `thresholdGoodSet μ k T M`. The localized sources are
  the actual restrictions `μ.restrict (region i)`.
* For `ν = μ.restrict (region i)` and `ν`-almost every `z` (which lies both in
  the region and in the topological support of `ν`), restriction lowers the
  `(0,2)` square below `M`, and the exact tail law for the natural beta numbers
  bounds the tail above `2` by the `(1,2)` square, so the all-scale square is at
  most `2 * M`. The scale `2` itself is `scaleMeasure`-null.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-! ## The fixed cover, chosen from the dimension only -/

/-- The closed unit ball is covered by finitely many open balls of radius `1/64`. -/
theorem exists_localization_cover (n : ℕ) :
    ∃ (m : ℕ) (c : Fin m → Space n),
      Metric.closedBall (point (0 : Spatial n) 0) 1 ⊆ ⋃ i, Metric.ball (c i) (1 / 64) := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (point (0 : Spatial n) 0) 1) (by norm_num : (0 : ℝ) < 1 / 64)
  refine ⟨ht.toFinset.card, fun i => (ht.toFinset.equivFin.symm i : Space n), ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcov hx)
  refine mem_iUnion.mpr ⟨ht.toFinset.equivFin ⟨y, ht.mem_toFinset.mpr hy⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hxy

/-- The number of cover balls; it depends on the dimension only. -/
def localizationCount (n : ℕ) : ℕ := (exists_localization_cover n).choose

/-- The fixed centers of the cover balls. -/
def localizationCenter (n : ℕ) : Fin (localizationCount n) → Space n :=
  (exists_localization_cover n).choose_spec.choose

theorem closedBall_subset_iUnion_localizationBall (n : ℕ) :
    Metric.closedBall (point (0 : Spatial n) 0) 1 ⊆
      ⋃ i, Metric.ball (localizationCenter n i) (1 / 64) :=
  (exists_localization_cover n).choose_spec.choose_spec

/-- The fixed disjointified cells, in the order of `Fin`. -/
def localizationCell (n : ℕ) (i : Fin (localizationCount n)) : Set (Space n) :=
  disjointed (fun j => Metric.ball (localizationCenter n j) (1 / 64)) i

theorem localizationCell_subset_ball (n : ℕ) (i : Fin (localizationCount n)) :
    localizationCell n i ⊆ Metric.ball (localizationCenter n i) (1 / 64) :=
  disjointed_subset _ i

theorem measurableSet_localizationCell (n : ℕ) (i : Fin (localizationCount n)) :
    MeasurableSet (localizationCell n i) := by
  rw [localizationCell, disjointed_eq_inter_compl]
  exact measurableSet_ball.inter
    (MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_ball.compl)

theorem localizationCell_disjoint (n : ℕ) {i j : Fin (localizationCount n)} (hij : i ≠ j) :
    Disjoint (localizationCell n i) (localizationCell n j) :=
  disjoint_disjointed _ hij

theorem iUnion_localizationCell (n : ℕ) :
    (⋃ i, localizationCell n i) = ⋃ i, Metric.ball (localizationCenter n i) (1 / 64) :=
  iUnion_disjointed

/-- The actual Borel good set of the original source. -/
theorem measurableSet_thresholdGoodSet {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (T : FamilyKind) (M : ℝ) :
    MeasurableSet (thresholdGoodSet μ k T M) :=
  measurableSet_ball.inter (measurableSet_le (measurable_squareEnergy μ k T 2) measurable_const)

theorem thresholdGoodSet_subset_iUnion_localizationCell {n : ℕ} (μ : Measure (Space n))
    (k : ℕ) (T : FamilyKind) (M : ℝ) :
    thresholdGoodSet μ k T M ⊆ ⋃ i, localizationCell n i := by
  rw [iUnion_localizationCell]
  exact inter_subset_left.trans
    (Metric.ball_subset_closedBall.trans (closedBall_subset_iUnion_localizationBall n))

/-- The localization regions: actual good points in the fixed cells. -/
def localizationRegion {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind) (M : ℝ)
    (i : Fin (localizationCount n)) : Set (Space n) :=
  thresholdGoodSet μ k T M ∩ localizationCell n i

theorem localizationRegion_subset_ball {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (M : ℝ) (i : Fin (localizationCount n)) :
    localizationRegion μ k T M i ⊆ Metric.ball (localizationCenter n i) (1 / 64) :=
  inter_subset_right.trans (localizationCell_subset_ball n i)

theorem measurableSet_localizationRegion {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (T : FamilyKind) (M : ℝ)
    (i : Fin (localizationCount n)) : MeasurableSet (localizationRegion μ k T M i) :=
  (measurableSet_thresholdGoodSet μ k T M).inter (measurableSet_localizationCell n i)

theorem localizationRegion_disjoint {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (M : ℝ) {i j : Fin (localizationCount n)} (hij : i ≠ j) :
    Disjoint (localizationRegion μ k T M i) (localizationRegion μ k T M j) :=
  (localizationCell_disjoint n hij).mono inter_subset_right inter_subset_right

/-- Exact cover of the original good set. -/
theorem iUnion_localizationRegion {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (M : ℝ) :
    (⋃ i, localizationRegion μ k T M i) = thresholdGoodSet μ k T M := by
  simp only [localizationRegion]
  rw [← inter_iUnion]
  exact inter_eq_left.mpr (thresholdGoodSet_subset_iUnion_localizationCell μ k T M)

/-- The topological support of an actual restriction to a set inside an open
ball lies in the closed ball. The region itself need not contain the support. -/
theorem support_restrict_subset_closedBall {n : ℕ} (μ : Measure (Space n))
    {G : Set (Space n)} {c : Space n} {r : ℝ} (hG : G ⊆ Metric.ball c r) :
    (μ.restrict G).support ⊆ Metric.closedBall c r :=
  Measure.support_restrict_subset.trans
    (inter_subset_left.trans ((closure_mono hG).trans Metric.closure_ball_subset_closedBall))

theorem localizationRegion_support_subset {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) (M : ℝ) (i : Fin (localizationCount n)) :
    (μ.restrict (localizationRegion μ k T M i)).support ⊆
      Metric.closedBall (localizationCenter n i) (1 / 64) :=
  support_restrict_subset_closedBall μ (localizationRegion_subset_ball μ k T M i)

theorem isFiniteMeasure_restrict_localizationRegion {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (T : FamilyKind) (M : ℝ)
    (i : Fin (localizationCount n)) :
    IsFiniteMeasure (μ.restrict (localizationRegion μ k T M i)) :=
  isFiniteMeasure_restrict.mpr
    ((measure_mono (localizationRegion_subset_ball μ k T M i)).trans_lt
      (measure_ball_lt_top μ _ _)).ne

theorem innerRegular_restrict_localizationRegion {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegular] (k : ℕ) (T : FamilyKind) (M : ℝ)
    (i : Fin (localizationCount n)) :
    (μ.restrict (localizationRegion μ k T M i)).InnerRegular := by
  have := isFiniteMeasure_restrict_localizationRegion μ k T M i
  infer_instance

/-! ## The all-scale bound through the exact tail law -/

/-- For a restriction whose support lies in a closed ball of radius `1/64`, at a
support point where the original `(0,2)` square is at most `M`, the whole
all-scale square of the restriction is at most `2 * M`. No finiteness of any
energy is assumed; the bound itself is the finiteness. -/
theorem allScaleEnergy_restrict_le_two_mul {n : ℕ} (μ : Measure (Space n)) (k : ℕ)
    (T : FamilyKind) {M : ℝ} (hM : 0 ≤ M) {G : Set (Space n)} {c : Space n}
    (hsupp : (μ.restrict G).support ⊆ Metric.closedBall c (1 / 64))
    {z : Space n} (hz : z ∈ (μ.restrict G).support)
    (hzM : squareEnergy μ k T 2 z ≤ ENNReal.ofReal M) :
    allScaleEnergy (μ.restrict G) k T z ≤ ENNReal.ofReal (2 * M) := by
  set ν := μ.restrict G with hν
  -- the `(0,2)` square of the restriction is at most `M`
  have hlow : ∫⁻ r in Ioo (0 : ℝ) 2, betaSq ν k T z r ∂scaleMeasure ≤ ENNReal.ofReal M :=
    (squareEnergy_restrict_le μ G k T 2 z).trans hzM
  -- compact support of diameter at most `1/32 < 1`
  have hc : IsCompact ν.support :=
    (isCompact_closedBall c (1 / 64)).of_isClosed_subset Measure.isClosed_support hsupp
  have hd : Metric.diam ν.support < 1 :=
    (Metric.diam_mono hsupp Metric.isBounded_closedBall).trans_lt
      ((Metric.diam_closedBall (by norm_num : (0 : ℝ) ≤ 1 / 64)).trans_lt (by norm_num))
  -- the exact tail identity, with factor at most one
  have htail := betaSq_tail_eq_annulus ν k T hc hd hz
  have hpow : (4 : ℝ) ≤ 2 ^ (k + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hfac : (ENNReal.ofReal ((2 : ℝ) ^ (k + 2) - 1))⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.mpr (ENNReal.one_le_ofReal.mpr (by linarith))
  have hhigh : ∫⁻ r in Ioi (2 : ℝ), betaSq ν k T z r ∂scaleMeasure ≤ ENNReal.ofReal M := by
    rw [htail]
    calc
      _ ≤ 1 * ∫⁻ r in Ioo (1 : ℝ) 2, betaSq ν k T z r ∂scaleMeasure := by gcongr
      _ = ∫⁻ r in Ioo (1 : ℝ) 2, betaSq ν k T z r ∂scaleMeasure := one_mul _
      _ ≤ ∫⁻ r in Ioo (0 : ℝ) 2, betaSq ν k T z r ∂scaleMeasure :=
        lintegral_mono_set (Ioo_subset_Ioo_left zero_le_one)
      _ ≤ ENNReal.ofReal M := hlow
  -- split the positive scales at the null endpoint `2`
  have hsplit : Ioi (0 : ℝ) ⊆ Ioo 0 2 ∪ Ici 2 := by
    intro r hr
    by_cases h : r < 2
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr (le_of_not_gt h)
  have hIci : ∫⁻ r in Ici (2 : ℝ), betaSq ν k T z r ∂scaleMeasure = ∫⁻ r in Ioi (2 : ℝ), betaSq ν k T z r ∂scaleMeasure :=
    setLIntegral_congr (Ioi_ae_eq_Ici' (scaleMeasure_singleton 2)).symm
  calc
    allScaleEnergy ν k T z = ∫⁻ r in Ioi (0 : ℝ), betaSq ν k T z r ∂scaleMeasure := rfl
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) 2 ∪ Ici 2, betaSq ν k T z r ∂scaleMeasure := lintegral_mono_set hsplit
    _ ≤ (∫⁻ r in Ioo (0 : ℝ) 2, betaSq ν k T z r ∂scaleMeasure) + ∫⁻ r in Ici (2 : ℝ), betaSq ν k T z r ∂scaleMeasure :=
      lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal M := by
      rw [hIci]
      exact add_le_add hlow hhigh
    _ = ENNReal.ofReal (2 * M) := by rw [two_mul, ENNReal.ofReal_add hM hM]

/-- The all-scale bound for the localized sources: almost every point of the restricted source
lies in its region (hence in the original good set) and in its support. -/
theorem ae_allScaleEnergy_localizationRegion_le {n : ℕ} (μ : Measure (Space n))
    [IsFiniteMeasureOnCompacts μ] (k : ℕ) (T : FamilyKind) {M : ℝ} (hM : 0 ≤ M)
    (i : Fin (localizationCount n)) :
    ∀ᵐ z ∂μ.restrict (localizationRegion μ k T M i),
      allScaleEnergy (μ.restrict (localizationRegion μ k T M i)) k T z ≤
        ENNReal.ofReal (2 * M) := by
  filter_upwards [ae_restrict_mem (measurableSet_localizationRegion μ k T M i),
    Measure.support_mem_ae] with z hzG hzs
  exact allScaleEnergy_restrict_le_two_mul μ k T hM
    (localizationRegion_support_subset μ k T M i) hzs hzG.1.2

/-! ## Assembly -/

/-- The localization built from the fixed cover, for an actual Radon source. -/
def goodSourceLocalization {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegular] (k : ℕ) (T : FamilyKind) {M : ℝ} (hM : 0 ≤ M) :
    GoodSourceLocalization μ k T M (localizationCount n + 1) where
  count := localizationCount n
  count_le := Nat.le_succ _
  region := localizationRegion μ k T M
  measurable := measurableSet_localizationRegion μ k T M
  disjoint := fun _ _ hij => localizationRegion_disjoint μ k T M hij
  cover := iUnion_localizationRegion μ k T M
  center := localizationCenter n
  support_small := localizationRegion_support_subset μ k T M
  finite := isFiniteMeasure_restrict_localizationRegion μ k T M
  innerRegular := innerRegular_restrict_localizationRegion μ k T M
  energy := ae_allScaleEnergy_localizationRegion_le μ k T hM

/-- Finite good-source localization: the statement
`exists_good_source_localization`. The count bound `N` depends on `n` only. -/
theorem goodSourceLocalization_exists :
    ∀ n : ℕ, 1 ≤ n →
      ∃ N : ℕ, 0 < N ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
        ∀ T : FamilyKind, Nonempty (Models n k T) →
        ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
        ∀ M : ℝ, 0 ≤ M → Nonempty (GoodSourceLocalization μ k T M N) := by
  intro n _
  refine ⟨localizationCount n + 1, Nat.succ_pos _, ?_⟩
  intro k _ _ T _ μ hμ hreg M hM
  exact ⟨goodSourceLocalization μ k T hM⟩

end ParabolicRectifiability
