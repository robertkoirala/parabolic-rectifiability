import ParabolicRectifiability.Measure.Neck.ConstructionConclusions
import ParabolicRectifiability.Geometry.CovarianceComparison

/-!
# Elementary facts about the source construction

Helper lemmas for the plane comparison, the fitted-time comparison, the genuine and full
record time compatibility and the finite ambient square:

* the parabolic distance in coordinates, and the spatial and time parts of the distance to
  a lower model set `T.lowerModelSet L τ`;
* the fitting error at a positive radius as `r^{k+2} b_ν`;
* the kept sets `S_j` of `ConstructionData`: monotonicity, containment in `S`, and the kept
  pieces (a kept point of stage `j ≥ 1` lies within `κ r_j` of a continuing candidate and
  within `θ r_j` of its fitted model); candidates and terminal centers enter from `S_{j-1}`;
* the scales `r_j` and the levels of the coherent family of the construction.

Every declaration carries the prefix `ms3_`.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Parabolic distance in coordinates -/

theorem ms3_dist_eq {n : ℕ} (z w : Space n) :
    dist z w = max ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) := by
  rcases z with ⟨x, ⟨t⟩⟩
  rcases w with ⟨y, ⟨s⟩⟩
  exact dist_point x y t s

theorem ms3_norm_sub_le_dist {n : ℕ} (z w : Space n) : ‖z.1 - w.1‖ ≤ dist z w := by
  rw [ms3_dist_eq]
  exact le_max_left _ _

theorem ms3_abs_time_le_dist_sq {n : ℕ} (z w : Space n) :
    |z.2.val - w.2.val| ≤ dist z w ^ 2 := by
  have h : Real.sqrt |z.2.val - w.2.val| ≤ dist z w := by
    rw [ms3_dist_eq]
    exact le_max_right _ _
  exact (Real.sqrt_le_left dist_nonneg).1 h

theorem ms3_dist_le_of {n : ℕ} {z w : Space n} {r : ℝ} (hr : 0 ≤ r) (h1 : ‖z.1 - w.1‖ ≤ r)
    (h2 : |z.2.val - w.2.val| ≤ r ^ 2) : dist z w ≤ r := by
  rw [ms3_dist_eq]
  exact max_le h1 ((Real.sqrt_le_left hr).2 h2)

theorem ms3_dist_sq_eq {n : ℕ} (z w : Space n) :
    dist z w ^ 2 = max (‖z.1 - w.1‖ ^ 2) |z.2.val - w.2.val| := by
  rw [ms3_dist_eq]
  rcases le_total ‖z.1 - w.1‖ (Real.sqrt |z.2.val - w.2.val|) with h | h
  · rw [max_eq_right h, Real.sq_sqrt (abs_nonneg _), max_eq_right]
    calc ‖z.1 - w.1‖ ^ 2 ≤ Real.sqrt |z.2.val - w.2.val| ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = |z.2.val - w.2.val| := Real.sq_sqrt (abs_nonneg _)
  · rw [max_eq_left h, max_eq_left]
    calc |z.2.val - w.2.val| = Real.sqrt |z.2.val - w.2.val| ^ 2 :=
          (Real.sq_sqrt (abs_nonneg _)).symm
      _ ≤ ‖z.1 - w.1‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-! ## Distances to lower model sets -/

theorem ms3_ofReal_sqrt_time_le_infEDist {n m : ℕ} (L : AffineSpatialPlane n m) (τ : ℝ)
    (z : Space n) :
    ENNReal.ofReal (Real.sqrt |z.2.val - τ|) ≤
      Metric.infEDist z (NeckType.horizontal.lowerModelSet L τ) := by
  refine Metric.le_infEDist.2 fun y hy => ?_
  have hy' : y.1 ∈ L.toSet ∧ y.2.val = τ := hy
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [ms3_dist_eq, ← hy'.2]
  exact le_max_right _ _

theorem ms3_abs_time_sub_le {n m : ℕ} (L : AffineSpatialPlane n m) (τ : ℝ) (z : Space n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : Metric.infEDist z (NeckType.horizontal.lowerModelSet L τ) ≤ ENNReal.ofReal ε) :
    |z.2.val - τ| ≤ ε ^ 2 := by
  have h1 := (ms3_ofReal_sqrt_time_le_infEDist L τ z).trans h
  rw [ENNReal.ofReal_le_ofReal_iff hε] at h1
  exact (Real.sqrt_le_left hε).1 h1

theorem ms3_ofReal_abs_time_le_sq {n m : ℕ} (L : AffineSpatialPlane n m) (τ : ℝ)
    (z : Space n) :
    ENNReal.ofReal |z.2.val - τ| ≤
      Metric.infEDist z (NeckType.horizontal.lowerModelSet L τ) ^ 2 := by
  have h := ms3_ofReal_sqrt_time_le_infEDist L τ z
  calc ENNReal.ofReal |z.2.val - τ| = ENNReal.ofReal (Real.sqrt |z.2.val - τ|) ^ 2 := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (abs_nonneg _)]
    _ ≤ _ := by gcongr

theorem ms3_ofReal_spatial_sq_le {n m : ℕ} (T : NeckType) (L : AffineSpatialPlane n m)
    (τ : ℝ) (z : Space n) :
    ENNReal.ofReal (‖z.1 - L.projection z.1‖ ^ 2) ≤
      Metric.infEDist z (T.lowerModelSet L τ) ^ 2 := by
  have h : ENNReal.ofReal ‖z.1 - L.projection z.1‖ ≤
      Metric.infEDist z (T.lowerModelSet L τ) := by
    refine Metric.le_infEDist.2 fun y hy => ?_
    have hy1 : y.1 ∈ L.toSet := by
      cases T with
      | horizontal => exact (show y.1 ∈ L.toSet ∧ y.2.val = τ from hy).1
      | vertical => exact (show y.1 ∈ L.toSet from hy)
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal ((L.nearest z.1 hy1).trans (ms3_norm_sub_le_dist z y))
  rw [ENNReal.ofReal_pow (norm_nonneg _)]
  gcongr

/-! ## Fitting errors at positive radius -/

theorem ms3_typeFittingError_eq {n : ℕ} (ν : Measure (Space n)) (k : ℕ) (F : FamilyKind)
    (x : Space n) {r : ℝ} (hr : 0 < r) :
    typeFittingError ν k F x r = ENNReal.ofReal r ^ (k + 2) * betaSq ν k F x r := by
  rw [betaSq_of_pos ν k F x hr, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top, one_pow,
    one_mul]
  rfl

/-! ## Scales -/

namespace SourceSetup

variable {n : ℕ}

theorem ms3_scale_succ (P : SourceSetup n) (T : NeckType) (j : ℕ) :
    P.scale T (j + 1) = P.scale T j / 10 := by
  unfold SourceSetup.scale coherentScale
  rw [pow_succ, div_div]

theorem ms3_scale_zero (P : SourceSetup n) (T : NeckType) :
    P.scale T 0 = T.rootRadius P.R := by
  unfold SourceSetup.scale coherentScale
  rw [pow_zero, div_one]

theorem ms3_scale_anti (P : SourceSetup n) (T : NeckType) (hR : 0 < P.R) {i j : ℕ}
    (h : i ≤ j) : P.scale T j ≤ P.scale T i :=
  div_le_div_of_nonneg_left (T.rootRadius_pos hR).le (pow_pos (by norm_num) i)
    (pow_le_pow_right₀ (by norm_num) h)

theorem ms3_scale_tendsto (P : SourceSetup n) (T : NeckType) :
    Tendsto (fun m : ℕ => P.scale T (m + 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => T.rootRadius P.R / 10 ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact h.comp (tendsto_add_atTop_nat 1)

end SourceSetup

theorem NeckType.ms3_four_le_rootRadius (T : NeckType) {R : ℝ} (hR : 0 ≤ R) :
    4 * R ≤ T.rootRadius R := by
  cases T
  · show 4 * R ≤ 8 * R
    linarith
  · show 4 * R ≤ 4 * R
    exact le_rfl

/-! ## The kept sets of the construction -/

namespace ConstructionData

variable {n k : ℕ} {T : NeckType} (D : ConstructionData n k T) (P : SourceSetup n)

theorem ms3_afterTerm_subset (j : ℕ) (E : Set (Space n)) : D.afterTerm P j E ⊆ E :=
  sdiff_subset

theorem ms3_afterColl_subset (j : ℕ) (E : Set (Space n)) : D.afterColl P j E ⊆ E :=
  fun _ hz => D.ms3_afterTerm_subset P j E hz.1

theorem ms3_keptPiece_subset (j : ℕ) (E : Set (Space n)) (i : ℕ) :
    D.keptPiece P j E i ⊆ E :=
  fun _ hz => D.ms3_afterColl_subset P j E hz.1.1

theorem ms3_stageKept_subset (j : ℕ) (E : Set (Space n)) : D.stageKept P j E ⊆ E := by
  intro z hz
  simp only [stageKept, mem_iUnion] at hz
  obtain ⟨i, -, hzi⟩ := hz
  exact D.ms3_keptPiece_subset P j E i hzi

theorem ms3_kept_succ_subset (j : ℕ) : D.kept P (j + 1) ⊆ D.kept P j :=
  fun _ hz => D.ms3_stageKept_subset P (j + 1) (D.kept P j) hz

theorem ms3_kept_anti {i j : ℕ} (h : i ≤ j) : D.kept P j ⊆ D.kept P i :=
  (antitone_nat_of_succ_le (f := D.kept P) fun j => D.ms3_kept_succ_subset P j) h

theorem ms3_kept_subset_S (j : ℕ) : D.kept P j ⊆ P.S :=
  (D.ms3_kept_anti P (Nat.zero_le j)).trans fun _ hz => hz.1

theorem ms3_kept_zero_infEDist {z : Space n} (hz : z ∈ D.kept P 0) :
    Metric.infEDist z D.rootModel ≤ ENNReal.ofReal (P.θ * P.R) :=
  hz.2

theorem ms3_mem_contIndex {j i : ℕ} :
    i ∈ D.contIndex P j ↔ i < D.candCount j ∧ D.IsContinuing P j i := by
  simp only [contIndex, Finset.mem_filter, Finset.mem_range]

/-- A kept point of stage `j + 1` lies within `κ r_{j+1}` of a continuing candidate of that
stage and within `θ r_{j+1}` of its fitted model. -/
theorem ms3_mem_kept_succ {j : ℕ} {z : Space n} (hz : z ∈ D.kept P (j + 1)) :
    ∃ i ∈ D.contIndex P (j + 1),
      dist z (D.cand (j + 1) i) < T.sourceSeparation * P.scale T (j + 1) ∧
        Metric.infEDist z (D.modelSet (j + 1) i) ≤
          ENNReal.ofReal (P.θ * P.scale T (j + 1)) := by
  have hz' : z ∈ D.stageKept P (j + 1) (D.kept P j) := hz
  simp only [stageKept, mem_iUnion] at hz'
  obtain ⟨i, ⟨hi, hcont⟩, hzi⟩ := hz'
  refine ⟨i, (D.ms3_mem_contIndex P).2 ⟨hi, hcont⟩, ?_, hzi.2⟩
  exact hzi.1.2.1

theorem ms3_cand_mem_kept (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ}
    (hi : i < D.candCount j) : D.cand j i ∈ D.kept P (j - 1) :=
  D.ms3_afterTerm_subset P j _ (hD.cand_mem j hj i hi)

theorem ms3_term_mem_kept (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ}
    (hi : i < D.termCount j) : D.term j i ∈ D.kept P (j - 1) :=
  (hD.term_mem j hj i hi).1

theorem ms3_cand_mem_S (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ}
    (hi : i < D.candCount j) : D.cand j i ∈ P.S :=
  D.ms3_kept_subset_S P (j - 1) (D.ms3_cand_mem_kept P hD hj hi)

theorem ms3_cand_cutoff_lt (hD : D.IsSourceConstruction P) {j : ℕ} (hj : 1 ≤ j) {i : ℕ}
    (hi : i < D.candCount j) : P.f (D.cand j i) < P.scale T j :=
  hD.term_done j hj _ (hD.cand_mem j hj i hi)

/-- The spatial fitting integral of a fitted plane on its fitting ball is at most
`(40 r_j)^{k+2} b_ν(g, 40 r_j)` (attained fit of the original source). -/
theorem ms3_spatialFit_le (hD : D.IsSourceConstruction P) (hR : 0 < P.R) {j : ℕ}
    (hj : 1 ≤ j) {i : ℕ} (hi : i < D.candCount j) :
    spatialFittingIntegral (P.ν.restrict (Metric.ball (D.cand j i) (40 * P.scale T j)))
        (D.plane j i) ≤
      ENNReal.ofReal (40 * P.scale T j) ^ (k + 2) *
        betaSq P.ν k T.toFamilyKind (D.cand j i) (40 * P.scale T j) := by
  have hr : 0 < 40 * P.scale T j := by
    have := P.scale_pos T hR j
    linarith
  rw [← ms3_typeFittingError_eq _ _ _ _ hr]
  refine le_trans ?_ (hD.fit_minimal j hj i hi)
  exact lintegral_mono fun z => ms3_ofReal_spatial_sq_le T (D.plane j i) (D.time j i) z

/-- The global spatial fitting integral of the root plane is at most the global error. -/
theorem ms3_rootFit_le :
    spatialFittingIntegral P.ν D.rootPlane ≤ ∫⁻ z, Metric.infEDist z D.rootModel ^ 2 ∂P.ν :=
  lintegral_mono fun z => ms3_ofReal_spatial_sq_le T D.rootPlane D.rootTime z

/-! ## The coherent family of the construction -/

theorem ms3_family_index_zero (hR : 0 < P.R) : (D.family P hR).index 0 = {0} := rfl

theorem ms3_family_index_pos (hR : 0 < P.R) {j : ℕ} (hj : j ≠ 0) :
    (D.family P hR).index j = D.contIndex P j := ite_eq_right hj

theorem ms3_family_center_zero (hR : 0 < P.R) (a : ℕ) :
    (D.family P hR).center 0 a = D.rootCenter := rfl

theorem ms3_family_center_pos (hR : 0 < P.R) {j : ℕ} (hj : j ≠ 0) (a : ℕ) :
    (D.family P hR).center j a = D.cand j a := ite_eq_right hj

theorem ms3_family_plane_zero (hR : 0 < P.R) (a : ℕ) :
    (D.family P hR).plane 0 a = D.rootPlane := rfl

theorem ms3_family_plane_pos (hR : 0 < P.R) {j : ℕ} (hj : j ≠ 0) (a : ℕ) :
    (D.family P hR).plane j a = D.plane j a := ite_eq_right hj

theorem ms3_family_scale (hR : 0 < P.R) (j : ℕ) :
    (D.family P hR).scale j = P.scale T j := rfl

theorem ms3_family_initialPlane (hR : 0 < P.R) :
    (D.family P hR).initialPlane = D.rootPlane := rfl

end ConstructionData

end ParabolicRectifiability
