import ParabolicRectifiability.Decomposition.AmbientEndpoint

/-! # The loss-free zero-threshold assembly

This module proves the zero-threshold case of the decomposition theorem. Each localized source `μ|region i` has its whole
compact support in one attained admissible model. That support is retained
in full as a piece of the model's own type, so no source mass is lost and the
only remainder cost is the original bad set `Γ`, with coefficient one.

* **Graphs.** A horizontal model is the graph of the zero normal map and the
  constant time function over its whole spatial direction. A vertical model is
  the full regular vertical graph of the zero function. Both serve every
  positive tolerance.
* **Content.** Orthonormal coordinates make each model an isometric copy of
  `ℝ^k` (horizontal) or of the parabolic space `Space (k - 2)` (vertical). The
  isometric-model bounds (`content_of_isometry`) then give all
  content and packing bounds for a support inside a closed ball of radius
  `1/64`, with a constant depending only on `n` and `k`; summing over
  `k ≤ n + 2` gives one constant depending only on `n`.
* **Assembly.** The finite source assembly is applied with `N + 1` pieces (so `N = 0` is harmless) and zero piece loss.
  The resulting constant depends only on `n` and `N` and is chosen before
  `k, T, μ, Γ, S`.
-/

noncomputable section
open MeasureTheory Set Module
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-! ### Monotonicity in the constant -/

theorem HasMetricContentBounds.mono {n k : ℕ} {C C' : ℝ} {K : Set (Space n)}
    (h : HasMetricContentBounds k C K) (hC : C ≤ C') : HasMetricContentBounds k C' K where
  hausdorff q R hR hR1 := (h.hausdorff q R hR hR1).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hR.le k)))
  separated q R r hR hR1 hr hrR F hF hsep := (h.separated q R r hR hR1 hr hrR F hF hsep).trans
    (mul_le_mul_of_nonneg_right hC (pow_nonneg (div_nonneg hR.le hr.le) k))
  minkowski r hr hr1 := (h.minkowski r hr hr1).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hr.le _)))

theorem HasFiniteBallPacking.mono {n k : ℕ} {C C' : ℝ} {K : Set (Space n)}
    (h : HasFiniteBallPacking k C K) (hC : C ≤ C') : HasFiniteBallPacking k C' K :=
  fun q R hR hR1 l z r hz hr hd => (h q R hR hR1 l z r hz hr hd).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC (pow_nonneg hR.le k)))

/-! ### Orthonormal charts of affine spatial planes -/

namespace AffineSpatialPlane

variable {n m : ℕ}

/-- Orthonormal coordinates on the direction, translated to the anchor. -/
def chart (P : AffineSpatialPlane n m) (y : Spatial (finrank ℝ P.direction)) : Spatial n :=
  P.anchor + ((subspaceCoordinates P.direction).symm y : Spatial n)

theorem isometry_chart (P : AffineSpatialPlane n m) : Isometry P.chart := by
  refine Isometry.of_dist_eq fun y y' => ?_
  rw [chart, chart, dist_add_left]
  exact (isometry_subtype_coe.comp (subspaceCoordinates P.direction).symm.isometry).dist_eq y y'

theorem exists_chart_eq (P : AffineSpatialPlane n m) {x : Spatial n} (hx : x ∈ P.toSet) :
    ∃ y, P.chart y = x := by
  refine ⟨subspaceCoordinates P.direction ⟨x - P.anchor, hx⟩, ?_⟩
  rw [chart, LinearIsometryEquiv.symm_apply_apply]
  show P.anchor + (x - P.anchor) = x
  abel

end AffineSpatialPlane

/-! ### Horizontal models -/

namespace HorizontalModel

variable {n k : ℕ}

/-- The model as an isometric copy of `ℝ^k` at the model time. -/
def chart (L : HorizontalModel n k) (y : Spatial (finrank ℝ L.spatial.direction)) : Space n :=
  point (L.spatial.chart y) L.time

theorem isometry_chart (L : HorizontalModel n k) : Isometry L.chart := by
  refine Isometry.of_dist_eq fun y y' => ?_
  rw [chart, chart, dist_point, sub_self, abs_zero, Real.sqrt_zero, ← dist_eq_norm,
    L.spatial.isometry_chart.dist_eq]
  exact max_eq_left dist_nonneg

theorem toSet_subset_range_chart (L : HorizontalModel n k) : L.toSet ⊆ range L.chart := by
  intro z hz
  obtain ⟨y, hy⟩ := L.spatial.exists_chart_eq hz.1
  refine ⟨y, ?_⟩
  rw [chart, hy, ← hz.2]
  rfl

/-- The model is the graph of the zero normal map and constant time over the
whole spatial direction, at every nonnegative tolerance. -/
theorem hasHorizontalGraphCover (L : HorizontalModel n k) {K : Set (Space n)}
    (hK : K ⊆ L.toSet) {ε : ℝ} (hε : 0 ≤ ε) : HasHorizontalGraphCover k K ε := by
  let G : HorizontalGraph n k ε :=
    { direction := L.spatial.direction
      rank_eq := L.spatial.rank_eq
      domain := univ
      offset := L.spatial.anchor
      normal := fun _ => 0
      time := fun _ => L.time
      small_slope := fun u v => by
        simp only [sub_self, norm_zero, abs_zero, Real.sqrt_zero, max_self]
        exact mul_nonneg hε (norm_nonneg _) }
  have hcov : K ⊆ G.image := by
    intro z hz
    have hz' := hK hz
    refine ⟨⟨⟨z.1 - L.spatial.anchor, hz'.1⟩, mem_univ _⟩, ?_⟩
    show point (L.spatial.anchor + (z.1 - L.spatial.anchor) +
      ((0 : L.spatial.directionᗮ) : Spatial n)) L.time = z
    rw [Submodule.coe_zero, add_zero, add_sub_cancel, ← hz'.2]
    rfl
  exact ⟨{0}, fun _ => G, measure_mono_null
    (fun x hx => (hx.2 (mem_iUnion.mpr ⟨⟨0, rfl⟩, hcov hx.1⟩)).elim) measure_empty⟩

end HorizontalModel

/-! ### Vertical models -/

namespace VerticalModel

variable {n k : ℕ}

/-- The model as an isometric copy of the parabolic space of its spatial rank. -/
def chart (L : VerticalModel n k) (y : Space (finrank ℝ L.spatial.direction)) : Space n :=
  (L.spatial.chart y.1, y.2)

theorem isometry_chart (L : VerticalModel n k) : Isometry L.chart :=
  L.spatial.isometry_chart.prodMap isometry_id

theorem toSet_subset_range_chart (L : VerticalModel n k) : L.toSet ⊆ range L.chart := by
  intro z hz
  obtain ⟨y, hy⟩ := L.spatial.exists_chart_eq hz
  refine ⟨(y, z.2), ?_⟩
  show (L.spatial.chart y, z.2) = z
  rw [hy]

/-- The model is the full regular vertical graph of the zero function. -/
theorem hasRegularVerticalGraphCover (L : VerticalModel n k) {K : Set (Space n)}
    (hK : K ⊆ L.toSet) {ε : ℝ} (hε : 0 ≤ ε) : HasRegularVerticalGraphCover k K ε := by
  let G : RegularVerticalGraph n k ε :=
    { vertical_dimension := L.two_le
      direction := L.spatial.direction
      rank_eq := by rw [L.spatial.rank_eq, L.rank_eq]
      offset := L.spatial.anchor
      function := fun _ => 0
      regular := isRegularVerticalFunction_zero _ hε }
  have hcov : K ⊆ G.image := by
    intro z hz
    refine ⟨(⟨z.1 - L.spatial.anchor, hK hz⟩, z.2), ?_⟩
    show (L.spatial.anchor + (z.1 - L.spatial.anchor) +
      ((0 : L.spatial.directionᗮ) : Spatial n), z.2) = z
    rw [Submodule.coe_zero, add_zero, add_sub_cancel]
  exact ⟨{0}, fun _ => G, measure_mono_null
    (fun x hx => (hx.2 (mem_iUnion.mpr ⟨⟨0, rfl⟩, hcov hx.1⟩)).elim) measure_empty⟩

end VerticalModel

/-! ### Content of flat supports -/

/-- One constant for every flat model of dimension `k` in `Space n`. -/
def flatModelConstant (n k : ℕ) : ℝ :=
  isometricModelConstant n k (horizontalHausdorffConstant k * omega k) +
    isometricModelConstant n k (verticalHausdorffConstant (k - 2) * (2 * omega (k - 2)))

theorem flatModelConstant_nonneg (n k : ℕ) : 0 ≤ flatModelConstant n k :=
  add_nonneg (isometricModelConstant_nonneg _ _ _) (isometricModelConstant_nonneg _ _ _)

theorem HorizontalModel.content {n k : ℕ} (L : HorizontalModel n k) {K : Set (Space n)}
    {c : Space n} (hK : K ⊆ L.toSet) (hKc : K ⊆ Metric.closedBall c 1) :
    HasMetricContentBounds k (flatModelConstant n k) K ∧
      HasFiniteBallPacking k (flatModelConstant n k) K := by
  have hdim : finrank ℝ L.spatial.direction ≤ n + 2 :=
    (Submodule.finrank_le L.spatial.direction).trans (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨h1, h2⟩ := content_of_isometry (ν := (volume : Measure (Spatial _)))
    (omega_pos _).ne' (omega_lt_top _).ne (fun x r hr => volume_spatial_ball x hr)
    (fun E => (spatial_hausdorff_comparison _ E).2) (horizontalHausdorffConstant_lt_top _).ne
    L.isometry_chart (hK.trans L.toSet_subset_range_chart) hKc hdim
  rw [L.spatial.rank_eq] at h1 h2
  have hle : isometricModelConstant n k (horizontalHausdorffConstant k * omega k) ≤
      flatModelConstant n k :=
    le_add_of_nonneg_right (isometricModelConstant_nonneg _ _ _)
  exact ⟨h1.mono hle, h2.mono hle⟩

theorem VerticalModel.content {n k : ℕ} (L : VerticalModel n k) {K : Set (Space n)}
    {c : Space n} (hK : K ⊆ L.toSet) (hKc : K ⊆ Metric.closedBall c 1) :
    HasMetricContentBounds k (flatModelConstant n k) K ∧
      HasFiniteBallPacking k (flatModelConstant n k) K := by
  have hdim : finrank ℝ L.spatial.direction + 2 ≤ n + 2 := by
    have := Submodule.finrank_le L.spatial.direction
    rw [finrank_euclideanSpace_fin] at this
    omega
  obtain ⟨h1, h2⟩ := content_of_isometry
    (ν := parabolicVolume (finrank ℝ L.spatial.direction))
    (ENNReal.mul_pos (by norm_num) (omega_pos _).ne').ne'
    (ENNReal.mul_ne_top (by norm_num) (omega_lt_top _).ne)
    (fun y r hr => parabolicVolume_ball y r hr)
    (fun E => (parabolic_hausdorff_comparison _ E).2) (verticalHausdorffConstant_lt_top _).ne
    L.isometry_chart (hK.trans L.toSet_subset_range_chart) hKc hdim
  have hrank : L.spatialRank = k - 2 := by have := L.rank_eq; omega
  rw [L.spatial.rank_eq, L.rank_eq, hrank] at h1 h2
  have hle : isometricModelConstant n k
      (verticalHausdorffConstant (k - 2) * (2 * omega (k - 2))) ≤ flatModelConstant n k :=
    le_add_of_nonneg_left (isometricModelConstant_nonneg _ _ _)
  exact ⟨h1.mono hle, h2.mono hle⟩

/-- Content and packing for a bounded subset of any admissible model of the family. -/
theorem modelSet_content {n k : ℕ} {T : FamilyKind} (L : Models n k T) {K : Set (Space n)}
    {c : Space n} (hK : K ⊆ modelSet L) (hKc : K ⊆ Metric.closedBall c 1) :
    HasMetricContentBounds k (flatModelConstant n k) K ∧
      HasFiniteBallPacking k (flatModelConstant n k) K := by
  cases T with
  | horizontal => exact HorizontalModel.content L hK hKc
  | vertical => exact VerticalModel.content L hK hKc
  | mixed =>
    cases L with
    | inl L => exact HorizontalModel.content L hK hKc
    | inr L => exact VerticalModel.content L hK hKc

/-! ### Typed pieces retaining the whole localized source -/

/-- Retain the whole support of a source lying in a horizontal model. -/
def horizontalFlatPieces {n k : ℕ} (ν : Measure (Space n)) (L : HorizontalModel n k)
    (T : FamilyKind) (hT : T ≠ .vertical) (hL : ν.support ⊆ L.toSet)
    (hc : IsCompact ν.support) : CompactTypedPieces ν k T 0 1 ν.support where
  horizontal := ν.support
  vertical := ∅
  horizontal_compact := hc
  vertical_compact := isCompact_empty
  horizontal_subset := Subset.rfl
  vertical_subset := empty_subset _
  disjoint := disjoint_empty _
  loss := by
    rw [union_empty, Measure.measure_compl_support]
    exact zero_le
  horizontal_unavailable := fun h => (h (HorizontalModel.nonempty_iff.mp ⟨L⟩)).elim
  vertical_unavailable := fun _ => rfl
  family := ⟨fun _ => rfl, fun h => absurd h hT⟩
  horizontal_graphs := fun _ hε => L.hasHorizontalGraphCover hL hε.le
  vertical_graphs := fun _ _ => ⟨∅, fun i => absurd i.2 (notMem_empty _), by simp⟩

/-- Retain the whole support of a source lying in a vertical model. -/
def verticalFlatPieces {n k : ℕ} (ν : Measure (Space n)) (L : VerticalModel n k)
    (T : FamilyKind) (hT : T ≠ .horizontal) (hL : ν.support ⊆ L.toSet)
    (hc : IsCompact ν.support) : CompactTypedPieces ν k T 0 1 ν.support where
  horizontal := ∅
  vertical := ν.support
  horizontal_compact := isCompact_empty
  vertical_compact := hc
  horizontal_subset := empty_subset _
  vertical_subset := Subset.rfl
  disjoint := empty_disjoint _
  loss := by
    rw [empty_union, Measure.measure_compl_support]
    exact zero_le
  horizontal_unavailable := fun _ => rfl
  vertical_unavailable := fun h => (h (VerticalModel.nonempty_iff.mp ⟨L⟩)).elim
  family := ⟨fun h => absurd h hT, fun _ => rfl⟩
  horizontal_graphs := fun _ _ => ⟨∅, fun i => absurd i.2 (notMem_empty _), by simp⟩
  vertical_graphs := fun _ hε => L.hasRegularVerticalGraphCover hL hε.le

theorem nonempty_flatPieces {n k : ℕ} {T : FamilyKind} (ν : Measure (Space n))
    (L : Models n k T) (hL : ν.support ⊆ modelSet L) (hc : IsCompact ν.support) :
    Nonempty (CompactTypedPieces ν k T 0 1 ν.support) := by
  cases T with
  | horizontal => exact ⟨horizontalFlatPieces ν L .horizontal (by decide) hL hc⟩
  | vertical => exact ⟨verticalFlatPieces ν L .vertical (by decide) hL hc⟩
  | mixed =>
    cases L with
    | inl L => exact ⟨horizontalFlatPieces ν L .mixed (by decide) hL hc⟩
    | inr L => exact ⟨verticalFlatPieces ν L .mixed (by decide) hL hc⟩

/-! ### The zero-threshold assembly constant -/

/-- The statement of `exists_flat_assembly_constant`. The constant is `(N + 1) (1 + 2F)`, where `F` bounds the flat-model constants
for all `k ≤ n + 2`; it is chosen before `k, T, μ, Γ, S`. -/
theorem flatAssemblyConstant_proof (n : ℕ) (_hn : 1 ≤ n) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, Nonempty (Models n k T) →
      ∀ μ : Measure (Space n), IsFiniteMeasureOnCompacts μ → μ.InnerRegular →
      ∀ Γ : ℝ, 0 ≤ Γ →
      μ (Metric.ball (point 0 0) 1 ∩
        {z | 0 < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ →
      ∀ S : GoodSourceLocalization μ k T 0 N,
      (∀ i, ∃ L : Models n k T, (μ.restrict (S.region i)).support ⊆ modelSet L) →
      HasFamilyDecomposition k T C 0 Γ μ := by
  set F : ℝ := ∑ j ∈ Finset.range (n + 3), flatModelConstant n j + 1
  have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 3), flatModelConstant n j :=
    Finset.sum_nonneg fun j _ => flatModelConstant_nonneg n j
  have hF : 0 < F := by positivity
  refine ⟨((N + 1 : ℕ) : ℝ) * (1 + F + F), by positivity, ?_⟩
  intro k hk hkn T _ μ hμ hreg Γ hΓ hbad S hmodel
  have hkF : flatModelConstant n k ≤ F :=
    (Finset.single_le_sum (fun j _ => flatModelConstant_nonneg n j)
      (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_right zero_le_one)
  let S' : GoodSourceLocalization μ k T 0 (N + 1) :=
    { S with count_le := S.count_le.trans (Nat.le_succ N) }
  have hbad' : μ (Metric.ball (point 0 0) 1 ∩
      {z | ENNReal.ofReal 0 < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ := by
    rwa [ENNReal.ofReal_zero]
  have hsmall : ∀ i, (μ.restrict (S.region i)).support ⊆ Metric.closedBall (S.center i) 1 :=
    fun i => (S.support_small i).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hcompact : ∀ i, IsCompact (μ.restrict (S.region i)).support := fun i =>
    (isCompact_closedBall _ _).of_isClosed_subset Measure.isClosed_support (S.support_small i)
  choose L hL using hmodel
  have hcontent := fun i => modelSet_content (L i) (hL i) (hsmall i)
  exact familyDecomposition_of_compactSources hk hkn (Nat.succ_pos N) T μ hμ hreg 0 Γ 1 F F
    le_rfl hΓ one_pos hF hF hbad' S' (fun i => (μ.restrict (S.region i)).support)
    (fun i => (nonempty_flatPieces _ (L i) (hL i) (hcompact i)).some)
    (fun i => ((hcontent i).1.mono hkF)) (fun i => ((hcontent i).2.mono hkF))

end ParabolicRectifiability
