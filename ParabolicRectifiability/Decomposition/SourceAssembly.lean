import ParabolicRectifiability.Decomposition.Interfaces

/-! # Finite assembly of localized compact sources

This module proves the finite measure bookkeeping of the positive-threshold case
of the decomposition theorem. The original source is restricted to the sets
`region i ∩ A_T i`, where `A_T i` are compact typed pieces of the localized
source `μ|region i`; the compact pieces alone are not used as retained sets,
because a compact piece may carry source mass outside its own region.

* **Retained sets.** The horizontal and vertical retained sets are the finite
  unions of `region i ∩ horizontal i` and `region i ∩ vertical i`. They are
  Borel, disjoint (the regions are disjoint and each pair of pieces is
  disjoint) and lie in the open unit ball.
* **Remainder.** In the unit ball, a point outside both retained sets is either
  in the bad set or in some region outside that region's pieces. The bad set
  contributes the original `Γ` with coefficient one; each region contributes
  its piece loss.
* **Supports.** The support of a restriction lies in the closure of the set,
  hence in the finite union of the compact pieces and in the closed unit ball.
* **Graph covers and content.** Graph covers with Hausdorff-null exceptions,
  metric content, separated sets, Minkowski neighbourhoods and finite packing
  pass to subsets of finite unions with the constant multiplied by the number
  of pieces. Countable packing follows from finite partial sums.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-! ### Countable re-indexing and unions of null-exception covers -/

/-- A countable family has a re-indexing by a subset of the naturals with the
same union of images. Empty families give the empty index set. -/
theorem exists_setNat_iUnion_eq {α X ι : Type*} [Countable ι] (img : α → Set X)
    (f : ι → α) : ∃ (I : Set ℕ) (g : I → α), (⋃ j, img (g j)) = ⋃ i, img (f i) := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  refine ⟨Set.range e, fun m => f (Classical.choose (Set.mem_range.mp m.2)), ?_⟩
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨_, hj⟩
  · rintro ⟨i, hi⟩
    refine ⟨⟨e i, Set.mem_range_self i⟩, ?_⟩
    have key : ∀ h : ∃ j, e j = e i, f (Classical.choose h) = f i :=
      fun h => congrArg f (he (Classical.choose_spec h))
    show z ∈ img (f (Classical.choose (Set.mem_range.mp (Set.mem_range_self (f := e) i))))
    rw [key]
    exact hi

/-- Null-exception covers indexed by subsets of the naturals pass from a
countable family of sets to every subset of their union. -/
theorem exists_setNat_null_cover {α X ι : Type*} [MeasurableSpace X] [Countable ι]
    (m : Measure X) (img : α → Set X) {L : Set X} (K : ι → Set X)
    (hL : L ⊆ ⋃ i, K i)
    (hK : ∀ i, ∃ (I : Set ℕ) (G : I → α), m (K i \ ⋃ j, img (G j)) = 0) :
    ∃ (I : Set ℕ) (G : I → α), m (L \ ⋃ j, img (G j)) = 0 := by
  choose I G hG using hK
  obtain ⟨J, g, hg⟩ := exists_setNat_iUnion_eq img (fun p : Σ i, I i => G p.1 p.2)
  refine ⟨J, g, ?_⟩
  rw [hg]
  refine measure_mono_null ?_ (measure_iUnion_null hG)
  rintro z ⟨hzL, hz⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hL hzL)
  refine mem_iUnion.mpr ⟨i, hi, fun hz' => hz ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp hz'
  exact mem_iUnion.mpr ⟨⟨i, j⟩, hj⟩

theorem HasHorizontalGraphCover.of_subset_iUnion {n k : ℕ} {ε : ℝ} {ι : Type*}
    [Countable ι] {L : Set (Space n)} (K : ι → Set (Space n)) (hL : L ⊆ ⋃ i, K i)
    (hK : ∀ i, HasHorizontalGraphCover k (K i) ε) : HasHorizontalGraphCover k L ε :=
  exists_setNat_null_cover (hausdorffP n k) (HorizontalGraph.image (n := n) (k := k) (ε := ε))
    K hL hK

theorem HasRegularVerticalGraphCover.of_subset_iUnion {n k : ℕ} {ε : ℝ} {ι : Type*}
    [Countable ι] {L : Set (Space n)} (K : ι → Set (Space n)) (hL : L ⊆ ⋃ i, K i)
    (hK : ∀ i, HasRegularVerticalGraphCover k (K i) ε) :
    HasRegularVerticalGraphCover k L ε :=
  exists_setNat_null_cover (hausdorffP n k)
    (RegularVerticalGraph.image (n := n) (k := k) (ε := ε)) K hL hK

/-! ### Content bounds for subsets of finite unions -/

/-- `c ≤ N` copies of `ofReal a` are at most `ofReal b` when `N * a ≤ b`. -/
theorem sum_fin_ofReal_le {c N : ℕ} (hc : c ≤ N) {a b : ℝ} (ha : 0 ≤ a)
    (hab : (N : ℝ) * a ≤ b) : ∑ _i : Fin c, ENNReal.ofReal a ≤ ENNReal.ofReal b := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) ha).trans hab)

theorem mul_mul_le_of_mul_le {N C C' x : ℝ} (hC : N * C ≤ C') (hx : 0 ≤ x) :
    N * (C * x) ≤ C' * x := by
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hC hx

/-- Equal-radius content bounds pass to subsets of a union of `c ≤ N` sets. -/
theorem HasMetricContentBounds.of_subset_iUnion {n k c N : ℕ} (hc : c ≤ N)
    {Cm C : ℝ} (hCm : 0 ≤ Cm) (hC : (N : ℝ) * Cm ≤ C) {K : Fin c → Set (Space n)}
    {L : Set (Space n)} (hL : L ⊆ ⋃ i, K i)
    (hK : ∀ i, HasMetricContentBounds k Cm (K i)) : HasMetricContentBounds k C L where
  hausdorff q R hR hR1 := by
    have hsub : L ∩ Metric.ball q R ⊆ ⋃ i, (K i ∩ Metric.ball q R) := by
      rintro z ⟨hzL, hzB⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hL hzL)
      exact mem_iUnion.mpr ⟨i, hi, hzB⟩
    have hx : 0 ≤ R ^ k := pow_nonneg hR.le k
    calc hausdorffP n k (L ∩ Metric.ball q R)
        ≤ ∑ i, hausdorffP n k (K i ∩ Metric.ball q R) :=
          (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _i : Fin c, ENNReal.ofReal (Cm * R ^ k) :=
          Finset.sum_le_sum fun i _ => (hK i).hausdorff q R hR hR1
      _ ≤ ENNReal.ofReal (C * R ^ k) :=
          sum_fin_ofReal_le hc (mul_nonneg hCm hx) (mul_mul_le_of_mul_le hC hx)
  separated q R r hR hR1 hr hrR F hF hsep := by
    classical
    have hcover : F ⊆ Finset.univ.biUnion (fun i : Fin c => F.filter (· ∈ K i)) := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hL (hF hx).1)
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hi⟩⟩
    have hpiece : ∀ i, ((F.filter (· ∈ K i)).card : ℝ) ≤ Cm * (R / r) ^ k := by
      intro i
      refine (hK i).separated q R r hR hR1 hr hrR _ ?_ ?_
      · intro x hx
        have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
        exact ⟨hx'.2, (hF hx'.1).2⟩
      · intro x hx y hy hxy
        exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    have hx : 0 ≤ (R / r) ^ k := pow_nonneg (div_nonneg hR.le hr.le) k
    calc (F.card : ℝ)
        ≤ ((Finset.univ.biUnion fun i : Fin c => F.filter (· ∈ K i)).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hcover)
      _ ≤ ∑ i : Fin c, ((F.filter (· ∈ K i)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin c, Cm * (R / r) ^ k := Finset.sum_le_sum fun i _ => hpiece i
      _ = (c : ℝ) * (Cm * (R / r) ^ k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (Cm * (R / r) ^ k) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (mul_nonneg hCm hx)
      _ ≤ C * (R / r) ^ k := mul_mul_le_of_mul_le hC hx
  minkowski r hr hr1 := by
    have hsub : {z | Metric.infEDist z L < ENNReal.ofReal r} ⊆
        ⋃ i, {z | Metric.infEDist z (K i) < ENNReal.ofReal r} := by
      intro z hz
      have h1 : Metric.infEDist z (⋃ i, K i) < ENNReal.ofReal r :=
        (Metric.infEDist_anti hL).trans_lt hz
      rw [Metric.infEDist_iUnion] at h1
      obtain ⟨i, hi⟩ := iInf_lt_iff.mp h1
      exact mem_iUnion.mpr ⟨i, hi⟩
    have hx : 0 ≤ r ^ (n + 2 - k) := pow_nonneg hr.le _
    calc parabolicVolume n {z | Metric.infEDist z L < ENNReal.ofReal r}
        ≤ ∑ i, parabolicVolume n {z | Metric.infEDist z (K i) < ENNReal.ofReal r} :=
          (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _i : Fin c, ENNReal.ofReal (Cm * r ^ (n + 2 - k)) :=
          Finset.sum_le_sum fun i _ => (hK i).minkowski r hr hr1
      _ ≤ ENNReal.ofReal (C * r ^ (n + 2 - k)) :=
          sum_fin_ofReal_le hc (mul_nonneg hCm hx) (mul_mul_le_of_mul_le hC hx)

/-- Finite packing for a disjoint ball family indexed by an arbitrary finset. -/
theorem HasFiniteBallPacking.finset {n k : ℕ} {C : ℝ} {K : Set (Space n)}
    (h : HasFiniteBallPacking k C K) {ι : Type*} (s : Finset ι) (z : ι → Space n)
    (r : ι → ℝ) {q : Space n} {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hz : ∀ i ∈ s, z i ∈ K ∩ Metric.ball q R) (hr : ∀ i ∈ s, 0 < r i ∧ r i ≤ R)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) :
    ∑ i ∈ s, ENNReal.ofReal (r i) ^ k ≤ ENNReal.ofReal (C * R ^ k) := by
  let e := s.equivFin
  have hsum : ∑ i ∈ s, ENNReal.ofReal (r i) ^ k =
      ∑ m : Fin s.card, ENNReal.ofReal (r (e.symm m)) ^ k := by
    rw [← Finset.sum_coe_sort s]
    exact Fintype.sum_equiv e _ _ (fun x => by rw [Equiv.symm_apply_apply])
  rw [hsum]
  exact h q R hR hR1 s.card (fun m => z (e.symm m)) (fun m => r (e.symm m))
    (fun m => hz _ (e.symm m).2) (fun m => hr _ (e.symm m).2)
    (fun a b hab => hd _ (e.symm a).2 _ (e.symm b).2
      (fun h' => hab (e.symm.injective (Subtype.ext h'))))

/-- Finite packing passes to subsets of a union of `c ≤ N` sets. -/
theorem HasFiniteBallPacking.of_subset_iUnion {n k c N : ℕ} (hc : c ≤ N)
    {Cp C : ℝ} (hCp : 0 ≤ Cp) (hC : (N : ℝ) * Cp ≤ C) {K : Fin c → Set (Space n)}
    {L : Set (Space n)} (hL : L ⊆ ⋃ i, K i)
    (hK : ∀ i, HasFiniteBallPacking k Cp (K i)) : HasFiniteBallPacking k C L := by
  classical
  intro q R hR hR1 l z r hz hr hd
  have hle : ∀ m : Fin l, ENNReal.ofReal (r m) ^ k ≤
      ∑ i : Fin c, if z m ∈ K i then ENNReal.ofReal (r m) ^ k else 0 := by
    intro m
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hL (hz m).1)
    calc ENNReal.ofReal (r m) ^ k
        = if z m ∈ K i then ENNReal.ofReal (r m) ^ k else 0 := by simp [hi]
      _ ≤ ∑ j : Fin c, if z m ∈ K j then ENNReal.ofReal (r m) ^ k else 0 :=
          Finset.single_le_sum
            (f := fun j => if z m ∈ K j then ENNReal.ofReal (r m) ^ k else 0)
            (fun j _ => zero_le) (Finset.mem_univ i)
  have hx : 0 ≤ R ^ k := pow_nonneg hR.le k
  calc ∑ m, ENNReal.ofReal (r m) ^ k
      ≤ ∑ m : Fin l, ∑ i : Fin c, if z m ∈ K i then ENNReal.ofReal (r m) ^ k else 0 :=
        Finset.sum_le_sum fun m _ => hle m
    _ = ∑ i : Fin c, ∑ m ∈ Finset.univ.filter (fun m => z m ∈ K i),
          ENNReal.ofReal (r m) ^ k := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_filter]
    _ ≤ ∑ _i : Fin c, ENNReal.ofReal (Cp * R ^ k) :=
        Finset.sum_le_sum fun i _ => (hK i).finset _ z r hR hR1
          (fun m hm => ⟨(Finset.mem_filter.mp hm).2, (hz m).2⟩) (fun m _ => hr m)
          (fun a _ b _ hab => hd a b hab)
    _ ≤ ENNReal.ofReal (C * R ^ k) :=
        sum_fin_ofReal_le hc (mul_nonneg hCp hx) (mul_mul_le_of_mul_le hC hx)

/-- Countable disjoint packing follows from finite packing by partial sums. -/
theorem HasFiniteBallPacking.countable {n k : ℕ} {C : ℝ} {K : Set (Space n)}
    (h : HasFiniteBallPacking k C K) : ∀ q R, 0 < R → R ≤ 1 →
    ∀ (I : Set ℕ) (z : I → Space n) (r : I → ℝ),
      (∀ i, z i ∈ K ∩ Metric.ball q R) →
      (∀ i, 0 < r i ∧ r i ≤ R) →
      (∀ i j, i ≠ j → Disjoint (Metric.ball (z i) (r i)) (Metric.ball (z j) (r j))) →
      (∑' i, ENNReal.ofReal (r i) ^ k) ≤ ENNReal.ofReal (C * R ^ k) := by
  intro q R hR hR1 I z r hz hr hd
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s => h.finset s z r hR hR1 (fun i _ => hz i) (fun i _ => hr i)
    (fun i _ j _ hij => hd i j hij)

/-- Metric content and finite packing give every rectifiability content bound. -/
theorem HasRectifiabilityContentBounds.of_metric_packing {n k : ℕ} {C : ℝ}
    {K : Set (Space n)} (hm : HasMetricContentBounds k C K)
    (hp : HasFiniteBallPacking k C K) : HasRectifiabilityContentBounds k C K where
  hausdorff := hm.hausdorff
  separated := hm.separated
  minkowski := hm.minkowski
  finite_packing := hp
  countable_packing := hp.countable

/-! ### Restrictions and supports -/

/-- The identity `μ = μ|(H ∪ V)ᶜ + μ|H + μ|V` for disjoint Borel retained sets. -/
theorem RetainedSets.measure_eq_sum {n : ℕ} (D : RetainedSets n) (μ : Measure (Space n)) :
    μ = D.remainderMeasure μ + D.horizontalMeasure μ + D.verticalMeasure μ := by
  unfold RetainedSets.remainderMeasure RetainedSets.horizontalMeasure
    RetainedSets.verticalMeasure
  rw [add_assoc, ← Measure.restrict_union D.disjoint D.measurable_vertical, add_comm,
    Measure.restrict_add_restrict_compl (D.measurable_horizontal.union D.measurable_vertical)]

/-- The support of a restriction lies in every closed set containing the set. -/
theorem support_restrict_subset_of_isClosed {n : ℕ} (μ : Measure (Space n))
    {A B : Set (Space n)} (hAB : A ⊆ B) (hB : IsClosed B) : (μ.restrict A).support ⊆ B :=
  Measure.support_restrict_subset.trans (inter_subset_left.trans (closure_minimal hAB hB))

theorem restrict_eq_zero_and_support_empty {n : ℕ} (μ : Measure (Space n))
    {A : Set (Space n)} (hA : A = ∅) : μ.restrict A = 0 ∧ (μ.restrict A).support = ∅ := by
  rw [hA, Measure.restrict_empty]
  exact ⟨rfl, Measure.support_zero⟩

/-! ### The assembled retained sets -/

namespace GoodSourceLocalization

variable {n k N : ℕ} {T : FamilyKind} {μ : Measure (Space n)} {M : ℝ}

theorem region_subset_ball (S : GoodSourceLocalization μ k T M N) (i : Fin S.count) :
    S.region i ⊆ Metric.ball (point 0 0) 1 := by
  intro z hz
  have hgood : z ∈ thresholdGoodSet μ k T M := by
    rw [← S.cover]
    exact mem_iUnion.mpr ⟨i, hz⟩
  exact hgood.1

variable {Cl : ℝ} (S : GoodSourceLocalization μ k T M N) {K : Fin S.count → Set (Space n)}
  (pieces : ∀ i, CompactTypedPieces (μ.restrict (S.region i)) k T M Cl (K i))

/-- Retain `region i ∩ horizontal i` and `region i ∩ vertical i`, not the compact
pieces themselves. -/
def assembledRetainedSets : RetainedSets n where
  horizontal := ⋃ i, S.region i ∩ (pieces i).horizontal
  vertical := ⋃ i, S.region i ∩ (pieces i).vertical
  measurable_horizontal := MeasurableSet.iUnion fun i =>
    (S.measurable i).inter (pieces i).horizontal_compact.isClosed.measurableSet
  measurable_vertical := MeasurableSet.iUnion fun i =>
    (S.measurable i).inter (pieces i).vertical_compact.isClosed.measurableSet
  disjoint := by
    rw [Set.disjoint_iUnion_left]
    intro i
    rw [Set.disjoint_iUnion_right]
    intro j
    by_cases hij : i = j
    · subst hij
      exact (pieces i).disjoint.mono inter_subset_right inter_subset_right
    · exact (S.disjoint i j hij).mono inter_subset_left inter_subset_left
  horizontal_subset := iUnion_subset fun i => inter_subset_left.trans (S.region_subset_ball i)
  vertical_subset := iUnion_subset fun i => inter_subset_left.trans (S.region_subset_ball i)

theorem assembled_horizontal :
    (S.assembledRetainedSets pieces).horizontal = ⋃ i, S.region i ∩ (pieces i).horizontal :=
  rfl

theorem assembled_vertical :
    (S.assembledRetainedSets pieces).vertical = ⋃ i, S.region i ∩ (pieces i).vertical :=
  rfl

/-- Supports of the retained restrictions lie in the compact pieces and the
closed unit ball. -/
theorem horizontalSupport_subset :
    (S.assembledRetainedSets pieces).horizontalSupport μ ⊆
      (⋃ i, (pieces i).horizontal) ∩ Metric.closedBall (point 0 0) 1 := by
  refine support_restrict_subset_of_isClosed μ ?_
    ((isClosed_iUnion_of_finite fun i => (pieces i).horizontal_compact.isClosed).inter
      Metric.isClosed_closedBall)
  exact subset_inter (iUnion_mono fun i => inter_subset_right)
    (((S.assembledRetainedSets pieces).horizontal_subset).trans Metric.ball_subset_closedBall)

theorem verticalSupport_subset :
    (S.assembledRetainedSets pieces).verticalSupport μ ⊆
      (⋃ i, (pieces i).vertical) ∩ Metric.closedBall (point 0 0) 1 := by
  refine support_restrict_subset_of_isClosed μ ?_
    ((isClosed_iUnion_of_finite fun i => (pieces i).vertical_compact.isClosed).inter
      Metric.isClosed_closedBall)
  exact subset_inter (iUnion_mono fun i => inter_subset_right)
    (((S.assembledRetainedSets pieces).vertical_subset).trans Metric.ball_subset_closedBall)

theorem supportUnion_subset :
    (S.assembledRetainedSets pieces).supportUnion μ ⊆ ⋃ i, K i :=
  union_subset
    ((S.horizontalSupport_subset pieces).trans
      (inter_subset_left.trans (iUnion_mono fun i => (pieces i).horizontal_subset)))
    ((S.verticalSupport_subset pieces).trans
      (inter_subset_left.trans (iUnion_mono fun i => (pieces i).vertical_subset)))

/-- In the unit ball, the remainder is the bad set plus the piece losses. -/
theorem remainder_le (Γ : ℝ)
    (hbad : μ (Metric.ball (point 0 0) 1 ∩
      {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ) :
    (S.assembledRetainedSets pieces).remainderMeasure μ (Metric.ball (point 0 0) 1) ≤
      ENNReal.ofReal Γ + ∑ _i : Fin S.count, ENNReal.ofReal (Cl * M) := by
  set D := S.assembledRetainedSets pieces
  have hsub : Metric.ball (point 0 0) 1 ∩ (D.horizontal ∪ D.vertical)ᶜ ⊆
      (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ∪
        ⋃ i, S.region i ∩ ((pieces i).horizontal ∪ (pieces i).vertical)ᶜ := by
    rintro z ⟨hzB, hzHV⟩
    by_cases hz : ENNReal.ofReal M < squareEnergy μ k T 2 z
    · exact Or.inl ⟨hzB, hz⟩
    · have hgood : z ∈ thresholdGoodSet μ k T M := ⟨hzB, not_lt.mp hz⟩
      rw [← S.cover] at hgood
      obtain ⟨i, hi⟩ := mem_iUnion.mp hgood
      refine Or.inr (mem_iUnion.mpr ⟨i, hi, fun hzhv => hzHV ?_⟩)
      rcases hzhv with h | h
      · exact Or.inl (mem_iUnion.mpr ⟨i, hi, h⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨i, hi, h⟩)
  have hpiece : ∀ i, μ (S.region i ∩ ((pieces i).horizontal ∪ (pieces i).vertical)ᶜ) ≤
      ENNReal.ofReal (Cl * M) := by
    intro i
    have hloss := (pieces i).loss
    rwa [Measure.restrict_apply' (S.measurable i), inter_comm] at hloss
  unfold RetainedSets.remainderMeasure
  rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet]
  calc μ (Metric.ball (point 0 0) 1 ∩ (D.horizontal ∪ D.vertical)ᶜ)
      ≤ μ (Metric.ball (point 0 0) 1 ∩ {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) +
          μ (⋃ i, S.region i ∩ ((pieces i).horizontal ∪ (pieces i).vertical)ᶜ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal Γ + ∑ _i : Fin S.count, ENNReal.ofReal (Cl * M) :=
        add_le_add hbad
          ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => hpiece i))

end GoodSourceLocalization

/-- The statement of `assemble_compact_sources`. Assemble restrictions to `region i ∩ A_T i`; retain actual compact supports,
one `Γ` with coefficient one, every graph tolerance, finite-union content
bounds and countable packing. The dimension guards and the source regularity
hypotheses are kept to match that statement; the bookkeeping itself does not
need them. -/
theorem familyDecomposition_of_compactSources {n k N : ℕ} (_hk : 1 ≤ k) (_hkn : k ≤ n + 2)
    (hN : 0 < N) (T : FamilyKind) (μ : Measure (Space n))
    (_hμ : IsFiniteMeasureOnCompacts μ) (_hreg : μ.InnerRegular)
    (M Γ Cl Cm Cp : ℝ) (hM : 0 ≤ M) (hΓ : 0 ≤ Γ)
    (hCl : 0 < Cl) (hCm : 0 < Cm) (hCp : 0 < Cp)
    (hbad : μ (Metric.ball (point 0 0) 1 ∩
      {z | ENNReal.ofReal M < squareEnergy μ k T 2 z}) ≤ ENNReal.ofReal Γ)
    (S : GoodSourceLocalization μ k T M N)
    (K : Fin S.count → Set (Space n))
    (pieces : ∀ i, CompactTypedPieces (μ.restrict (S.region i)) k T M Cl (K i))
    (hmetric : ∀ i, HasMetricContentBounds k Cm (K i))
    (hpacking : ∀ i, HasFiniteBallPacking k Cp (K i)) :
    HasFamilyDecomposition k T ((N : ℝ) * (Cl + Cm + Cp)) M Γ μ := by
  set D := S.assembledRetainedSets pieces
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hClC : (N : ℝ) * Cl ≤ (N : ℝ) * (Cl + Cm + Cp) :=
    mul_le_mul_of_nonneg_left (by linarith) hNn
  have hCmC : (N : ℝ) * Cm ≤ (N : ℝ) * (Cl + Cm + Cp) :=
    mul_le_mul_of_nonneg_left (by linarith) hNn
  have hCpC : (N : ℝ) * Cp ≤ (N : ℝ) * (Cl + Cm + Cp) :=
    mul_le_mul_of_nonneg_left (by linarith) hNn
  have hHsupp := S.horizontalSupport_subset pieces
  have hVsupp := S.verticalSupport_subset pieces
  have hHcompact : IsCompact (⋃ i, (pieces i).horizontal) :=
    isCompact_iUnion fun i => (pieces i).horizontal_compact
  have hVcompact : IsCompact (⋃ i, (pieces i).vertical) :=
    isCompact_iUnion fun i => (pieces i).vertical_compact
  have hHempty : (∀ i, (pieces i).horizontal = ∅) → D.horizontal = ∅ := fun h =>
    iUnion_eq_empty.mpr fun i => by rw [h i, inter_empty]
  have hVempty : (∀ i, (pieces i).vertical = ∅) → D.vertical = ∅ := fun h =>
    iUnion_eq_empty.mpr fun i => by rw [h i, inter_empty]
  have hx : 0 ≤ (N : ℝ) * (Cl + Cm + Cp) * M := mul_nonneg (by positivity) hM
  refine ⟨D, ?_, ?_, ?_⟩
  · exact
    { measure_eq := D.measure_eq_sum μ
      remainder_bound := by
        calc D.remainderMeasure μ (Metric.ball (point 0 0) 1)
            ≤ ENNReal.ofReal Γ + ∑ _i : Fin S.count, ENNReal.ofReal (Cl * M) :=
              S.remainder_le pieces Γ hbad
          _ ≤ ENNReal.ofReal Γ + ENNReal.ofReal ((N : ℝ) * (Cl + Cm + Cp) * M) :=
              add_le_add le_rfl (sum_fin_ofReal_le S.count_le (mul_nonneg hCl.le hM)
                (mul_mul_le_of_mul_le hClC hM))
          _ = ENNReal.ofReal ((N : ℝ) * (Cl + Cm + Cp) * M + Γ) := by
              rw [← ENNReal.ofReal_add hΓ hx, add_comm Γ]
      horizontal_compact :=
        (hHcompact.inter_right Metric.isClosed_closedBall).of_isClosed_subset
          Measure.isClosed_support hHsupp
      vertical_compact :=
        (hVcompact.inter_right Metric.isClosed_closedBall).of_isClosed_subset
          Measure.isClosed_support hVsupp
      horizontal_in_unit := hHsupp.trans inter_subset_right
      vertical_in_unit := hVsupp.trans inter_subset_right
      horizontal_unavailable := fun h => restrict_eq_zero_and_support_empty μ
        (hHempty fun i => (pieces i).horizontal_unavailable h)
      vertical_unavailable := fun h => restrict_eq_zero_and_support_empty μ
        (hVempty fun i => (pieces i).vertical_unavailable h)
      horizontal_graphs := fun ε hε =>
        HasHorizontalGraphCover.of_subset_iUnion (fun i => (pieces i).horizontal)
          (hHsupp.trans inter_subset_left) fun i => (pieces i).horizontal_graphs ε hε
      vertical_graphs := fun ε hε =>
        HasRegularVerticalGraphCover.of_subset_iUnion (fun i => (pieces i).vertical)
          (hVsupp.trans inter_subset_left) fun i => (pieces i).vertical_graphs ε hε
      content := HasRectifiabilityContentBounds.of_metric_packing
        (HasMetricContentBounds.of_subset_iUnion S.count_le hCm.le hCmC
          (S.supportUnion_subset pieces) hmetric)
        (HasFiniteBallPacking.of_subset_iUnion S.count_le hCp.le hCpC
          (S.supportUnion_subset pieces) hpacking) }
  · intro hT
    exact restrict_eq_zero_and_support_empty μ (hVempty fun i => ((pieces i).family.1 hT))
  · intro hT
    exact restrict_eq_zero_and_support_empty μ (hHempty fun i => ((pieces i).family.2 hT))

end ParabolicRectifiability
