import ParabolicRectifiability.QuantitativeCharacterization.Statements.BoundedSupportComponents
import ParabolicRectifiability.QuantitativeCharacterization.Assembly.Monotonicity
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Forward.PartitionEnergy.Assignment

/-! # The bounded union of root certificates

Proof of `dp2_bounded_union : dp2_BoundedUnionStatement`.

Proof idea:
* the chosen root coverings `𝒞 j` (`j : Fin N`) are combined over the index
  `Σ j, (𝒞 j).index`, encoded in `ℕ` by `Nat.pair` (`dp2_union_code`) and reindexed by
  `Equiv.ofInjective` (`dp2_union_equiv`); references are enlarged by `Reference.mono`;
* the finite Borel assignment `G_j = P(b_j, r) \ ⋃_{l < j} P(b_l, r)` is the first piece
  `Forward.PartitionEnergy.d1aassign_firstPiece univ Fin.val (fun j => P(b_j, r))`
  (`dp2_union_piece`);
* scale sets `𝒰^j_i ∩ ((G_j ∩ P(a,R)) × ℝ)` (`dp2_union_scale`), bad set
  `⋃_j 𝓑_j ∩ ((G_j ∩ P(a,R)) × ℝ) ∪ (P(a,R) ∩ E) × [r, R)` (`dp2_union_bad`);
* one helper lemma per covering field, then the assembly `dp2_union_covering` and the statement
  `dp2_bounded_union_proof`.

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations
open Forward.PartitionEnergy

variable {n k : ℕ} {K' L' : ℝ} {μ : Measure (Space n)} {r : ℝ} {N : ℕ} {b : Fin N → Space n}

/-! ## The Borel assignment `G_j` (first pieces, `S = univ`, `ord = Fin.val`) -/

/-- `G_j = P(b_j, r) \ ⋃_{l < j} P(b_l, r)`. -/
def dp2_union_piece (b : Fin N → Space n) (r : ℝ) (j : Fin N) : Set (Space n) :=
  d1aassign_firstPiece univ Fin.val (fun j => Metric.ball (b j) r) j

theorem dp2_union_piece_subset (j : Fin N) : dp2_union_piece b r j ⊆ Metric.ball (b j) r :=
  d1aassign_firstPiece_subset univ Fin.val (fun j => Metric.ball (b j) r) j

theorem dp2_union_piece_eq {j j' : Fin N} {z : Space n} (hz : z ∈ dp2_union_piece b r j)
    (hz' : z ∈ dp2_union_piece b r j') : j = j' := by
  by_contra hne
  exact Set.disjoint_left.mp (d1aassign_firstPiece_disjoint
    (Set.injOn_of_injective Fin.val_injective) (fun j => Metric.ball (b j) r)
    (mem_univ j) (mem_univ j') hne) hz hz'

theorem dp2_union_piece_cover : (⋃ j, dp2_union_piece b r j) = ⋃ j, Metric.ball (b j) r := by
  have h := d1aassign_biUnion_firstPiece (univ : Set (Fin N)) Fin.val
    (fun j => Metric.ball (b j) r)
  simp only [biUnion_univ] at h
  exact h

theorem dp2_union_piece_measurable (j : Fin N) : MeasurableSet (dp2_union_piece b r j) :=
  d1aassign_firstPiece_measurable (C := fun j => Metric.ball (b j) r) countable_univ Fin.val
    (fun _ => measurableSet_ball) j

/-- The slab `(G_j ∩ P(a,R)) × ℝ` to which the regions of the certificate `j` are restricted. -/
def dp2_union_slab (b : Fin N → Space n) (r : ℝ) (a : Space n) (R : ℝ) (j : Fin N) :
    Set (Space n × ℝ) :=
  (dp2_union_piece b r j ∩ Metric.ball a R) ×ˢ univ

theorem dp2_union_slab_measurable (a : Space n) (R : ℝ) (j : Fin N) :
    MeasurableSet (dp2_union_slab b r a R j) :=
  ((dp2_union_piece_measurable j).inter measurableSet_ball).prod MeasurableSet.univ

/-! ## The combined index and regions -/

variable (𝒞 : ∀ j, RegularMixedCovering k K' L' μ (b j) r)

/-- Encoding of the union index `Σ j, (𝒞 j).index` into `ℕ`. -/
def dp2_union_code (p : Σ j, (𝒞 j).index) : ℕ :=
  Nat.pair p.1.val p.2.val

theorem dp2_union_code_injective : Function.Injective (dp2_union_code 𝒞) := by
  rintro ⟨j, i⟩ ⟨j', i'⟩ h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  obtain rfl : j = j' := Fin.ext h1
  obtain rfl : i = i' := Subtype.ext h2
  rfl

/-- The union index set `range (dp2_union_code 𝒞) ⊆ ℕ`, identified with `Σ j, (𝒞 j).index`. -/
def dp2_union_equiv : Set.range (dp2_union_code 𝒞) ≃ Σ j, (𝒞 j).index :=
  (Equiv.ofInjective _ (dp2_union_code_injective 𝒞)).symm

/-- The scale set `𝒰^j_i ∩ ((G_j ∩ P(a,R)) × ℝ)`. -/
def dp2_union_scale (a : Space n) (R : ℝ) (p : Σ j, (𝒞 j).index) : Set (Space n × ℝ) :=
  (𝒞 p.1).scaleSet p.2 ∩ dp2_union_slab b r a R p.1

/-- The bad set `⋃_j 𝓑_j ∩ ((G_j ∩ P(a,R)) × ℝ) ∪ (P(a,R) ∩ E) × [r, R)`. -/
def dp2_union_bad (a : Space n) (R : ℝ) : Set (Space n × ℝ) :=
  (⋃ j, (𝒞 j).badSet ∩ dp2_union_slab b r a R j) ∪ (Metric.ball a R ∩ μ.support) ×ˢ Ico r R

/-! ## Sums over the union index -/

theorem dp2_union_tsum_le {ι : Fin N → Type*} (f : ∀ j, ι j → ℝ≥0∞) {c : ℝ≥0∞}
    (h : ∀ j, ∑' i, f j i ≤ c) : ∑' p : Σ j, ι j, f p.1 p.2 ≤ N * c := by
  rw [ENNReal.tsum_sigma, tsum_fintype]
  calc ∑ j, ∑' i, f j i ≤ ∑ _j : Fin N, c := Finset.sum_le_sum fun j _ => h j
    _ = N * c := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem dp2_union_natCast_mul_ofReal (x : ℝ) :
    (N : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal ((N : ℝ) * x) := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]

/-- The radius sum of the union: `Σ ≤ N K' r^k` (also the root packing). -/
theorem dp2_union_radiusSum :
    ∑' p : Σ j, (𝒞 j).index, ENNReal.ofReal ((𝒞 p.1).radius p.2) ^ k ≤
      ENNReal.ofReal ((N : ℝ) * K' * r ^ k) := by
  refine (dp2_union_tsum_le (fun j i => ENNReal.ofReal ((𝒞 j).radius i) ^ k)
    fun j => (𝒞 j).root_packing).trans_eq ?_
  rw [dp2_union_natCast_mul_ofReal, mul_assoc]

open scoped Classical in
/-- Local packing of the union: the sum of the `N` local packings. -/
theorem dp2_union_localSum (z : Space n) (s : ℝ) (hs : 0 < s) :
    (∑' p : Σ j, (𝒞 j).index,
        if (𝒞 p.1).center p.2 ∈ Metric.ball z s ∧ (𝒞 p.1).radius p.2 ≤ s then
          ENNReal.ofReal ((𝒞 p.1).radius p.2) ^ k else 0) ≤
      ENNReal.ofReal ((N : ℝ) * K' * s ^ k) := by
  refine (dp2_union_tsum_le (fun j i =>
      if (𝒞 j).center i ∈ Metric.ball z s ∧ (𝒞 j).radius i ≤ s then
        ENNReal.ofReal ((𝒞 j).radius i) ^ k else 0)
    fun j => (𝒞 j).local_packing z s hs).trans_eq ?_
  rw [dp2_union_natCast_mul_ofReal, mul_assoc]

theorem dp2_union_real_le {K Kb R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hK' : 0 ≤ K')
    (hK : (N : ℝ) * K' + Kb ≤ K) : (N : ℝ) * K' * r ^ k + Kb * R ^ k ≤ K * R ^ k := by
  have hNK : 0 ≤ (N : ℝ) * K' := mul_nonneg (Nat.cast_nonneg N) hK'
  have hR : 0 ≤ R ^ k := pow_nonneg (hr.le.trans hrR) k
  calc (N : ℝ) * K' * r ^ k + Kb * R ^ k ≤ (N : ℝ) * K' * R ^ k + Kb * R ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrR k) hNK) le_rfl
    _ = ((N : ℝ) * K' + Kb) * R ^ k := by ring
    _ ≤ K * R ^ k := mul_le_mul_of_nonneg_right hK hR

/-! ## The covering fields -/

theorem dp2_union_scale_measurable (a : Space n) (R : ℝ) (p : Σ j, (𝒞 j).index) :
    MeasurableSet (dp2_union_scale 𝒞 a R p) :=
  ((𝒞 p.1).measurable_scaleSet p.2).inter (dp2_union_slab_measurable a R p.1)

theorem dp2_union_bad_measurable (a : Space n) (R : ℝ) : MeasurableSet (dp2_union_bad 𝒞 a R) :=
  (MeasurableSet.iUnion fun j =>
      ((𝒞 j).measurable_badSet).inter (dp2_union_slab_measurable a R j)).union
    ((measurableSet_ball.inter μ.isClosed_support.measurableSet).prod measurableSet_Ico)

theorem dp2_union_scale_subset {a : Space n} {R : ℝ} (hrR : r ≤ R) (p : Σ j, (𝒞 j).index) :
    dp2_union_scale 𝒞 a R p ⊆ rootPairs μ a R := by
  rintro ⟨z, t⟩ ⟨hU, hS⟩
  have h1 := (𝒞 p.1).scaleSet_subset p.2 hU
  simp only [rootPairs, dp2_union_slab, mem_prod, mem_inter_iff, mem_Ioo, mem_univ,
    and_true] at h1 hS ⊢
  exact ⟨⟨hS.2, h1.1.2⟩, h1.2.1, h1.2.2.trans_le hrR⟩

theorem dp2_union_bad_subset {a : Space n} {R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    dp2_union_bad 𝒞 a R ⊆ rootPairs μ a R := by
  rintro ⟨z, t⟩ (h | h)
  · obtain ⟨j, hB, hS⟩ := mem_iUnion.mp h
    have h1 := (𝒞 j).badSet_subset hB
    simp only [rootPairs, dp2_union_slab, mem_prod, mem_inter_iff, mem_Ioo, mem_univ,
      and_true] at h1 hS ⊢
    exact ⟨⟨hS.2, h1.1.2⟩, h1.2.1, h1.2.2.trans_le hrR⟩
  · simp only [rootPairs, mem_prod, mem_Ico, mem_Ioo] at h ⊢
    exact ⟨h.1, hr.trans_le h.2.1, h.2.2⟩

theorem dp2_union_bad_inter_scale {a : Space n} {R : ℝ} (p : Σ j, (𝒞 j).index) :
    pointScaleMeasure μ (dp2_union_bad 𝒞 a R ∩ dp2_union_scale 𝒞 a R p) = 0 := by
  refine measure_mono_null ?_ ((𝒞 p.1).bad_inter_scale_null p.2)
  rintro ⟨z, t⟩ ⟨hB | hB, hU, hS⟩
  · obtain ⟨j, hBj, hSj⟩ := mem_iUnion.mp hB
    have hj : j = p.1 := dp2_union_piece_eq hSj.1.1 hS.1.1
    subst hj
    exact ⟨hBj, hU⟩
  · have h1 := (𝒞 p.1).scaleSet_subset p.2 hU
    simp only [rootPairs, mem_prod, mem_Ico, mem_Ioo] at h1 hB
    exact absurd h1.2.2 (not_lt.mpr hB.2.1)

theorem dp2_union_scale_inter_scale {a : Space n} {R : ℝ} {p q : Σ j, (𝒞 j).index}
    (hpq : p ≠ q) :
    pointScaleMeasure μ (dp2_union_scale 𝒞 a R p ∩ dp2_union_scale 𝒞 a R q) = 0 := by
  obtain ⟨j, i⟩ := p
  obtain ⟨j', i'⟩ := q
  by_cases hj : j = j'
  · subst hj
    have hi : i ≠ i' := fun h => hpq (by rw [h])
    refine measure_mono_null ?_ ((𝒞 j).scale_inter_scale_null i i' hi)
    exact inter_subset_inter inter_subset_left inter_subset_left
  · have hempty : dp2_union_scale 𝒞 a R ⟨j, i⟩ ∩ dp2_union_scale 𝒞 a R ⟨j', i'⟩ = ∅ := by
      ext ⟨z, t⟩
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hS⟩, _, hS'⟩
      exact hj (dp2_union_piece_eq hS.1.1 hS'.1.1)
    rw [hempty, measure_empty]

theorem dp2_union_cover {a : Space n} {R : ℝ} (hcov : μ.support ⊆ ⋃ j, Metric.ball (b j) r) :
    pointScaleMeasure μ
      (rootPairs μ a R \ (dp2_union_bad 𝒞 a R ∪ ⋃ p, dp2_union_scale 𝒞 a R p)) = 0 := by
  refine measure_mono_null ?_ (measure_iUnion_null fun j => (𝒞 j).cover_null)
  rintro ⟨z, t⟩ ⟨hP, hnot⟩
  simp only [rootPairs, mem_prod, mem_inter_iff, mem_Ioo] at hP
  rcases lt_or_ge t r with htr | hrt
  · have hz : z ∈ ⋃ j, dp2_union_piece b r j := by
      rw [dp2_union_piece_cover]; exact hcov hP.1.2
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨j, ?_, ?_⟩
    · simp only [rootPairs, mem_prod, mem_inter_iff, mem_Ioo]
      exact ⟨⟨dp2_union_piece_subset j hj, hP.1.2⟩, hP.2.1, htr⟩
    · rintro (hB | hU)
      · exact hnot (Or.inl (Or.inl (mem_iUnion.mpr ⟨j, hB, ⟨hj, hP.1.1⟩, mem_univ _⟩)))
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hU
        exact hnot (Or.inr (mem_iUnion.mpr ⟨⟨j, i⟩, hi, ⟨hj, hP.1.1⟩, mem_univ _⟩))
  · exact (hnot (Or.inl (Or.inr ⟨hP.1, hrt, hP.2.2⟩))).elim

theorem dp2_union_scale_cover {L : ℝ} (hL' : 0 < L') (hL'L : L' ≤ L) {a : Space n} {R : ℝ}
    (p : Σ j, (𝒞 j).index) :
    dp2_union_scale 𝒞 a R p ⊆
      {q : Space n × ℝ | q.1 ∈ Metric.ball a R ∩
          Metric.ball ((𝒞 p.1).center p.2) ((𝒞 p.1).radius p.2) ∧
        L⁻¹ * Metric.infDist q.1 (((𝒞 p.1).reference p.2).mono hL'.le hL'L).carrier ≤ q.2 ∧
          q.2 < (𝒞 p.1).radius p.2} := by
  rintro q ⟨hU, hS⟩
  obtain ⟨⟨_, hc⟩, hd, ht⟩ := (𝒞 p.1).scaleSet_cover p.2 hU
  refine ⟨⟨hS.1.2, hc⟩, ?_, ht⟩
  rw [Reference.carrier_mono]
  exact (mul_le_mul_of_nonneg_right (inv_anti₀ hL' hL'L) Metric.infDist_nonneg).trans hd

theorem dp2_union_bad_bound {K Kb : ℝ} {a : Space n} {R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hK' : 0 ≤ K') (hKb : 0 ≤ Kb)
    (hband : pointScaleMeasure μ ((Metric.ball a R ∩ μ.support) ×ˢ Ico r R) ≤
      ENNReal.ofReal (Kb * R ^ k))
    (hK : (N : ℝ) * K' + Kb ≤ K) :
    pointScaleMeasure μ (dp2_union_bad 𝒞 a R) ≤ ENNReal.ofReal (K * R ^ k) := by
  have hNr : 0 ≤ (N : ℝ) * K' * r ^ k :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hK') (pow_nonneg hr.le k)
  have hbR : 0 ≤ Kb * R ^ k := mul_nonneg hKb (pow_nonneg (hr.le.trans hrR) k)
  calc pointScaleMeasure μ (dp2_union_bad 𝒞 a R)
      ≤ pointScaleMeasure μ (⋃ j, (𝒞 j).badSet ∩ dp2_union_slab b r a R j) +
          pointScaleMeasure μ ((Metric.ball a R ∩ μ.support) ×ˢ Ico r R) :=
        measure_union_le _ _
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (K' * r ^ k) + ENNReal.ofReal (Kb * R ^ k) := by
        refine add_le_add ?_ hband
        calc pointScaleMeasure μ (⋃ j, (𝒞 j).badSet ∩ dp2_union_slab b r a R j)
            ≤ ∑ j, pointScaleMeasure μ ((𝒞 j).badSet ∩ dp2_union_slab b r a R j) :=
              measure_iUnion_fintype_le _ _
          _ ≤ ∑ _j : Fin N, ENNReal.ofReal (K' * r ^ k) :=
              Finset.sum_le_sum fun j _ => (measure_mono inter_subset_left).trans (𝒞 j).bad_bound
          _ = (N : ℝ≥0∞) * ENNReal.ofReal (K' * r ^ k) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal ((N : ℝ) * K' * r ^ k + Kb * R ^ k) := by
        rw [dp2_union_natCast_mul_ofReal, ← mul_assoc, ENNReal.ofReal_add hNr hbR]
    _ ≤ ENNReal.ofReal (K * R ^ k) :=
        ENNReal.ofReal_le_ofReal (dp2_union_real_le hr hrR hK' hK)

/-! ## Assembly -/

open scoped Classical in
/-- The `(K, L)`-regular mixed covering of `P(a, R)` combining the root certificates `𝒞 j`. -/
def dp2_union_covering {K L Kb : ℝ} (a : Space n) (R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (hK' : 0 ≤ K') (hL' : 0 < L') (hL'L : L' ≤ L) (hKb : 0 ≤ Kb)
    (hcov : μ.support ⊆ ⋃ j, Metric.ball (b j) r) (hball : ∀ j, dist (b j) a + L' * r ≤ L * R)
    (hband : pointScaleMeasure μ ((Metric.ball a R ∩ μ.support) ×ˢ Ico r R) ≤
      ENNReal.ofReal (Kb * R ^ k))
    (hK : (N : ℝ) * K' + Kb ≤ K) : RegularMixedCovering k K L μ a R where
  index := Set.range (dp2_union_code 𝒞)
  reference m :=
    ((𝒞 (dp2_union_equiv 𝒞 m).1).reference (dp2_union_equiv 𝒞 m).2).mono hL'.le hL'L
  center m := (𝒞 (dp2_union_equiv 𝒞 m).1).center (dp2_union_equiv 𝒞 m).2
  radius m := (𝒞 (dp2_union_equiv 𝒞 m).1).radius (dp2_union_equiv 𝒞 m).2
  badSet := dp2_union_bad 𝒞 a R
  scaleSet m := dp2_union_scale 𝒞 a R (dp2_union_equiv 𝒞 m)
  center_mem_support m := (𝒞 (dp2_union_equiv 𝒞 m).1).center_mem_support _
  radius_pos m := (𝒞 (dp2_union_equiv 𝒞 m).1).radius_pos _
  ball_subset m := ((𝒞 (dp2_union_equiv 𝒞 m).1).ball_subset _).trans
    (Metric.ball_subset_ball' (by rw [add_comm]; exact hball _))
  ball_meets_carrier m := by
    simpa only [Reference.carrier_mono] using
      (𝒞 (dp2_union_equiv 𝒞 m).1).ball_meets_carrier (dp2_union_equiv 𝒞 m).2
  root_packing := by
    have h := dp2_union_real_le (k := k) hr hrR hK' hK
    have hbR : 0 ≤ Kb * R ^ k := mul_nonneg hKb (pow_nonneg (hr.le.trans hrR) k)
    refine ((dp2_union_equiv 𝒞).tsum_eq
      (fun p => ENNReal.ofReal ((𝒞 p.1).radius p.2) ^ k)).trans_le
      ((dp2_union_radiusSum 𝒞).trans (ENNReal.ofReal_le_ofReal ?_))
    linarith
  local_packing z s hs := by
    have hNK : (N : ℝ) * K' ≤ K := by linarith
    refine ((dp2_union_equiv 𝒞).tsum_eq (fun p =>
        if (𝒞 p.1).center p.2 ∈ Metric.ball z s ∧ (𝒞 p.1).radius p.2 ≤ s then
          ENNReal.ofReal ((𝒞 p.1).radius p.2) ^ k else 0)).trans_le
      ((dp2_union_localSum 𝒞 z s hs).trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right hNK (pow_nonneg hs.le k)
  measurable_badSet := dp2_union_bad_measurable 𝒞 a R
  measurable_scaleSet m := dp2_union_scale_measurable 𝒞 a R _
  badSet_subset := dp2_union_bad_subset 𝒞 hr hrR
  scaleSet_subset m := dp2_union_scale_subset 𝒞 hrR _
  bad_inter_scale_null m := dp2_union_bad_inter_scale 𝒞 _
  scale_inter_scale_null m m' hmm' :=
    dp2_union_scale_inter_scale 𝒞 ((dp2_union_equiv 𝒞).injective.ne hmm')
  cover_null := by
    rw [(dp2_union_equiv 𝒞).surjective.iUnion_comp (dp2_union_scale 𝒞 a R)]
    exact dp2_union_cover 𝒞 hcov
  scaleSet_cover m := dp2_union_scale_cover 𝒞 hL' hL'L _
  bad_bound := dp2_union_bad_bound 𝒞 hr hrR hK' hKb hband hK

/-- **The bounded union** (`dp2_bounded_union`): the bounded union of root
certificates, with radius sum at most `N K' r^k`. -/
theorem dp2_bounded_union_proof : dp2_BoundedUnionStatement := by
  intro n k K' L' K L Kb μ a R r N b h hr hrR hK' hL' hL'L hKb hcov hball hband hK
  let 𝒞 : ∀ j, RegularMixedCovering k K' L' μ (b j) r := fun j => (h j).some
  refine ⟨dp2_union_covering 𝒞 a R hr hrR hK' hL' hL'L hKb hcov hball hband hK, ?_⟩
  exact ((dp2_union_equiv 𝒞).tsum_eq
    (fun p => ENNReal.ofReal ((𝒞 p.1).radius p.2) ^ k)).trans_le (dp2_union_radiusSum 𝒞)

end ParabolicRectifiability.QuantitativeCharacterization
