import ParabolicRectifiability.Decomposition.Interfaces

/-! # Compact typed pieces

The compactification step of the positive-threshold decomposition, proving
`exists_compact_typed_pieces` (as `compactTypedPieces_exists`).

* `exists_typed_borel_partition`: a Borel partition of the compact refined set into a horizontal and a
  vertical part. Points on horizontal cores are horizontal, the remaining points on
  vertical cores are vertical, and the Hausdorff-null leftover is given to one
  available, family-compatible type. Each part inherits graph covers at every
  tolerance from the countably many cores; the added leftover is Hausdorff-null.
* `exists_isCompact_subset_measure_sdiff_le`: compact inner approximation of each part with respect to the original finite
  inner-regular source, losing less than `M/2` per part.

The losses are `Cg*M` (geometric carrier), `Cd*M` (density refinement) and at most `M`
(compactification), so the total is `(Cg + Cd + 1) * M`. The compact typed sets are
chosen before any graph tolerance.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ParabolicRectifiability

/-! ## Graph covers of subsets of countable unions, up to a Hausdorff-null set -/

/-- A set inside a countable union of sets with countable graph covers, up to a
Hausdorff-null set, again has a countable graph cover indexed by a subset of `ℕ`.
The graph type is arbitrary, so this applies to horizontal and vertical graphs. -/
theorem exists_graphCover_of_subset_iUnion {n k : ℕ} {ι β : Type*} [Countable ι]
    (img : β → Set (Space n)) (C : ι → Set (Space n))
    (hC : ∀ i, ∃ (I : Set ℕ) (g : I → β), hausdorffP n k (C i \ ⋃ j, img (g j)) = 0)
    {K N : Set (Space n)} (hK : K ⊆ (⋃ i, C i) ∪ N) (hN : hausdorffP n k N = 0) :
    ∃ (J : Set ℕ) (g : J → β), hausdorffP n k (K \ ⋃ j, img (g j)) = 0 := by
  choose I g hg using hC
  obtain ⟨e, he⟩ := Countable.exists_injective_nat (Σ i, I i)
  refine ⟨range e, fun m => g (Classical.choose (mem_range.mp m.2)).1
    (Classical.choose (mem_range.mp m.2)).2, ?_⟩
  apply measure_mono_null _ (measure_union_null hN (measure_iUnion_null hg))
  rintro x ⟨hxK, hx⟩
  rcases hK hxK with hxC | hxN
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hxC
    refine Or.inr (mem_iUnion.mpr ⟨i, hi, fun hxi => hx ?_⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxi
    have hm : e ⟨i, j⟩ ∈ range e := ⟨⟨i, j⟩, rfl⟩
    have hc : Classical.choose (mem_range.mp hm) = ⟨i, j⟩ :=
      he (Classical.choose_spec (mem_range.mp hm))
    refine mem_iUnion.mpr ⟨⟨e ⟨i, j⟩, hm⟩, ?_⟩
    show x ∈ img (g (Classical.choose (mem_range.mp hm)).1
      (Classical.choose (mem_range.mp hm)).2)
    rw [hc]
    exact hj
  · exact Or.inl hxN

theorem iUnion_eq_empty_of_index_eq_empty {X : Type*} {I : Set ℕ} (C : I → Set X)
    (h : I = ∅) : (⋃ i, C i) = ∅ := by
  subst h
  exact iUnion_eq_empty.mpr fun i => absurd i.2 (notMem_empty _)

/-- One of the two types is available and compatible with the family. -/
theorem available_type_of_nonempty {n k : ℕ} {T : FamilyKind} (hT : Nonempty (Models n k T)) :
    (T ≠ .vertical ∧ 1 ≤ k ∧ k ≤ n) ∨ (T ≠ .horizontal ∧ 2 ≤ k ∧ k ≤ n + 2) := by
  cases T with
  | horizontal => exact Or.inl ⟨by simp, HorizontalModel.nonempty_iff.mp hT⟩
  | vertical => exact Or.inr ⟨by simp, VerticalModel.nonempty_iff.mp hT⟩
  | mixed =>
    rcases AdmissibleModel.nonempty_iff.mp hT with h | h
    · exact Or.inl ⟨by simp, h⟩
    · exact Or.inr ⟨by simp, h⟩

/-! ## Borel type assignment with Hausdorff-null exceptions -/

/-- A Borel partition of a compact subset of the geometric carrier into typed
parts with graph covers at every tolerance. -/
theorem exists_typed_borel_partition {n k : ℕ} {T : FamilyKind} {ν : Measure (Space n)}
    {M Cg : ℝ} (G : GeometricExtraction ν k T M Cg)
    (hH : ∀ i ε, 0 < ε → HasHorizontalGraphCover k (G.horizontalCore i) ε)
    (hV : ∀ i ε, 0 < ε → HasRegularVerticalGraphCover k (G.verticalCore i) ε)
    (hAvail : (T ≠ .vertical ∧ 1 ≤ k ∧ k ≤ n) ∨ (T ≠ .horizontal ∧ 2 ≤ k ∧ k ≤ n + 2))
    {K : Set (Space n)} (hK : IsCompact K) (hKG : K ⊆ G.carrier) :
    ∃ H V : Set (Space n), MeasurableSet H ∧ MeasurableSet V ∧ H ⊆ K ∧ V ⊆ K ∧
      K ⊆ H ∪ V ∧ Disjoint H V ∧
      ((¬ (1 ≤ k ∧ k ≤ n) ∨ T = .vertical) → H = ∅) ∧
      ((¬ (2 ≤ k ∧ k ≤ n + 2) ∨ T = .horizontal) → V = ∅) ∧
      (∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k H ε) ∧
      (∀ ε : ℝ, 0 < ε → HasRegularVerticalGraphCover k V ε) := by
  set Hc := ⋃ i, G.horizontalCore i with hHc
  set Vc := ⋃ i, G.verticalCore i with hVc
  have hHm : MeasurableSet Hc :=
    MeasurableSet.iUnion fun i => (G.horizontal_certificate i).1.isClosed.measurableSet
  have hVm : MeasurableSet Vc :=
    MeasurableSet.iUnion fun i => (G.vertical_certificate i).2.2.1.isClosed.measurableSet
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hRnull : hausdorffP n k (K \ (Hc ∪ Vc)) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hKG) G.null_remainder
  -- the cores vanish for unavailable or family-incompatible types
  have hHc0 : (¬ (1 ≤ k ∧ k ≤ n) ∨ T = .vertical) → Hc = ∅ := fun h =>
    iUnion_eq_empty_of_index_eq_empty _ (G.horizontal_unavailable h.symm)
  have hVc0 : (¬ (2 ≤ k ∧ k ≤ n + 2) ∨ T = .horizontal) → Vc = ∅ := fun h =>
    iUnion_eq_empty_of_index_eq_empty _ (G.vertical_unavailable h.symm)
  -- graph covers inherited from the cores
  have hcovH : ∀ {S N : Set (Space n)}, S ⊆ Hc ∪ N → hausdorffP n k N = 0 →
      ∀ ε : ℝ, 0 < ε → HasHorizontalGraphCover k S ε := fun hS hN ε hε =>
    exists_graphCover_of_subset_iUnion HorizontalGraph.image (fun i => G.horizontalCore i)
      (fun i => hH i ε hε) hS hN
  have hcovV : ∀ {S N : Set (Space n)}, S ⊆ Vc ∪ N → hausdorffP n k N = 0 →
      ∀ ε : ℝ, 0 < ε → HasRegularVerticalGraphCover k S ε := fun hS hN ε hε =>
    exists_graphCover_of_subset_iUnion RegularVerticalGraph.image (fun i => G.verticalCore i)
      (fun i => hV i ε hε) hS hN
  rcases hAvail with hA | hA
  · -- the leftover is horizontal
    refine ⟨(K ∩ Hc) ∪ K \ (Hc ∪ Vc), (K ∩ Vc) \ Hc, (hKm.inter hHm).union
      (hKm.diff (hHm.union hVm)), (hKm.inter hVm).diff hHm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact union_subset inter_subset_left sdiff_subset
    · exact sdiff_subset.trans inter_subset_left
    · intro x hx
      by_cases h1 : x ∈ Hc
      · exact Or.inl (Or.inl ⟨hx, h1⟩)
      · by_cases h2 : x ∈ Vc
        · exact Or.inr ⟨⟨hx, h2⟩, h1⟩
        · exact Or.inl (Or.inr ⟨hx, fun h => h.elim h1 h2⟩)
    · rw [disjoint_left]
      rintro x (hx | hx) ⟨⟨_, hxV⟩, hxH⟩
      · exact hxH hx.2
      · exact hx.2 (Or.inr hxV)
    · intro h
      exfalso
      rcases h with h | h
      · exact h hA.2
      · exact hA.1 h
    · intro h
      rw [hVc0 h]
      simp
    · exact hcovH (union_subset_union inter_subset_right subset_rfl) hRnull
    · exact hcovV (fun x hx => Or.inl hx.1.2) (measure_empty (μ := hausdorffP n k))
  · -- the leftover is vertical
    refine ⟨K ∩ Hc, ((K ∩ Vc) \ Hc) ∪ K \ (Hc ∪ Vc), hKm.inter hHm,
      ((hKm.inter hVm).diff hHm).union (hKm.diff (hHm.union hVm)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact inter_subset_left
    · exact union_subset (sdiff_subset.trans inter_subset_left) sdiff_subset
    · intro x hx
      by_cases h1 : x ∈ Hc
      · exact Or.inl ⟨hx, h1⟩
      · by_cases h2 : x ∈ Vc
        · exact Or.inr (Or.inl ⟨⟨hx, h2⟩, h1⟩)
        · exact Or.inr (Or.inr ⟨hx, fun h => h.elim h1 h2⟩)
    · rw [disjoint_left]
      rintro x ⟨_, hxH⟩ (hx | hx)
      · exact hx.2 hxH
      · exact hx.2 (Or.inl hxH)
    · intro h
      rw [hHc0 h]
      simp
    · intro h
      exfalso
      rcases h with h | h
      · exact h hA.2
      · exact hA.1 h
    · exact hcovH (fun x hx => Or.inl hx.2) (measure_empty (μ := hausdorffP n k))
    · refine hcovV ?_ hRnull
      rintro x (hx | hx)
      · exact Or.inl hx.1.2
      · exact Or.inr hx

/-! ## Compact approximation with respect to the original source -/

/-- Inner approximation by a compact subset for the original finite
inner-regular source, with loss at most `M/2`. -/
theorem exists_isCompact_subset_measure_sdiff_le {n : ℕ} (ν : Measure (Space n))
    [IsFiniteMeasure ν] [ν.InnerRegular] {A : Set (Space n)} (hA : MeasurableSet A)
    {M : ℝ} (hM : 0 < M) :
    ∃ B, B ⊆ A ∧ IsCompact B ∧ ν (A \ B) ≤ ENNReal.ofReal (M / 2) := by
  obtain ⟨B, hBA, hB, hlt⟩ := hA.exists_isCompact_sdiff_lt (measure_ne_top ν A)
    (ENNReal.ofReal_pos.mpr (half_pos hM)).ne'
  exact ⟨B, hBA, hB, hlt.le⟩

/-! ## Assembly -/

/-- Compactification: the statement `exists_compact_typed_pieces`. -/
theorem compactTypedPieces_exists {n k : ℕ} (_hk : 1 ≤ k) (_hkn : k < n + 2)
    (T : FamilyKind) (hT : Nonempty (Models n k T))
    (ν : Measure (Space n)) (hν : IsFiniteMeasure ν) (hreg : ν.InnerRegular)
    (M Cg Cd : ℝ) (hM : 0 < M) (hCg : 0 < Cg) (hCd : 0 < Cd)
    (G : GeometricExtraction ν k T M Cg) (D : DensityRefinement ν k M Cd G.carrier)
    (hH : ∀ i ε, 0 < ε → HasHorizontalGraphCover k (G.horizontalCore i) ε)
    (hV : ∀ i ε, 0 < ε → HasRegularVerticalGraphCover k (G.verticalCore i) ε) :
    Nonempty (CompactTypedPieces ν k T M (Cg + Cd + 1) D.set) := by
  obtain ⟨H, V, hHm, hVm, hHK, hVK, hKHV, hdisj, hH0, hV0, hHg, hVg⟩ :=
    exists_typed_borel_partition G hH hV (available_type_of_nonempty hT) D.compact
      D.subset
  obtain ⟨A, hAH, hAc, hAloss⟩ := exists_isCompact_subset_measure_sdiff_le ν hHm hM
  obtain ⟨B, hBV, hBc, hBloss⟩ := exists_isCompact_subset_measure_sdiff_le ν hVm hM
  -- loss outside the refined compact set: `Cd*M + Cg*M`
  have hDm : MeasurableSet D.setᶜ := D.compact.isClosed.measurableSet.compl
  have hloss1 : ν D.setᶜ ≤ ENNReal.ofReal (Cd * M) + ENNReal.ofReal (Cg * M) := by
    calc
      ν D.setᶜ ≤ ν (D.setᶜ ∩ G.carrier) + ν (D.setᶜ \ G.carrier) :=
        measure_le_inter_add_sdiff ν _ _
      _ ≤ ENNReal.ofReal (Cd * M) + ENNReal.ofReal (Cg * M) := by
        refine add_le_add ?_ ((measure_mono (fun x hx => hx.2)).trans G.loss)
        rw [← Measure.restrict_apply hDm]
        exact D.loss
  -- loss inside the refined compact set: at most `M`
  have hloss2 : ν (D.set \ (A ∪ B)) ≤ ENNReal.ofReal (M / 2) + ENNReal.ofReal (M / 2) := by
    calc
      ν (D.set \ (A ∪ B)) ≤ ν ((H \ A) ∪ (V \ B)) := by
        apply measure_mono
        rintro x ⟨hxK, hxAB⟩
        rcases hKHV hxK with hx | hx
        · exact Or.inl ⟨hx, fun h => hxAB (Or.inl h)⟩
        · exact Or.inr ⟨hx, fun h => hxAB (Or.inr h)⟩
      _ ≤ ν (H \ A) + ν (V \ B) := measure_union_le _ _
      _ ≤ _ := add_le_add hAloss hBloss
  have hsum : ENNReal.ofReal (Cd * M) + ENNReal.ofReal (Cg * M) +
      (ENNReal.ofReal (M / 2) + ENNReal.ofReal (M / 2)) =
      ENNReal.ofReal ((Cg + Cd + 1) * M) := by
    have h1 : ENNReal.ofReal (Cd * M + Cg * M) =
        ENNReal.ofReal (Cd * M) + ENNReal.ofReal (Cg * M) :=
      ENNReal.ofReal_add (mul_pos hCd hM).le (mul_pos hCg hM).le
    have h2 : ENNReal.ofReal (M / 2 + M / 2) = ENNReal.ofReal (M / 2) + ENNReal.ofReal (M / 2) :=
      ENNReal.ofReal_add (half_pos hM).le (half_pos hM).le
    have h3 : ENNReal.ofReal (Cd * M + Cg * M + (M / 2 + M / 2)) =
        ENNReal.ofReal (Cd * M + Cg * M) + ENNReal.ofReal (M / 2 + M / 2) :=
      ENNReal.ofReal_add (add_pos (mul_pos hCd hM) (mul_pos hCg hM)).le
        (add_pos (half_pos hM) (half_pos hM)).le
    rw [← h1, ← h2, ← h3]
    congr 1
    ring
  refine ⟨{
    horizontal := A
    vertical := B
    horizontal_compact := hAc
    vertical_compact := hBc
    horizontal_subset := hAH.trans hHK
    vertical_subset := hBV.trans hVK
    disjoint := hdisj.mono hAH hBV
    loss := ?_
    horizontal_unavailable := fun h => subset_eq_empty hAH (hH0 (Or.inl h))
    vertical_unavailable := fun h => subset_eq_empty hBV (hV0 (Or.inl h))
    family := ⟨fun h => subset_eq_empty hBV (hV0 (Or.inr h)),
      fun h => subset_eq_empty hAH (hH0 (Or.inr h))⟩
    horizontal_graphs := ?_
    vertical_graphs := ?_ }⟩
  · rw [← hsum]
    calc
      ν (A ∪ B)ᶜ ≤ ν (D.setᶜ ∪ (D.set \ (A ∪ B))) := by
        apply measure_mono
        intro x hx
        by_cases hxD : x ∈ D.set
        · exact Or.inr ⟨hxD, hx⟩
        · exact Or.inl hxD
      _ ≤ ν D.setᶜ + ν (D.set \ (A ∪ B)) := measure_union_le _ _
      _ ≤ _ := add_le_add hloss1 hloss2
  · intro ε hε
    have hc := hHg ε hε
    unfold HasHorizontalGraphCover at hc ⊢
    obtain ⟨I, g, hg⟩ := hc
    exact ⟨I, g, measure_mono_null (sdiff_subset_sdiff_left hAH) hg⟩
  · intro ε hε
    have hc := hVg ε hε
    unfold HasRegularVerticalGraphCover at hc ⊢
    obtain ⟨I, g, hg⟩ := hc
    exact ⟨I, g, measure_mono_null (sdiff_subset_sdiff_left hBV) hg⟩

end ParabolicRectifiability
