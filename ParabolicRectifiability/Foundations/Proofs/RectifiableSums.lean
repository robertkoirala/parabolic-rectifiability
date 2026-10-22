import ParabolicRectifiability.Foundations.Graphs

/-! # Proofs of the typed-rectifiability helpers

Proofs of the two rectifiability helpers `f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous`
and `f2i_isRegularlyRectifiableMeasure_sum`, with the same binders and conclusions:

* **Domination** `f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous_proof`: typed regular
  rectifiability passes to every measure `ν ≪ μ`. Keep `μ`'s graph family; `ν ≪ μ ≪ H_P^k`, and
  the `μ`-null complement of the carrier is `ν`-null.
* **Countable sums** `f2i_isRegularlyRectifiableMeasure_sum_proof`: a countable sum of measures, each zero or
  typed regularly rectifiable, is typed regularly rectifiable. Zero summands get the empty family;
  every graph is packaged with its own finite norm as `(ε, G) : Σ ε, Graph ε`; the countably many
  families are merged over `Σ i, I_i` and reindexed by a subset of `ℕ`
  (`Countable.exists_injective_nat`, `Set.iUnion_sigma`; the same reindexing is used in
  `exists_natSubset_reindex`); the complement of the
  merged carrier is null for every summand, hence for the sum (`Measure.sum_apply_eq_zero`,
  arbitrary sets).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

/-! ## Countable reindexing (copied from the template, generalized to a countable index) -/

/-- A family indexed by a countable type can be reindexed by a subset of `ℕ` with the same
range. -/
theorem f2i_exists_natSubset_reindex {ι α : Type*} [Countable ι] (f : ι → α) :
    ∃ (I : Set ℕ) (g : I → α), range g = range f := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  refine ⟨range e, fun p => f (Exists.choose p.2), ?_⟩
  ext a
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨⟨e i, i, rfl⟩, ?_⟩
    have h : e (Exists.choose (⟨i, rfl⟩ : e i ∈ range e)) = e i :=
      Exists.choose_spec (⟨i, rfl⟩ : e i ∈ range e)
    exact congrArg f (he h)

/-- Countably many families, each indexed by a subset of `ℕ`, merge into one family indexed by
a subset of `ℕ`, with the same union of images. -/
theorem f2i_exists_merge_families {ι α X : Type*} [Countable ι] (img : α → Set X)
    (I : ι → Set ℕ) (G : ∀ i, I i → α) :
    ∃ (J : Set ℕ) (g : J → α), (⋃ j, img (g j)) = ⋃ i, ⋃ p, img (G i p) := by
  obtain ⟨J, g, hg⟩ := f2i_exists_natSubset_reindex (fun s : Σ i, I i => G s.1 s.2)
  refine ⟨J, g, ?_⟩
  calc (⋃ j, img (g j)) = ⋃ s : Σ i, I i, img (G s.1 s.2) := by
        rw [← biUnion_range (f := g) (g := img), hg, biUnion_range]
    _ = ⋃ i, ⋃ p, img (G i p) := iUnion_sigma (fun s : Σ i, I i => img (G s.1 s.2))

/-! ## Carriers of countable sums -/

/-- One family of packaged graphs: if every summand vanishes off the images of some family
indexed by a subset of `ℕ`, then so does the sum, for the merged family. -/
theorem f2i_sum_carried_one {ι α X : Type*} [Countable ι] [MeasurableSpace X]
    (img : α → Set X) (ν : ι → Measure X)
    (h : ∀ i, ∃ (I : Set ℕ) (g : I → α), ν i (⋃ p, img (g p))ᶜ = 0) :
    ∃ (J : Set ℕ) (g : J → α), Measure.sum ν (⋃ j, img (g j))ᶜ = 0 := by
  choose I G hG using h
  obtain ⟨J, g, hg⟩ := f2i_exists_merge_families img I G
  refine ⟨J, g, Measure.sum_apply_eq_zero.2 fun i => measure_mono_null ?_ (hG i)⟩
  rw [hg]
  exact compl_subset_compl.2 (subset_iUnion (fun i => ⋃ p, img (G i p)) i)

/-- Two families of packaged graphs (the mixed carrier): the same statement for the union of
the images of a family of each kind. -/
theorem f2i_sum_carried_two {ι α β X : Type*} [Countable ι] [MeasurableSpace X]
    (img₁ : α → Set X) (img₂ : β → Set X) (ν : ι → Measure X)
    (h : ∀ i, ∃ (I : Set ℕ) (g : I → α) (J : Set ℕ) (f : J → β),
      ν i ((⋃ p, img₁ (g p)) ∪ ⋃ q, img₂ (f q))ᶜ = 0) :
    ∃ (I : Set ℕ) (g : I → α) (J : Set ℕ) (f : J → β),
      Measure.sum ν ((⋃ p, img₁ (g p)) ∪ ⋃ q, img₂ (f q))ᶜ = 0 := by
  choose I G J F hGF using h
  obtain ⟨I', g, hg⟩ := f2i_exists_merge_families img₁ I G
  obtain ⟨J', f, hf⟩ := f2i_exists_merge_families img₂ J F
  refine ⟨I', g, J', f, Measure.sum_apply_eq_zero.2 fun i => measure_mono_null ?_ (hGF i)⟩
  rw [hg, hf]
  exact compl_subset_compl.2 (union_subset_union
    (subset_iUnion (fun i => ⋃ p, img₁ (G i p)) i)
    (subset_iUnion (fun i => ⋃ q, img₂ (F i q)) i))

/-- The carrier conjunct of a zero measure: the empty families. -/
theorem f2i_isCarriedByFiniteNormGraphs_zero {n k : ℕ} (T : FamilyKind) :
    IsCarriedByFiniteNormGraphs T k (0 : Measure (Space n)) := by
  have hI : ∀ p : (∅ : Set ℕ), False := fun p => p.2
  cases T <;> dsimp only [IsCarriedByFiniteNormGraphs]
  · exact ⟨∅, fun p => (hI p).elim, fun p => (hI p).elim, by simp⟩
  · exact ⟨∅, fun p => (hI p).elim, fun p => (hI p).elim, by simp⟩
  · exact ⟨∅, ∅, fun p => (hI p).elim, fun p => (hI p).elim, fun p => (hI p).elim,
      fun p => (hI p).elim, by simp⟩

/-- The carrier conjunct passes to countable sums of carried measures. -/
theorem f2i_isCarriedByFiniteNormGraphs_sum {n k : ℕ} {ι : Type*} [Countable ι]
    (T : FamilyKind) (ν : ι → Measure (Space n))
    (hν : ∀ i, IsCarriedByFiniteNormGraphs T k (ν i)) :
    IsCarriedByFiniteNormGraphs T k (Measure.sum ν) := by
  cases T <;> dsimp only [IsCarriedByFiniteNormGraphs] at hν ⊢
  case horizontal =>
      obtain ⟨J, g, hg⟩ := f2i_sum_carried_one
        (fun s : Σ ε : ℝ, HorizontalGraph n k ε => s.2.image) ν (fun i => by
          obtain ⟨I, ε, H, h⟩ := hν i
          exact ⟨I, fun p => ⟨ε p, H p⟩, h⟩)
      exact ⟨J, fun j => (g j).1, fun j => (g j).2, hg⟩
  case vertical =>
      obtain ⟨J, g, hg⟩ := f2i_sum_carried_one
        (fun s : Σ ε : ℝ, GeneralRegularVerticalGraph n k ε => s.2.image) ν (fun i => by
          obtain ⟨I, ε, V, h⟩ := hν i
          exact ⟨I, fun p => ⟨ε p, V p⟩, h⟩)
      exact ⟨J, fun j => (g j).1, fun j => (g j).2, hg⟩
  case mixed =>
      obtain ⟨I, g, J, f, hgf⟩ := f2i_sum_carried_two
        (fun s : Σ ε : ℝ, HorizontalGraph n k ε => s.2.image)
        (fun s : Σ ε : ℝ, GeneralRegularVerticalGraph n k ε => s.2.image) ν (fun i => by
          obtain ⟨I, J, εH, H, εV, V, h⟩ := hν i
          exact ⟨I, fun p => ⟨εH p, H p⟩, J, fun q => ⟨εV q, V q⟩, h⟩)
      exact ⟨I, J, fun i => (g i).1, fun i => (g i).2, fun j => (f j).1, fun j => (f j).2, hgf⟩

/-! ## The two statements -/

/-- **Domination** (proof of `f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous`). -/
theorem f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous_proof
    {n k : ℕ} (T : FamilyKind) {μ ν : Measure (Space n)}
    (hμ : IsRegularlyRectifiableMeasure T k μ) (hνμ : ν ≪ μ) :
    IsRegularlyRectifiableMeasure T k ν := by
  unfold IsRegularlyRectifiableMeasure at hμ ⊢
  obtain ⟨hac, hcar⟩ := hμ
  refine ⟨hνμ.trans hac, ?_⟩
  cases T <;> dsimp only [IsCarriedByFiniteNormGraphs] at hcar ⊢
  case horizontal =>
      obtain ⟨I, ε, H, h⟩ := hcar
      exact ⟨I, ε, H, hνμ h⟩
  case vertical =>
      obtain ⟨J, ε, V, h⟩ := hcar
      exact ⟨J, ε, V, hνμ h⟩
  case mixed =>
      obtain ⟨I, J, εH, H, εV, V, h⟩ := hcar
      exact ⟨I, J, εH, H, εV, V, hνμ h⟩

/-- **Countable sums** (proof of `f2i_isRegularlyRectifiableMeasure_sum`). -/
theorem f2i_isRegularlyRectifiableMeasure_sum_proof
    {n k : ℕ} {ι : Type*} [Countable ι]
    (T : FamilyKind) (ν : ι → Measure (Space n))
    (hν : ∀ i, ν i ≠ 0 →
      IsRegularlyRectifiableMeasure T k (ν i)) :
    IsRegularlyRectifiableMeasure T k (Measure.sum ν) := by
  classical
  unfold IsRegularlyRectifiableMeasure at hν ⊢
  refine ⟨Measure.absolutelyContinuous_sum_left fun i => ?_,
    f2i_isCarriedByFiniteNormGraphs_sum T ν fun i => ?_⟩
  · by_cases h0 : ν i = 0
    · rw [h0]
      exact Measure.AbsolutelyContinuous.zero _
    · exact (hν i h0).1
  · by_cases h0 : ν i = 0
    · rw [h0]
      exact f2i_isCarriedByFiniteNormGraphs_zero T
    · exact (hν i h0).2

end ParabolicRectifiability.Foundations
