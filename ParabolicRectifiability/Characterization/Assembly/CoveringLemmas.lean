import ParabolicRectifiability.Foundations.Graphs
import ParabolicRectifiability.Foundations.Density
import ParabolicRectifiability.Foundations.Carriers
import ParabolicRectifiability.Measure.BetaLaws

/-! # Elementary covering lemmas for the characterization

Elementary bookkeeping used in the proof of the branches of the characterization
(`intrinsic_sufficiency_skeleton`, `necessity_skeleton` and the typed refinements):

* reindexing countably many countable graph families by one subset of `ℕ`;
* combining typed set covers of countably many pieces into a typed measure cover, and a
  countable family of Borel envelopes into a Borel sigma-finite Hausdorff carrier;
* almost-everywhere statements on countable unions of carrying sets;
* the comparisons `β_{mixed} ≤ β_{H}, β_{V}`, monotonicity of the square in its endpoint,
  `Θ_* ≤ Θ^*`, and the availability of a family that has a graph.

No mathematical hypothesis is introduced; these are elementary arithmetic and monotonicity
steps.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-! ## Countable reindexing -/

/-- A family indexed by a countable type can be reindexed by a subset of `ℕ` with the same
range. -/
theorem exists_natSubset_reindex {ι α : Type*} [Countable ι] (f : ι → α) :
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

/-- Unions of images agree for two families with the same range. -/
theorem iUnion_eq_of_range_eq {ι κ α X : Type*} {g : κ → α} {f : ι → α}
    (h : range g = range f) (img : α → Set X) : (⋃ j, img (g j)) = ⋃ i, img (f i) := by
  rw [← biUnion_range (f := g) (g := img), h, biUnion_range]

/-- Countably many countable families, each indexed by a subset of `ℕ`, merge into one
family indexed by a subset of `ℕ`, with the same union of images. -/
theorem exists_merge_families {α X : Type*} (img : α → Set X) (I : ℕ → Set ℕ)
    (G : ∀ m, I m → α) :
    ∃ (J : Set ℕ) (g : J → α), (⋃ j, img (g j)) = ⋃ m, ⋃ i, img (G m i) := by
  obtain ⟨J, g, hg⟩ := exists_natSubset_reindex (fun s : Σ m, I m => G s.1 s.2)
  exact ⟨J, g, (iUnion_eq_of_range_eq hg img).trans
    (iUnion_sigma (fun s : Σ m, I m => img (G s.1 s.2)))⟩

/-- A countable family of sets can be listed as a sequence, padding with empty sets. -/
theorem exists_nat_family {ι X : Type*} [Countable ι] (s : ι → Set X) :
    ∃ F : ℕ → Set X, (∀ j, F j = ∅ ∨ ∃ i, F j = s i) ∧ (⋃ j, F j) = ⋃ i, s i := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option ι)
  refine ⟨fun j => Option.elim (f j) ∅ s, fun j => ?_, ?_⟩
  · show Option.elim (f j) ∅ s = ∅ ∨ ∃ i, Option.elim (f j) ∅ s = s i
    cases f j with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl⟩
  · ext z
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      revert hj
      cases f j with
      | none => intro hj; simp at hj
      | some i => intro hj; exact ⟨i, hj⟩
    · rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := hf (some i)
      refine ⟨j, ?_⟩
      rw [hj]
      exact hi

/-! ## Null sets, carriers and covers -/

/-- If `μ ≪ ν`, the pieces `F m` carry `μ`, and `U m` covers `F m` modulo `ν`, then the
union of the `U m` carries `μ`. -/
theorem measure_compl_iUnion_eq_zero_of_cover {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hμν : μ ≪ ν) (F U : ℕ → Set X) (hF : μ (⋃ m, F m)ᶜ = 0)
    (hU : ∀ m, ν (F m \ U m) = 0) : μ (⋃ m, U m)ᶜ = 0 := by
  refine measure_mono_null ?_ (measure_union_null hF (measure_iUnion_null fun m => hμν (hU m)))
  intro z hz
  rw [mem_compl_iff, mem_iUnion, not_exists] at hz
  by_cases hzF : z ∈ ⋃ m, F m
  · obtain ⟨m, hm⟩ := mem_iUnion.1 hzF
    exact Or.inr (mem_iUnion.2 ⟨m, hm, hz m⟩)
  · exact Or.inl hzF

/-- A property holding a.e. on each of countably many sets holds a.e. on their union. -/
theorem ae_mem_iUnion_imp {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*}
    [Countable ι] (S : ι → Set X) {P : X → Prop} (hP : ∀ i, ∀ᵐ z ∂μ, z ∈ S i → P z) :
    ∀ᵐ z ∂μ, z ∈ ⋃ i, S i → P z := by
  filter_upwards [ae_all_iff.2 hP] with z hz hzU
  obtain ⟨i, hi⟩ := mem_iUnion.1 hzU
  exact hz i hi

/-- A property holding a.e. on each of countably many sets that carry `μ` holds a.e. -/
theorem ae_of_cover {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*}
    [Countable ι] (S : ι → Set X) (hS : μ (⋃ i, S i)ᶜ = 0) {P : X → Prop}
    (hP : ∀ i, ∀ᵐ z ∂μ, z ∈ S i → P z) : ∀ᵐ z ∂μ, P z := by
  have hmem : ∀ᵐ z ∂μ, z ∈ ⋃ i, S i := mem_ae_iff.2 hS
  filter_upwards [hmem, ae_mem_iUnion_imp S hP] with z hz hzP
  exact hzP hz

/-- Countably many carrying sets, each inside a Borel set of locally finite Hausdorff
measure, give a Borel sigma-finite `H_P^k` carrier. -/
theorem hasBorelSigmaFiniteHausdorffCarrier_of_cover {n k : ℕ} {μ : Measure (Space n)}
    {ι : Type*} [Countable ι] (S : ι → Set (Space n)) (hS : μ (⋃ i, S i)ᶜ = 0)
    (B : ι → Set (Space n)) (hSB : ∀ i, S i ⊆ B i) (hBm : ∀ i, MeasurableSet (B i))
    (hBfin : ∀ i (q : Space n) (R : ℝ), hausdorffP n k (B i ∩ Metric.ball q R) < ⊤) :
    HasBorelSigmaFiniteHausdorffCarrier k μ := by
  obtain ⟨F, hF, hFU⟩ :=
    exists_nat_family (fun p : ι × ℕ => B p.1 ∩ Metric.ball (point 0 0) (p.2 : ℝ))
  refine ⟨F, fun j => ?_, fun j => ?_, ?_⟩
  · rcases hF j with h | ⟨p, h⟩
    · rw [h]
      exact MeasurableSet.empty
    · rw [h]
      exact (hBm p.1).inter measurableSet_ball
  · rcases hF j with h | ⟨p, h⟩
    · rw [h, measure_empty]
      exact ENNReal.zero_lt_top
    · rw [h]
      exact hBfin p.1 _ _
  · refine measure_mono_null ?_ hS
    intro z hz
    rw [mem_compl_iff] at hz ⊢
    intro hzS
    apply hz
    rw [hFU]
    obtain ⟨i, hi⟩ := mem_iUnion.1 hzS
    obtain ⟨N, hN⟩ := exists_nat_gt (dist z (point 0 0))
    exact mem_iUnion.2 ⟨(i, N), hSB i hi, Metric.mem_ball.2 hN⟩

/-- A typed set cover of a Hausdorff-null set exists at every tolerance (empty families). -/
theorem hasTypedGraphCover_of_null {n k : ℕ} (T : FamilyKind) {K : Set (Space n)} (ε : ℝ)
    (hK : hausdorffP n k K = 0) : HasTypedGraphCover T k K ε := by
  have hdiff : ∀ U : Set (Space n), hausdorffP n k (K \ U) = 0 :=
    fun U => measure_mono_null (fun z hz => hz.1) hK
  cases T with
  | horizontal =>
    exact ⟨∅, fun i => absurd i.2 (notMem_empty _), hdiff _⟩
  | vertical =>
    exact ⟨∅, fun i => absurd i.2 (notMem_empty _), hdiff _⟩
  | mixed =>
    exact ⟨∅, ∅, fun i => absurd i.2 (notMem_empty _), fun i => absurd i.2 (notMem_empty _),
      hdiff _⟩

/-- A typed measure cover of the zero measure exists at every tolerance (empty families). -/
theorem hasTypedMeasureCover_zero {n k : ℕ} (T : FamilyKind) (ε : ℝ) :
    HasTypedMeasureCover T k (0 : Measure (Space n)) ε := by
  cases T with
  | horizontal =>
    exact ⟨∅, fun i => absurd i.2 (notMem_empty _), by simp⟩
  | vertical =>
    exact ⟨∅, fun i => absurd i.2 (notMem_empty _), by simp⟩
  | mixed =>
    exact ⟨∅, ∅, fun i => absurd i.2 (notMem_empty _), fun i => absurd i.2 (notMem_empty _),
      by simp⟩

/-- Typed set covers, modulo `H_P^k`, of countably many pieces carrying `μ ≪ H_P^k` give a
typed measure cover of `μ` at the same tolerance. -/
theorem hasTypedMeasureCover_of_setCovers {n k : ℕ} {T : FamilyKind} {ε : ℝ}
    {μ : Measure (Space n)} (hμ : μ ≪ hausdorffP n k) (F : ℕ → Set (Space n))
    (hF : μ (⋃ m, F m)ᶜ = 0) (hcov : ∀ m, HasTypedGraphCover T k (F m) ε) :
    HasTypedMeasureCover T k μ ε := by
  cases T with
  | horizontal =>
    have hcov' : ∀ m, ∃ (I : Set ℕ) (G : I → HorizontalGraph n k ε),
        hausdorffP n k (F m \ ⋃ i, (G i).image) = 0 := hcov
    choose I G hG using hcov'
    obtain ⟨J, g, hg⟩ := exists_merge_families (fun H : HorizontalGraph n k ε => H.image) I G
    exact ⟨J, g, (congrArg (fun s : Set (Space n) => μ sᶜ) hg).trans
      (measure_compl_iUnion_eq_zero_of_cover hμ F (fun m => ⋃ i, (G m i).image) hF hG)⟩
  | vertical =>
    have hcov' : ∀ m, ∃ (I : Set ℕ) (G : I → GeneralRegularVerticalGraph n k ε),
        hausdorffP n k (F m \ ⋃ i, (G i).image) = 0 := hcov
    choose I G hG using hcov'
    obtain ⟨J, g, hg⟩ :=
      exists_merge_families (fun V : GeneralRegularVerticalGraph n k ε => V.image) I G
    exact ⟨J, g, (congrArg (fun s : Set (Space n) => μ sᶜ) hg).trans
      (measure_compl_iUnion_eq_zero_of_cover hμ F (fun m => ⋃ i, (G m i).image) hF hG)⟩
  | mixed =>
    have hcov' : ∀ m, ∃ (I I' : Set ℕ) (H : I → HorizontalGraph n k ε)
        (V : I' → GeneralRegularVerticalGraph n k ε),
        hausdorffP n k (F m \ ((⋃ i, (H i).image) ∪ ⋃ j, (V j).image)) = 0 := hcov
    choose I I' H V hHV using hcov'
    obtain ⟨J, g, hg⟩ := exists_merge_families (fun G : HorizontalGraph n k ε => G.image) I H
    obtain ⟨J', g', hg'⟩ :=
      exists_merge_families (fun G : GeneralRegularVerticalGraph n k ε => G.image) I' V
    have hU : ((⋃ j, (g j).image) ∪ ⋃ j, (g' j).image) =
        ⋃ m, ((⋃ i, (H m i).image) ∪ ⋃ j, (V m j).image) := by
      rw [iUnion_union_distrib]
      exact congrArg₂ (· ∪ ·) hg hg'
    exact ⟨J, J', g, g', (congrArg (fun s : Set (Space n) => μ sᶜ) hU).trans
      (measure_compl_iUnion_eq_zero_of_cover hμ F
        (fun m => (⋃ i, (H m i).image) ∪ ⋃ j, (V m j).image) hF hHV)⟩

/-- A typed measure cover at one tolerance is a carrier by typed graphs of finite norm. -/
theorem isCarriedByFiniteNormGraphs_of_hasTypedMeasureCover {n k : ℕ} {T : FamilyKind}
    {μ : Measure (Space n)} {ε : ℝ} (h : HasTypedMeasureCover T k μ ε) :
    IsCarriedByFiniteNormGraphs T k μ := by
  cases T with
  | horizontal =>
    obtain ⟨I, H, hH⟩ := h
    exact ⟨I, fun _ => ε, H, hH⟩
  | vertical =>
    obtain ⟨J, V, hV⟩ := h
    exact ⟨J, fun _ => ε, V, hV⟩
  | mixed =>
    obtain ⟨I, J, H, V, hHV⟩ := h
    exact ⟨I, J, fun _ => ε, H, fun _ => ε, V, hHV⟩

/-! ## Energies, densities and availability -/

/-- The mixed beta is at most the horizontal one (more models in the infimum). -/
theorem betaSq_mixed_le_horizontal {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (r : ℝ) : betaSq μ k .mixed z r ≤ betaSq μ k .horizontal z r := by
  by_cases hr : 0 < r
  · rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hr]
    gcongr
    exact le_iInf fun L => iInf_le (fun L' : Models n k .mixed => fit μ L' z r) (Sum.inl L)
  · simp [betaSq, hr]

/-- The mixed beta is at most the vertical one (more models in the infimum). -/
theorem betaSq_mixed_le_vertical {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n)
    (r : ℝ) : betaSq μ k .mixed z r ≤ betaSq μ k .vertical z r := by
  by_cases hr : 0 < r
  · rw [betaSq_of_pos _ _ _ _ hr, betaSq_of_pos _ _ _ _ hr]
    gcongr
    exact le_iInf fun L => iInf_le (fun L' : Models n k .mixed => fit μ L' z r) (Sum.inr L)
  · simp [betaSq, hr]

theorem squareEnergy_mixed_le_horizontal {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (R : ℝ)
    (z : Space n) : squareEnergy μ k .mixed R z ≤ squareEnergy μ k .horizontal R z :=
  lintegral_mono fun r => betaSq_mixed_le_horizontal μ k z r

theorem squareEnergy_mixed_le_vertical {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (R : ℝ)
    (z : Space n) : squareEnergy μ k .mixed R z ≤ squareEnergy μ k .vertical R z :=
  lintegral_mono fun r => betaSq_mixed_le_vertical μ k z r

/-- The square is monotone in its endpoint. -/
theorem squareEnergy_mono_endpoint {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    {R R' : ℝ} (h : R ≤ R') (z : Space n) : squareEnergy μ k T R z ≤ squareEnergy μ k T R' z :=
  lintegral_mono_set (Ioo_subset_Ioo_right h)

/-- `Θ_* ≤ Θ^*`. -/
theorem lowerDensity_le_upperDensity {n : ℕ} (μ : Measure (Space n)) (k : ℕ) (z : Space n) :
    lowerDensity μ k z ≤ upperDensity μ k z := by
  unfold lowerDensity upperDensity
  exact liminf_le_limsup

/-- A horizontal subset graph forces availability of the horizontal family (`k ≤ n`). -/
theorem nonempty_horizontalModels_of_graph {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε)
    (hk : 1 ≤ k) : Nonempty (Models n k .horizontal) := by
  have h := Submodule.finrank_le G.direction
  rw [G.rank_eq, finrank_euclideanSpace_fin] at h
  exact HorizontalModel.nonempty_iff.mpr ⟨hk, h⟩

/-- A full vertical graph forces availability of the vertical family (`2 ≤ k ≤ n + 2`). -/
theorem nonempty_verticalModels_of_graph {n k : ℕ} {ε : ℝ}
    (G : GeneralRegularVerticalGraph n k ε) : Nonempty (Models n k .vertical) := by
  have h := Submodule.finrank_le G.direction
  rw [finrank_euclideanSpace_fin] at h
  exact VerticalModel.nonempty_iff.mpr ⟨G.vertical_dimension, by have := G.rank_eq; omega⟩

/-- Hausdorff-null exceptional sets of the square at every positive endpoint on a set `S`
give finiteness at every positive endpoint `μ`-a.e. on `S`, for `μ ≪ H_P^k`. The endpoints
`N + 1` suffice by monotonicity in the endpoint. -/
theorem ae_forall_squareEnergy_lt_top {n k : ℕ} {μ ρ : Measure (Space n)}
    (hac : μ ≪ hausdorffP n k) {S : Set (Space n)} {T : FamilyKind}
    (h : ∀ R : ℝ, 0 < R → hausdorffP n k (S ∩ {z | squareEnergy ρ k T R z = ⊤}) = 0) :
    ∀ᵐ z ∂μ, z ∈ S → ∀ R : ℝ, 0 < R → squareEnergy ρ k T R z < ⊤ := by
  have h' : ∀ N : ℕ, ∀ᵐ z ∂μ, z ∈ S → squareEnergy ρ k T ((N : ℝ) + 1) z < ⊤ := by
    intro N
    refine ae_iff.2 (measure_mono_null ?_ (hac (h ((N : ℝ) + 1) (by positivity))))
    intro z hz
    simp only [mem_ofPred_eq, not_imp, not_lt, top_le_iff] at hz
    exact hz
  filter_upwards [ae_all_iff.2 h'] with z hz hzS R hR
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact (squareEnergy_mono_endpoint ρ k T (by linarith : R ≤ (N : ℝ) + 1) z).trans_lt
    (hz N hzS)

/-- The pointwise necessity conclusion on one carrying set `S`, from densities and the
square of a dominating family `T'`. -/
theorem ae_necessity_on_set {n k : ℕ} {μ : Measure (Space n)} {S : Set (Space n)}
    {T T' : FamilyKind}
    (hd : ∀ᵐ z ∂μ, z ∈ S → 0 < lowerDensity μ k z ∧ upperDensity μ k z < ⊤)
    (hs : ∀ᵐ z ∂μ, z ∈ S → ∀ R : ℝ, 0 < R → squareEnergy μ k T' R z < ⊤)
    (hmix : ∀ (R : ℝ) (z : Space n), squareEnergy μ k .mixed R z ≤ squareEnergy μ k T' R z)
    (hT : ∀ (R : ℝ) (z : Space n), squareEnergy μ k T R z ≤ squareEnergy μ k T' R z) :
    ∀ᵐ z ∂μ, z ∈ S → (0 < lowerDensity μ k z ∧ lowerDensity μ k z ≤ upperDensity μ k z ∧
        upperDensity μ k z < ⊤) ∧
      ∀ R : ℝ, 0 < R → squareEnergy μ k .mixed R z < ⊤ ∧ squareEnergy μ k T R z < ⊤ := by
  filter_upwards [hd, hs] with z hzd hzs hzS
  obtain ⟨h1, h2⟩ := hzd hzS
  exact ⟨⟨h1, lowerDensity_le_upperDensity μ k z, h2⟩, fun R hR =>
    ⟨(hmix R z).trans_lt (hzs hzS R hR), (hT R z).trans_lt (hzs hzS R hR)⟩⟩

end ParabolicRectifiability.Characterization
