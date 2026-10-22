import ParabolicRectifiability.IntegralCanonical.Assembly.MeasureHelpers
import ParabolicRectifiability.IntegralCanonical.Assembly.DensityBridgeAndTypeSeparation
import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.Foundations.Statements.Measurability
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # The canonical decomposition and its guards

Assembly of the proof of
* `canonicalDecomposition_of_providers`, in implication form from the hypotheses
  `IntrinsicSufficiencyStatement`, `GraphSourceStatement` and
  `SquareFinitenessEndpointStatement`, together with the density bridge
  `isIntrinsicSource_of_hasPositiveFiniteUpperDensity` and the type separation
  `horizontalGraph_inter_ordinaryVerticalGraph_separation`;
* `canonicalGuards_of_providers`, from the definitions and `AmbientEnergyZeroStatement`.

The steps of the assembly are:
* Borel finite-energy sets and locally Radon restrictions;
* typed covers of `μ⌊E_T`: restriction preserves the source class and decreases the square,
  then intrinsic sufficiency applies; an unavailable family has `E_T = ∅`;
* `μ(E_H ∩ E_V) = 0`: one vertical cover at norm `1`, one horizontal cover at slope `1/2`, and
  the separation of types (`L = 1`, `ε = 1/2`, so `Lε ≤ 1/2`) on each pair;
* `μ(G \ (E_H ∪ E_V)) = 0`: one mixed cover of `μ⌊G` and full-source graph necessity (the
  graph-source statement with the original `μ`, transferred by `μ ≪ H_P^k`) on each graph;
* purity of `μ_+`, graph by graph, from `E_+ ∩ E_T = ∅`;
* the measure identity and pairwise singularity on the Borel partition
  `E_H, E_V \ E_H, X \ (E_H ∪ E_V)` without subtracting infinite masses;
* uniqueness without competitor singularity;
* endpoint independence, from endpoint independence of square finiteness.
The ambient endpoint `k = n + 2` needs no separate branch: the statements used include it.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.IntegralCanonical

open ParabolicRectifiability.Foundations ParabolicRectifiability.Characterization

variable {n : ℕ}

/-! ## Graph bookkeeping -/

/-- A horizontal graph has a spatial direction of rank `k`, which forces `k ≤ n`. -/
theorem le_of_horizontalGraph {k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε) : k ≤ n := by
  have h := Submodule.finrank_le G.direction
  rwa [G.rank_eq, finrank_euclideanSpace_fin] at h

/-- The ordinary full vertical graph underlying a full general regular vertical graph of norm
at most `ε`: its parabolic Lipschitz constant is at most `ε`, since the BMO part of the norm
is nonnegative. The image is unchanged. -/
def ordinaryVerticalGraphOfGeneral {k : ℕ} {ε : ℝ} (G : GeneralRegularVerticalGraph n k ε) :
    OrdinaryVerticalGraph n k ε where
  vertical_dimension := G.vertical_dimension
  direction := G.direction
  rank_eq := G.rank_eq
  offset := G.offset
  function := G.function
  lipschitz := by
    obtain ⟨_, L, B, hL, -, -, hLB⟩ := G.regular
    exact ⟨L, hL, by linarith [B.coe_nonneg]⟩

theorem ordinaryVerticalGraphOfGeneral_image {k : ℕ} {ε : ℝ}
    (G : GeneralRegularVerticalGraph n k ε) :
    (ordinaryVerticalGraphOfGeneral G).image = G.image := rfl

/-- The zero measure has typed covers at every tolerance (by the empty family). -/
theorem hasTypedMeasureCover_zero (T : FamilyKind) (k : ℕ) (ε : ℝ) :
    HasTypedMeasureCover T k (0 : Measure (Space n)) ε := by
  cases T with
  | horizontal => exact ⟨∅, fun i => (show False from i.2).elim, by simp⟩
  | vertical => exact ⟨∅, fun i => (show False from i.2).elim, by simp⟩
  | mixed =>
    exact ⟨∅, ∅, fun i => (show False from i.2).elim, fun i => (show False from i.2).elim,
      by simp⟩

/-- A typed cover at one tolerance is a carrier by typed graphs of finite norm. -/
theorem isCarriedByFiniteNormGraphs_of_hasTypedMeasureCover {T : FamilyKind} {k : ℕ}
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
    obtain ⟨I, J, H, V, hC⟩ := h
    exact ⟨I, J, fun _ => ε, H, fun _ => ε, V, hC⟩

/-! ## Full-source graph necessity, transferred to the source -/

/-- Graph-source with the original `μ`, transferred by `μ ≪ H_P^k`: each horizontal
graph meets `X \ E_H` in a `μ`-null set. -/
theorem measure_horizontalGraph_inter_compl_eq_zero (hGS : GraphSourceStatement)
    (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) (hac : μ ≪ hausdorffP n k)
    {R : ℝ} (hR : 0 < R) {ε : ℝ} (G : HorizontalGraph n k ε) :
    μ (G.image ∩ (finiteEnergySet μ k .horizontal R)ᶜ) = 0 := by
  rw [compl_finiteEnergySet]
  exact hac ((hGS n hn k hk hkn).1 ε G μ hμ hreg R hR)

/-- Graph-source with the original `μ`, transferred by `μ ≪ H_P^k`: each full general
regular vertical graph meets `X \ E_V` in a `μ`-null set. -/
theorem measure_verticalGraph_inter_compl_eq_zero (hGS : GraphSourceStatement)
    (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) (hac : μ ≪ hausdorffP n k)
    {R : ℝ} (hR : 0 < R) {ε : ℝ} (G : GeneralRegularVerticalGraph n k ε) :
    μ (G.image ∩ (finiteEnergySet μ k .vertical R)ᶜ) = 0 := by
  rw [compl_finiteEnergySet]
  exact hac ((hGS n hn k hk hkn).2 ε G μ hμ hreg R hR)

/-! ## Typed restrictions -/

/-- `μ⌊E_T` has a type-`T` cover at every positive tolerance. Restriction
keeps the source class and decreases the square, so intrinsic sufficiency applies
with the energy finite at every point of `E_T`; an unavailable family has `E_T = ∅`. -/
theorem hasTypedMeasureCover_restrict_finiteEnergySet (hIS : IntrinsicSufficiencyStatement)
    (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) (hsrc : IsIntrinsicSource k μ)
    (T : FamilyKind) {R : ℝ} (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover T k (μ.restrict (finiteEnergySet μ k T R)) ε := by
  have := hμ
  by_cases hT : Nonempty (Models n k T)
  · have hE := measurableSet_finiteEnergySet μ k T R
    obtain ⟨hfin', hreg'⟩ := restrict_locallyRadon hμ hreg (finiteEnergySet μ k T R)
    obtain ⟨hac', hcar'⟩ := isIntrinsicSource_restrict hsrc (finiteEnergySet μ k T R)
    refine hIS n hn k hk hkn T hT _ hfin' hreg' hac' hcar' ⟨R, hR, ?_⟩
    filter_upwards [ae_restrict_mem hE] with z hz
    exact (squareEnergy_restrict_le μ _ k T R z).trans_lt
      (show squareEnergy μ k T R z < ⊤ from hz)
  · have : IsEmpty (Models n k T) := not_nonempty_iff.mp hT
    rw [finiteEnergySet_eq_empty_of_isEmpty μ hR, Measure.restrict_empty]
    exact fun ε _ => hasTypedMeasureCover_zero T k ε

/-! ## Null overlap, exhaustion and purity -/

/-- `μ(E_H ∩ E_V) = 0`. -/
theorem measure_inter_finiteEnergySet_eq_zero (hIS : IntrinsicSufficiencyStatement)
    (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) (hsrc : IsIntrinsicSource k μ)
    {R : ℝ} (hR : 0 < R) :
    μ (finiteEnergySet μ k .horizontal R ∩ finiteEnergySet μ k .vertical R) = 0 := by
  have := hμ
  have hEH := measurableSet_finiteEnergySet μ k .horizontal R
  have hEV := measurableSet_finiteEnergySet μ k .vertical R
  obtain ⟨I, H, hH⟩ := hasTypedMeasureCover_restrict_finiteEnergySet hIS hn hk hkn hμ hreg hsrc
    .horizontal hR (1 / 2) (by norm_num)
  obtain ⟨J, V, hV⟩ := hasTypedMeasureCover_restrict_finiteEnergySet hIS hn hk hkn hμ hreg hsrc
    .vertical hR 1 one_pos
  rw [Measure.restrict_apply' hEH] at hH
  rw [Measure.restrict_apply' hEV] at hV
  refine measure_eq_zero_of_cover (fun j => (V j).image) ?_ fun j => ?_
  · refine measure_mono_null ?_ hV
    rintro z ⟨⟨-, hzV⟩, hz⟩
    exact ⟨hz, hzV⟩
  · refine measure_eq_zero_of_cover (fun i => (H i).image) ?_ fun i => ?_
    · refine measure_mono_null ?_ hH
      rintro z ⟨⟨-, hzH, -⟩, hz⟩
      exact ⟨hz, hzH⟩
    · refine measure_mono_null (t := (H i).image ∩ (V j).image)
        (fun z hz => ⟨hz.1, hz.2.1⟩) ?_
      apply hsrc.1
      have h2 : 2 ≤ k := (V j).vertical_dimension
      have hkn' : k ≤ n := le_of_horizontalGraph (H i)
      exact (horizontalGraph_inter_ordinaryVerticalGraph_separation n k h2 hkn' 1
        (ordinaryVerticalGraphOfGeneral (V j)) (1 / 2) (H i) (by norm_num)
        (by norm_num)).2.2.1

/-- `μ(G \ (E_H ∪ E_V)) = 0`. The cover comes from mixed
sufficiency for `μ⌊G`; its points acquire a type from full-source graph necessity with the
original `μ`. No inference from the integral of a minimum to a fixed-family integral. -/
theorem measure_mixed_diff_finiteEnergySet_eq_zero (hIS : IntrinsicSufficiencyStatement)
    (hGS : GraphSourceStatement) (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hsrc : IsIntrinsicSource k μ) {R : ℝ} (hR : 0 < R) :
    μ (finiteEnergySet μ k .mixed R \
      (finiteEnergySet μ k .horizontal R ∪ finiteEnergySet μ k .vertical R)) = 0 := by
  have := hμ
  have hG := measurableSet_finiteEnergySet μ k .mixed R
  obtain ⟨I, J, H, V, hC⟩ := hasTypedMeasureCover_restrict_finiteEnergySet hIS hn hk hkn hμ
    hreg hsrc .mixed hR 1 one_pos
  rw [Measure.restrict_apply' hG] at hC
  refine measure_eq_zero_of_cover₂ (fun i => (H i).image) (fun j => (V j).image) ?_
    (fun i => ?_) (fun j => ?_)
  · refine measure_mono_null ?_ hC
    rintro z ⟨⟨hzG, -⟩, hz⟩
    exact ⟨hz, hzG⟩
  · refine measure_mono_null ?_
      (measure_horizontalGraph_inter_compl_eq_zero hGS hn hk hkn hμ hreg hsrc.1 hR (H i))
    rintro z ⟨hzH, -, hz⟩
    exact ⟨hzH, fun h => hz (Or.inl h)⟩
  · refine measure_mono_null ?_
      (measure_verticalGraph_inter_compl_eq_zero hGS hn hk hkn hμ hreg hsrc.1 hR (V j))
    rintro z ⟨hzV, -, hz⟩
    exact ⟨hzV, fun h => hz (Or.inr h)⟩

/-- `E_T ∩ E_+ = ∅`, since `E_T ⊆ G`. -/
theorem finiteEnergySet_inter_pureSet (μ : Measure (Space n)) (k : ℕ) (T : FamilyKind)
    (R : ℝ) : finiteEnergySet μ k T R ∩ pureSet μ k R = ∅ :=
  subset_empty_iff.1 fun _ hz => hz.2 (finiteEnergySet_subset_mixed μ k T R hz.1)

/-- `μ_+` is graph-pure, graph by graph; no common
exceptional set for all graphs is chosen. -/
theorem isGraphPure_purePart (hGS : GraphSourceStatement) (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) (hac : μ ≪ hausdorffP n k) {R : ℝ} (hR : 0 < R) :
    IsGraphPure k (purePart μ k R) := by
  have := hμ
  have hP : MeasurableSet (pureSet μ k R) := (measurableSet_finiteEnergySet μ k .mixed R).compl
  refine ⟨fun ε Γ => ?_, fun ε Γ => ?_⟩
  · rw [purePart, Measure.restrict_apply' hP]
    refine measure_mono_null (inter_subset_inter_right _ ?_)
      (measure_horizontalGraph_inter_compl_eq_zero hGS hn hk hkn hμ hreg hac hR Γ)
    exact compl_subset_compl.2 (finiteEnergySet_subset_mixed μ k .horizontal R)
  · rw [purePart, Measure.restrict_apply' hP]
    refine measure_mono_null (inter_subset_inter_right _ ?_)
      (measure_verticalGraph_inter_compl_eq_zero hGS hn hk hkn hμ hreg hac hR Γ)
    exact compl_subset_compl.2 (finiteEnergySet_subset_mixed μ k .vertical R)

/-! ## The measure partition -/

/-- `μ_V = μ⌊(E_V \ E_H)`, because the overlap is null. -/
theorem verticalPart_eq_restrict_diff {k : ℕ} {μ : Measure (Space n)} {R : ℝ}
    (hover : μ (finiteEnergySet μ k .horizontal R ∩ finiteEnergySet μ k .vertical R) = 0) :
    verticalPart μ k R =
      μ.restrict (finiteEnergySet μ k .vertical R \ finiteEnergySet μ k .horizontal R) := by
  unfold verticalPart
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨measure_mono_null ?_ hover, measure_mono_null ?_ measure_empty⟩
  · rintro z ⟨hzV, hz⟩
    exact ⟨not_not.1 fun h => hz ⟨hzV, h⟩, hzV⟩
  · rintro z ⟨⟨hzV, -⟩, hz⟩
    exact hz hzV

/-- `μ_+ = μ⌊(X \ (E_H ∪ E_V))`, because `G \ (E_H ∪ E_V)` is null and `E_H ∪ E_V ⊆ G`. -/
theorem purePart_eq_restrict_compl {k : ℕ} {μ : Measure (Space n)} {R : ℝ}
    (hexh : μ (finiteEnergySet μ k .mixed R \
      (finiteEnergySet μ k .horizontal R ∪ finiteEnergySet μ k .vertical R)) = 0) :
    purePart μ k R =
      μ.restrict (finiteEnergySet μ k .horizontal R ∪ finiteEnergySet μ k .vertical R)ᶜ := by
  unfold purePart
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨measure_mono_null ?_ measure_empty, measure_mono_null ?_ hexh⟩
  · rintro z ⟨hzP, hz⟩
    rcases not_not.1 hz with h | h
    · exact hzP (finiteEnergySet_subset_mixed μ k .horizontal R h)
    · exact hzP (finiteEnergySet_subset_mixed μ k .vertical R h)
  · rintro z ⟨hz, hzP⟩
    exact ⟨not_not.1 hzP, hz⟩

/-- The measure identity `μ = μ_H + μ_V + μ_+`, by countable additivity on the disjoint
Borel partition `E_H, E_V \ E_H, X \ (E_H ∪ E_V)`; no infinite mass is subtracted. -/
theorem measure_eq_canonical_sum {k : ℕ} {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) {R : ℝ}
    (hover : μ (finiteEnergySet μ k .horizontal R ∩ finiteEnergySet μ k .vertical R) = 0)
    (hexh : μ (finiteEnergySet μ k .mixed R \
      (finiteEnergySet μ k .horizontal R ∪ finiteEnergySet μ k .vertical R)) = 0) :
    μ = horizontalPart μ k R + verticalPart μ k R + purePart μ k R := by
  have := hμ
  have hEH := measurableSet_finiteEnergySet μ k .horizontal R
  have hEV := measurableSet_finiteEnergySet μ k .vertical R
  rw [verticalPart_eq_restrict_diff hover, purePart_eq_restrict_compl hexh, horizontalPart,
    ← Measure.restrict_union disjoint_sdiff_right (hEV.diff hEH), union_sdiff_self,
    ← Measure.restrict_union disjoint_compl_right (hEH.union hEV).compl, union_compl_self,
    Measure.restrict_univ]

/-! ## Uniqueness -/

/-- Uniqueness of the canonical decomposition, without a singularity
assumption on the competitor. Each competing summand is dominated by `μ`; full-source graph
necessity with the original `μ` puts `ρ_T` on `E_T`; purity makes `ρ_P` vanish on the typed
covers of `μ_H`, `μ_V`, hence on `E_H`, `E_V`; the identities are then restricted to the three
partition sets, with no cancellation. -/
theorem canonical_unique_of_providers (hIS : IntrinsicSufficiencyStatement)
    (hGS : GraphSourceStatement) (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    {μ : Measure (Space n)} (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (hsrc : IsIntrinsicSource k μ) {R : ℝ} (hR : 0 < R)
    (hover : μ (finiteEnergySet μ k .horizontal R ∩ finiteEnergySet μ k .vertical R) = 0)
    (hexh : μ (finiteEnergySet μ k .mixed R \
      (finiteEnergySet μ k .horizontal R ∪ finiteEnergySet μ k .vertical R)) = 0)
    (ρH ρV ρP : Measure (Space n)) (hsum : μ = ρH + ρV + ρP)
    (hH : IsRegularlyRectifiableMeasure .horizontal k ρH)
    (hV : IsRegularlyRectifiableMeasure .vertical k ρV) (hP : IsGraphPure k ρP) :
    ρH = horizontalPart μ k R ∧ ρV = verticalPart μ k R ∧ ρP = purePart μ k R := by
  have := hμ
  have hEH := measurableSet_finiteEnergySet μ k .horizontal R
  have hEV := measurableSet_finiteEnergySet μ k .vertical R
  have hμs : ∀ s, μ s = ρH s + ρV s + ρP s := fun s => by
    rw [hsum, Measure.add_apply, Measure.add_apply]
  have hleH : ∀ s, ρH s ≤ μ s := fun s => by
    rw [hμs]
    exact le_add_right (le_add_right le_rfl)
  have hleV : ∀ s, ρV s ≤ μ s := fun s => by
    rw [hμs]
    exact le_add_right (le_add_left le_rfl)
  have hleP : ∀ s, ρP s ≤ μ s := fun s => by
    rw [hμs]
    exact le_add_left le_rfl
  have hnull : ∀ ρ : Measure (Space n), (∀ s, ρ s ≤ μ s) → ∀ s, μ s = 0 → ρ s = 0 :=
    fun ρ hle s hs => nonpos_iff_eq_zero.1 ((hle s).trans hs.le)
  -- the rectifiable competitors live on the finite-energy sets of their type
  have hcH : ρH (finiteEnergySet μ k .horizontal R)ᶜ = 0 := by
    obtain ⟨-, I, εI, H, hHc⟩ := hH
    refine measure_eq_zero_of_cover (fun i => (H i).image)
      (measure_mono_null inter_subset_right hHc) fun i => hnull ρH hleH _ ?_
    exact measure_horizontalGraph_inter_compl_eq_zero hGS hn hk hkn hμ hreg hsrc.1 hR (H i)
  have hcV : ρV (finiteEnergySet μ k .vertical R)ᶜ = 0 := by
    obtain ⟨-, J, εJ, V, hVc⟩ := hV
    refine measure_eq_zero_of_cover (fun j => (V j).image)
      (measure_mono_null inter_subset_right hVc) fun j => hnull ρV hleV _ ?_
    exact measure_verticalGraph_inter_compl_eq_zero hGS hn hk hkn hμ hreg hsrc.1 hR (V j)
  -- the graph-pure competitor vanishes on the finite-energy sets
  have hPH : ρP (finiteEnergySet μ k .horizontal R) = 0 := by
    obtain ⟨I, H, hHc⟩ := hasTypedMeasureCover_restrict_finiteEnergySet hIS hn hk hkn hμ hreg
      hsrc .horizontal hR 1 one_pos
    rw [Measure.restrict_apply' hEH, inter_comm] at hHc
    exact measure_eq_zero_of_cover (fun i => (H i).image) (hnull ρP hleP _ hHc) fun i =>
      measure_mono_null inter_subset_left (hP.1 _ (H i))
  have hPV : ρP (finiteEnergySet μ k .vertical R) = 0 := by
    obtain ⟨J, V, hVc⟩ := hasTypedMeasureCover_restrict_finiteEnergySet hIS hn hk hkn hμ hreg
      hsrc .vertical hR 1 one_pos
    rw [Measure.restrict_apply' hEV, inter_comm] at hVc
    exact measure_eq_zero_of_cover (fun j => (V j).image) (hnull ρP hleP _ hVc) fun j =>
      measure_mono_null inter_subset_left (hP.2 _ (V j))
  refine ⟨?_, ?_, ?_⟩
  · ext A hA
    have hV0 : ρV (A ∩ finiteEnergySet μ k .horizontal R) = 0 := by
      refine measure_mono_null (fun z hz => ?_)
        (measure_union_null (hnull ρV hleV _ hover) hcV)
      by_cases h : z ∈ finiteEnergySet μ k .vertical R
      · exact Or.inl ⟨hz.2, h⟩
      · exact Or.inr h
    have hP0 : ρP (A ∩ finiteEnergySet μ k .horizontal R) = 0 :=
      measure_mono_null inter_subset_right hPH
    rw [horizontalPart, Measure.restrict_apply hA, hμs, measure_inter_conull hcH, hV0, hP0,
      add_zero, add_zero]
  · ext A hA
    have hH0 : ρH (A ∩ finiteEnergySet μ k .vertical R) = 0 := by
      refine measure_mono_null (fun z hz => ?_)
        (measure_union_null (hnull ρH hleH _ hover) hcH)
      by_cases h : z ∈ finiteEnergySet μ k .horizontal R
      · exact Or.inl ⟨h, hz.2⟩
      · exact Or.inr h
    have hP0 : ρP (A ∩ finiteEnergySet μ k .vertical R) = 0 :=
      measure_mono_null inter_subset_right hPV
    rw [verticalPart, Measure.restrict_apply hA, hμs, measure_inter_conull hcV, hH0, hP0,
      zero_add, add_zero]
  · ext A hA
    have hH0 : ρH (A ∩ (finiteEnergySet μ k .horizontal R ∪
        finiteEnergySet μ k .vertical R)ᶜ) = 0 :=
      measure_mono_null (fun _ hz h => hz.2 (Or.inl h)) hcH
    have hV0 : ρV (A ∩ (finiteEnergySet μ k .horizontal R ∪
        finiteEnergySet μ k .vertical R)ᶜ) = 0 :=
      measure_mono_null (fun _ hz h => hz.2 (Or.inr h)) hcV
    have hPc : ρP (finiteEnergySet μ k .horizontal R ∪
        finiteEnergySet μ k .vertical R)ᶜᶜ = 0 := by
      rw [compl_compl]
      exact measure_union_null hPH hPV
    rw [purePart_eq_restrict_compl hexh, Measure.restrict_apply hA, hμs, hH0, hV0, zero_add,
      zero_add, measure_inter_conull hPc]

/-! ## The canonical decomposition -/

/-- The conclusions of the canonical decomposition theorem for an intrinsic source, at one
endpoint `R > 0`, from intrinsic sufficiency, graph-source, endpoint independence of square
finiteness, and the separation of types. -/
theorem isCanonicalDecomposition_of_providers (hIS : IntrinsicSufficiencyStatement)
    (hGS : GraphSourceStatement) (hEnd : SquareFinitenessEndpointStatement) (hn : 1 ≤ n)
    {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2) {μ : Measure (Space n)}
    (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular) (hsrc : IsIntrinsicSource k μ)
    {R : ℝ} (hR : 0 < R) : IsCanonicalDecomposition k μ R := by
  have := hμ
  have hEH := measurableSet_finiteEnergySet μ k .horizontal R
  have hEV := measurableSet_finiteEnergySet μ k .vertical R
  have hG := measurableSet_finiteEnergySet μ k .mixed R
  have hP : MeasurableSet (pureSet μ k R) := hG.compl
  have hover := measure_inter_finiteEnergySet_eq_zero hIS hn hk hkn hμ hreg hsrc hR
  have hexh := measure_mixed_diff_finiteEnergySet_eq_zero hIS hGS hn hk hkn hμ hreg hsrc hR
  have hpure := isGraphPure_purePart hGS hn hk hkn hμ hreg hsrc.1 hR
  have hcovH := hasTypedMeasureCover_restrict_finiteEnergySet hIS hn hk hkn hμ hreg hsrc
    .horizontal hR
  have hcovV := hasTypedMeasureCover_restrict_finiteEnergySet hIS hn hk hkn hμ hreg hsrc
    .vertical hR
  have hacR : ∀ A : Set (Space n), μ.restrict A ≪ hausdorffP n k := fun _ =>
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hsrc.1
  exact
    { measurable_horizontal := hEH
      measurable_vertical := hEV
      measurable_pure := hP
      overlap_null := hover
      exhaustion_null := hexh
      horizontal_locallyRadon := restrict_locallyRadon hμ hreg _
      vertical_locallyRadon := restrict_locallyRadon hμ hreg _
      pure_locallyRadon := restrict_locallyRadon hμ hreg _
      measure_eq := measure_eq_canonical_sum hμ hover hexh
      singular_horizontal_vertical :=
        ⟨(finiteEnergySet μ k .horizontal R)ᶜ, hEH.compl,
          by rw [horizontalPart, Measure.restrict_apply' hEH, compl_inter_self, measure_empty],
          by rw [verticalPart, Measure.restrict_apply' hEV, compl_compl]; exact hover⟩
      singular_horizontal_pure :=
        ⟨(finiteEnergySet μ k .horizontal R)ᶜ, hEH.compl,
          by rw [horizontalPart, Measure.restrict_apply' hEH, compl_inter_self, measure_empty],
          by rw [purePart, Measure.restrict_apply' hP, compl_compl,
            finiteEnergySet_inter_pureSet, measure_empty]⟩
      singular_vertical_pure :=
        ⟨(finiteEnergySet μ k .vertical R)ᶜ, hEV.compl,
          by rw [verticalPart, Measure.restrict_apply' hEV, compl_inter_self, measure_empty],
          by rw [purePart, Measure.restrict_apply' hP, compl_compl,
            finiteEnergySet_inter_pureSet, measure_empty]⟩
      horizontal_rectifiable :=
        ⟨hacR _, isCarriedByFiniteNormGraphs_of_hasTypedMeasureCover (hcovH 1 one_pos)⟩
      vertical_rectifiable :=
        ⟨hacR _, isCarriedByFiniteNormGraphs_of_hasTypedMeasureCover (hcovV 1 one_pos)⟩
      horizontal_covers := hcovH
      vertical_covers := hcovV
      pure_graphPure := hpure
      pure_null_union := fun _ _ _ H _ V =>
        measure_union_null (measure_iUnion_null fun i => hpure.1 _ (H i))
          (measure_iUnion_null fun j => hpure.2 _ (V j))
      unique := fun ρH ρV ρP hsum hH hV hP =>
        canonical_unique_of_providers hIS hGS hn hk hkn hμ hreg hsrc hR hover hexh ρH ρV ρP
          hsum hH hV hP
      endpoint_independent := fun R' hR' => by
        have hset : ∀ T : FamilyKind, finiteEnergySet μ k T R' = finiteEnergySet μ k T R := by
          intro T
          ext z
          exact hEnd n hn k hk hkn T μ hμ hreg z R' R hR' hR
        refine ⟨?_, ?_, ?_⟩ <;> simp only [horizontalPart, verticalPart, purePart, pureSet, hset] }

/-- **The canonical decomposition theorem**, in implication form. Assumes
`IntrinsicSufficiencyStatement`, `GraphSourceStatement` and
`SquareFinitenessEndpointStatement`, and uses
`isIntrinsicSource_of_hasPositiveFiniteUpperDensity` (the density form of the hypothesis) and
`horizontalGraph_inter_ordinaryVerticalGraph_separation` (null overlap). -/
theorem canonicalDecomposition_of_providers (hIS : IntrinsicSufficiencyStatement)
    (hGS : GraphSourceStatement) (hEnd : SquareFinitenessEndpointStatement) :
    CanonicalDecompositionStatement := by
  intro n hn k hk hkn μ hμ hreg hsrc R hR
  have hsrc' : IsIntrinsicSource k μ :=
    hsrc.elim id (isIntrinsicSource_of_hasPositiveFiniteUpperDensity n hn k hk hkn μ hμ hreg)
  exact isCanonicalDecomposition_of_providers hIS hGS hEnd hn hk hkn hμ hreg hsrc' hR

/-- **The canonical guards**, in implication form, from the definitions and
`AmbientEnergyZeroStatement`: unavailable families have empty finite-energy sets
(`betaSq_of_isEmpty` and the availability lemmas); at
`k = n + 2` the vertical and mixed squares vanish, so `E_V = G = X`, `E_H = E_+ = ∅`; for
`μ = 0` both available squares vanish, so `E_H ∩ E_V = X`. The source-class premise of the
ambient clause is not needed. -/
theorem canonicalGuards_of_providers (hAmb : AmbientEnergyZeroStatement) :
    CanonicalGuardsStatement := by
  intro n hn k hk _ μ hμ hreg R hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    have : IsEmpty (Models n 1 .vertical) := VerticalModel.one_isEmpty
    exact finiteEnergySet_eq_empty_of_isEmpty μ hR
  · rintro rfl
    have : IsEmpty (Models n (n + 1) .horizontal) :=
      HorizontalModel.isEmpty_of_not_available (by omega)
    exact finiteEnergySet_eq_empty_of_isEmpty μ hR
  · rintro rfl -
    have : IsEmpty (Models n (n + 2) .horizontal) := HorizontalModel.ambient_isEmpty
    have hfull : ∀ T : FamilyKind, Nonempty (Models n (n + 2) T) →
        finiteEnergySet μ (n + 2) T R = univ := by
      intro T hT
      ext z
      simp only [mem_univ, iff_true]
      show squareEnergy μ (n + 2) T R z < ⊤
      rw [(hAmb n hn μ hμ hreg T hT).2 R hR z]
      exact ENNReal.zero_lt_top
    refine ⟨?_, ?_, ?_⟩
    · rw [horizontalPart, finiteEnergySet_eq_empty_of_isEmpty μ hR, Measure.restrict_empty]
    · rw [verticalPart, hfull .vertical (VerticalModel.nonempty_iff.mpr ⟨by omega, le_rfl⟩),
        Measure.restrict_univ]
    · rw [purePart, pureSet,
        hfull .mixed (AdmissibleModel.nonempty_of_range hn (by omega) le_rfl), compl_univ,
        Measure.restrict_empty]
  · rintro rfl
    refine ⟨by simp, fun h2 hkn' => ?_⟩
    have : Nonempty (Models n k .horizontal) := HorizontalModel.nonempty_iff.mpr ⟨hk, hkn'⟩
    have : Nonempty (Models n k .vertical) := VerticalModel.nonempty_iff.mpr ⟨h2, by omega⟩
    rw [finiteEnergySet_zero_measure, finiteEnergySet_zero_measure, inter_self]

end ParabolicRectifiability.IntegralCanonical
