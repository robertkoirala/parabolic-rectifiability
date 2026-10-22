import ParabolicRectifiability.Characterization.Assembly.IntermediateResults
import ParabolicRectifiability.Characterization.Assembly.CoveringLemmas

/-! # The branches of the characterization theorem

This file proves the four branch statements of the characterization of parabolic
rectifiability from the intermediate results of the characterization proof
(`finite_hausdorff_criterion`, `graph_source_square_finite`,
`exists_dominated_hausdorff_pieces`, `graph_borel_envelope`, `graph_density_bounds`), from
the basic energy facts `squareEnergy_mono_measure`, `squareEnergy_smul`,
`squareEnergy_restrict_le`, `hausdorffP_restrict_isFinite`, and from elementary covering
lemmas.

* `intrinsic_sufficiency_skeleton`: intrinsic sufficiency (finite-Hausdorff criterion and
  Radon–Nikodym exhaustion);
* `necessity_skeleton`: necessity (graph-source squares, graph envelopes, graph densities);
* `typed_refinement_set_skeleton`: typed refinement, set version;
* `typed_refinement_measure_skeleton`: typed refinement, measure version.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/-! ## Intrinsic sufficiency -/

/-- **Intrinsic sufficiency.** The Radon–Nikodym pieces `F` of
`exists_dominated_hausdorff_pieces` satisfy `η_F = H_P^k⌊F ≤ c μ`, hence
`S^R_{η_F,T} ≤ c S^R_{μ,T}` (`squareEnergy_mono_measure`, `squareEnergy_smul`), and
the `μ`-null exceptional set is `η_F`-null. The finite-Hausdorff criterion
(`finite_hausdorff_criterion`) covers each piece at the prescribed tolerance; absolute
continuity and the countable union give the measure cover. The case `k = n + 2` is included
in the finite-Hausdorff criterion. -/
theorem intrinsic_sufficiency_skeleton : IntrinsicSufficiencyStatement := by
  intro n hn k hk hkn T hT μ hμ hreg hac hcar hR ε hε
  obtain ⟨R, hRpos, hRae⟩ := hR
  obtain ⟨F, hFm, hFfin, hFdom, hFcar⟩ :=
    exists_dominated_hausdorff_pieces n k μ hμ hreg hac hcar
  have hset : ∀ m, IsRegularlyRectifiableSet T k (F m) := by
    intro m
    obtain ⟨c, -, hle⟩ := hFdom m
    refine (And.left finite_hausdorff_criterion) n hn k hk hkn T hT (F m) (hFm m) (hFfin m)
      ⟨R, hRpos, ?_⟩
    filter_upwards [(Measure.absolutelyContinuous_of_le_smul hle).ae_le hRae] with z hz
    calc squareEnergy ((hausdorffP n k).restrict (F m)) k T R z
        ≤ squareEnergy (ENNReal.ofReal c • μ) k T R z := squareEnergy_mono_measure hle k T R z
      _ = ENNReal.ofReal c * squareEnergy μ k T R z :=
          @squareEnergy_smul n μ (ENNReal.ofReal c) ENNReal.ofReal_ne_top k T hT R z
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hz
  exact hasTypedMeasureCover_of_setCovers hac F hFcar fun m => hset m ε hε

/-! ## Necessity -/

/-- **Necessity.** Fix the countable typed carrier of the finite-norm definition.
* Carrier: each carrying graph lies in a Borel envelope of locally finite `H_P^k` measure
  (`graph_borel_envelope`); the countably many bounded pieces form a Borel sigma-finite
  carrier.
* Densities: relative ADR differentiation on each graph (`graph_density_bounds`) gives
  `0 < Θ_*` and `Θ^* < ∞` at source-typical points; `Θ_* ≤ Θ^*` always.
* Squares: graph-source (`graph_source_square_finite`) on each graph with the same original
  source, its Hausdorff-null exceptions made `μ`-null by `μ ≪ H_P^k`, and the endpoints
  `N + 1` with monotonicity in the endpoint give every positive endpoint; the mixed square is
  at most each fixed-type square.
Countability of the carrier gives the global statement. -/
theorem necessity_skeleton : NecessityStatement := by
  intro n hn k hk hkn T hT μ hμ hreg hrect
  obtain ⟨hac, hcar⟩ := hrect
  obtain ⟨envH, envV⟩ := graph_borel_envelope n k
  obtain ⟨densH, densV⟩ := graph_density_bounds n hn k hk hkn μ hμ hreg hac
  obtain ⟨srcH, srcV⟩ := graph_source_square_finite n hn k hk hkn
  have sqH : ∀ (ε : ℝ) (G : HorizontalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
      ∀ R : ℝ, 0 < R → squareEnergy μ k .horizontal R z < ⊤ := fun ε G =>
    ae_forall_squareEnergy_lt_top hac fun R hR => srcH ε G μ hμ hreg R hR
  have sqV : ∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε), ∀ᵐ z ∂μ, z ∈ G.image →
      ∀ R : ℝ, 0 < R → squareEnergy μ k .vertical R z < ⊤ := fun ε G =>
    ae_forall_squareEnergy_lt_top hac fun R hR => srcV ε G μ hμ hreg R hR
  cases T with
  | horizontal =>
    obtain ⟨I, ε, H, hH⟩ := hcar
    choose H' hHsub hHmeas hHfin using fun i => envH (ε i) (H i)
    exact ⟨hasBorelSigmaFiniteHausdorffCarrier_of_cover (fun i => (H i).image) hH
        (fun i => (H' i).image) hHsub hHmeas hHfin,
      ae_of_cover (fun i => (H i).image) hH fun i =>
        ae_necessity_on_set (densH _ (H i)) (sqH _ (H i))
          (squareEnergy_mixed_le_horizontal μ k) (fun _ _ => le_rfl)⟩
  | vertical =>
    obtain ⟨J, ε, V, hV⟩ := hcar
    exact ⟨hasBorelSigmaFiniteHausdorffCarrier_of_cover (fun j => (V j).image) hV
        (fun j => (V j).image) (fun _ => subset_rfl) (fun j => (envV _ (V j)).1)
        (fun j => (envV _ (V j)).2),
      ae_of_cover (fun j => (V j).image) hV fun j =>
        ae_necessity_on_set (densV _ (V j)) (sqV _ (V j))
          (squareEnergy_mixed_le_vertical μ k) (fun _ _ => le_rfl)⟩
  | mixed =>
    obtain ⟨I, J, εH, H, εV, V, hHV⟩ := hcar
    choose H' hHsub hHmeas hHfin using fun i => envH (εH i) (H i)
    have hS : μ (⋃ x, Sum.elim (fun i => (H i).image) (fun j => (V j).image) x)ᶜ = 0 := by
      rw [iUnion_sum]
      exact hHV
    refine ⟨hasBorelSigmaFiniteHausdorffCarrier_of_cover _ hS
        (Sum.elim (fun i => (H' i).image) (fun j => (V j).image)) ?_ ?_ ?_,
      ae_of_cover _ hS ?_⟩
    · rintro (i | j)
      · exact hHsub i
      · exact subset_rfl
    · rintro (i | j)
      · exact hHmeas i
      · exact (envV _ (V j)).1
    · rintro (i | j)
      · exact hHfin i
      · exact (envV _ (V j)).2
    · rintro (i | j)
      · exact ae_necessity_on_set (densH _ (H i)) (sqH _ (H i))
          (squareEnergy_mixed_le_horizontal μ k) (squareEnergy_mixed_le_horizontal μ k)
      · exact ae_necessity_on_set (densV _ (V j)) (sqV _ (V j))
          (squareEnergy_mixed_le_vertical μ k) (squareEnergy_mixed_le_vertical μ k)

/-! ## Typed refinement -/

/-- First-type assignment for a Borel set, given Borel type envelopes `BH`, `BV`.
`E_H = E ∩ BH`, `E_V = (E \ E_H) ∩ BV` are chosen once; each available type is covered at
every tolerance by the fixed-family finite-Hausdorff criterion, applied to `H_P^k⌊E_T ≤ η`
with the full-source square (`squareEnergy_mono_measure`). -/
theorem typedRefinementSet_of_assignment {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {E : Set (Space n)} (hE : MeasurableSet E)
    (hEfin : hausdorffP n k E < ⊤) (BH BV : Set (Space n)) (hBH : MeasurableSet BH)
    (hBV : MeasurableSet BV) (hcovE : hausdorffP n k (E \ (BH ∪ BV)) = 0)
    (sqH : ∀ᵐ z ∂(hausdorffP n k).restrict E, z ∈ BH →
      squareEnergy ((hausdorffP n k).restrict E) k .horizontal 1 z < ⊤)
    (sqV : ∀ᵐ z ∂(hausdorffP n k).restrict E, z ∈ BV →
      squareEnergy ((hausdorffP n k).restrict E) k .vertical 1 z < ⊤)
    (unH : ¬ Nonempty (Models n k .horizontal) → BH = ∅)
    (unV : ¬ Nonempty (Models n k .vertical) → BV = ∅) :
    ∃ EH EV : Set (Space n), MeasurableSet EH ∧ MeasurableSet EV ∧ Disjoint EH EV ∧
      EH ⊆ E ∧ EV ⊆ E ∧ hausdorffP n k (E \ (EH ∪ EV)) = 0 ∧
      (Nonempty (Models n k .horizontal) →
        ∀ᵐ z ∂(hausdorffP n k).restrict E, z ∈ EH →
          squareEnergy ((hausdorffP n k).restrict E) k .horizontal 1 z < ⊤) ∧
      (Nonempty (Models n k .vertical) →
        ∀ᵐ z ∂(hausdorffP n k).restrict E, z ∈ EV →
          squareEnergy ((hausdorffP n k).restrict E) k .vertical 1 z < ⊤) ∧
      (∀ ε : ℝ, 0 < ε →
        HasTypedGraphCover .horizontal k EH ε ∧ HasTypedGraphCover .vertical k EV ε) ∧
      (¬ Nonempty (Models n k .horizontal) → EH = ∅) ∧
      (¬ Nonempty (Models n k .vertical) → EV = ∅) := by
  have hEH : MeasurableSet (E ∩ BH) := hE.inter hBH
  have hEV : MeasurableSet ((E \ (E ∩ BH)) ∩ BV) := (hE.diff hEH).inter hBV
  have piece : ∀ (T : FamilyKind) (P : Set (Space n)), Nonempty (Models n k T) →
      MeasurableSet P → P ⊆ E →
      (∀ᵐ z ∂(hausdorffP n k).restrict E, z ∈ P →
        squareEnergy ((hausdorffP n k).restrict E) k T 1 z < ⊤) →
      IsRegularlyRectifiableSet T k P := by
    intro T P hT hP hPE hsq
    have hle : (hausdorffP n k).restrict P ≤ (hausdorffP n k).restrict E :=
      Measure.restrict_mono hPE le_rfl
    refine (And.left finite_hausdorff_criterion) n hn k hk hkn T hT P hP
      ((measure_mono hPE).trans_lt hEfin) ⟨1, one_pos, ?_⟩
    filter_upwards [(Measure.absolutelyContinuous_of_le hle).ae_le hsq, ae_restrict_mem hP]
      with z hz hzP
    exact (squareEnergy_mono_measure hle k T 1 z).trans_lt (hz hzP)
  refine ⟨E ∩ BH, (E \ (E ∩ BH)) ∩ BV, hEH, hEV, ?_, inter_subset_left,
    fun z hz => hz.1.1, ?_, fun _ => sqH.mono fun z hz hzE => hz hzE.2,
    fun _ => sqV.mono fun z hz hzE => hz hzE.2, ?_, ?_, ?_⟩
  · exact disjoint_left.2 fun z h1 h2 => h2.1.2 h1
  · refine measure_mono_null ?_ hcovE
    intro z hz
    refine ⟨hz.1, fun hzU => hz.2 ?_⟩
    rcases hzU with hzH | hzV
    · exact Or.inl ⟨hz.1, hzH⟩
    · by_cases hzBH : z ∈ BH
      · exact Or.inl ⟨hz.1, hzBH⟩
      · exact Or.inr ⟨⟨hz.1, fun h => hzBH h.2⟩, hzV⟩
  · intro ε hε
    constructor
    · by_cases hav : Nonempty (Models n k .horizontal)
      · exact piece .horizontal (E ∩ BH) hav hEH inter_subset_left
          (sqH.mono fun z hz hzE => hz hzE.2) ε hε
      · rw [unH hav, inter_empty]
        exact hasTypedGraphCover_of_null .horizontal ε measure_empty
    · by_cases hav : Nonempty (Models n k .vertical)
      · exact piece .vertical _ hav hEV (fun z hz => hz.1.1)
          (sqV.mono fun z hz hzE => hz hzE.2) ε hε
      · rw [unV hav, inter_empty]
        exact hasTypedGraphCover_of_null .vertical ε measure_empty
  · intro hav
    rw [unH hav, inter_empty]
  · intro hav
    rw [unV hav, inter_empty]

/-- **Typed refinement, set version.** The finite-Hausdorff criterion at tolerance one (mixed) gives
one typed cover; its horizontal graphs are replaced by their Borel closure extensions
(`graph_borel_envelope`); every point is assigned to its first type; graph-source with the
full source `η = H_P^k⌊E` gives the fixed-type squares on each piece; the fixed-family
finite-Hausdorff criterion then covers each piece at every tolerance. A type without graphs
(an unavailable type) gets the empty piece. -/
theorem typed_refinement_set_skeleton : TypedRefinementSetStatement := by
  intro n hn k hk hkn E hE hEfin hae
  have hηfin : IsFiniteMeasure ((hausdorffP n k).restrict E) := hausdorffP_restrict_isFinite hEfin
  have hηc : IsFiniteMeasureOnCompacts ((hausdorffP n k).restrict E) := inferInstance
  have hηr : ((hausdorffP n k).restrict E).InnerRegular := inferInstance
  have hηac : (hausdorffP n k).restrict E ≪ hausdorffP n k :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  obtain ⟨I, J, H, V, hnull⟩ : HasTypedGraphCover .mixed k E 1 :=
    (And.left finite_hausdorff_criterion) n hn k hk hkn .mixed
      (AdmissibleModel.nonempty_of_range hn hk hkn) E hE hEfin ⟨1, one_pos, hae⟩ 1 one_pos
  obtain ⟨envH, envV⟩ := graph_borel_envelope n k
  choose H' hHsub hHmeas _ using fun i => envH 1 (H i)
  obtain ⟨srcH, srcV⟩ := graph_source_square_finite n hn k hk hkn
  refine typedRefinementSet_of_assignment hn hk hkn hE hEfin (⋃ i, (H' i).image)
    (⋃ j, (V j).image) (MeasurableSet.iUnion hHmeas)
    (MeasurableSet.iUnion fun j => (envV 1 (V j)).1) ?_ ?_ ?_ ?_ ?_
  · refine measure_mono_null ?_ hnull
    intro z hz
    refine ⟨hz.1, fun hzU => hz.2 ?_⟩
    rcases hzU with hzH | hzV
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hzH
      exact Or.inl (mem_iUnion.2 ⟨i, hHsub i hi⟩)
    · exact Or.inr hzV
  · exact (ae_mem_iUnion_imp _ fun i => ae_forall_squareEnergy_lt_top hηac fun R hR =>
      srcH 1 (H' i) _ hηc hηr R hR).mono fun z hz hzB => hz hzB 1 one_pos
  · exact (ae_mem_iUnion_imp _ fun j => ae_forall_squareEnergy_lt_top hηac fun R hR =>
      srcV 1 (V j) _ hηc hηr R hR).mono fun z hz hzB => hz hzB 1 one_pos
  · intro hav
    exact iUnion_eq_empty.2 fun i => absurd (nonempty_horizontalModels_of_graph (H' i) hk) hav
  · intro hav
    exact iUnion_eq_empty.2 fun j => absurd (nonempty_verticalModels_of_graph (V j)) hav

/-- First-type assignment for a graph-carried measure, given Borel type envelopes `BH`,
`BV` with Borel sigma-finite carriers for the two restrictions. `E_H = BH`,
`E_V = BV \ BH`; each available type is refined at every tolerance by intrinsic sufficiency
(`intrinsic_sufficiency_skeleton`), applied to `μ⌊E_T` with
`S_{μ⌊E_T,T} ≤ S_{μ,T}` (`squareEnergy_restrict_le`). -/
theorem typedRefinementMeasure_of_assignment {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkn : k ≤ n + 2) {μ : Measure (Space n)} [IsFiniteMeasureOnCompacts μ] [μ.InnerRegular]
    (hac : μ ≪ hausdorffP n k) (BH BV : Set (Space n)) (hBH : MeasurableSet BH)
    (hBV : MeasurableSet BV) (hcar : μ (BH ∪ BV)ᶜ = 0)
    (sqH : ∀ᵐ z ∂μ, z ∈ BH → squareEnergy μ k .horizontal 1 z < ⊤)
    (sqV : ∀ᵐ z ∂μ, z ∈ BV → squareEnergy μ k .vertical 1 z < ⊤)
    (carH : HasBorelSigmaFiniteHausdorffCarrier k (μ.restrict BH))
    (carV : HasBorelSigmaFiniteHausdorffCarrier k (μ.restrict (BV \ BH)))
    (unH : ¬ Nonempty (Models n k .horizontal) → BH = ∅)
    (unV : ¬ Nonempty (Models n k .vertical) → BV = ∅) :
    ∃ EH EV : Set (Space n), MeasurableSet EH ∧ MeasurableSet EV ∧ Disjoint EH EV ∧
      μ (EH ∪ EV)ᶜ = 0 ∧
      (Nonempty (Models n k .horizontal) →
        ∀ᵐ z ∂μ, z ∈ EH → squareEnergy μ k .horizontal 1 z < ⊤) ∧
      (Nonempty (Models n k .vertical) →
        ∀ᵐ z ∂μ, z ∈ EV → squareEnergy μ k .vertical 1 z < ⊤) ∧
      (∀ ε : ℝ, 0 < ε →
        HasTypedMeasureCover .horizontal k (μ.restrict EH) ε ∧
          HasTypedMeasureCover .vertical k (μ.restrict EV) ε) ∧
      (¬ Nonempty (Models n k .horizontal) → EH = ∅) ∧
      (¬ Nonempty (Models n k .vertical) → EV = ∅) := by
  have piece : ∀ (T : FamilyKind) (P : Set (Space n)), Nonempty (Models n k T) →
      MeasurableSet P → HasBorelSigmaFiniteHausdorffCarrier k (μ.restrict P) →
      (∀ᵐ z ∂μ, z ∈ P → squareEnergy μ k T 1 z < ⊤) →
      ∀ ε : ℝ, 0 < ε → HasTypedMeasureCover T k (μ.restrict P) ε := by
    intro T P hT hP hcarP hsq ε hε
    refine intrinsic_sufficiency_skeleton n hn k hk hkn T hT (μ.restrict P) inferInstance
      inferInstance ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac)
      hcarP ⟨1, one_pos, ?_⟩ ε hε
    filter_upwards [(Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le hsq,
      ae_restrict_mem hP] with z hz hzP
    exact (squareEnergy_restrict_le μ P k T 1 z).trans_lt (hz hzP)
  refine ⟨BH, BV \ BH, hBH, hBV.diff hBH, disjoint_sdiff_right, ?_, fun _ => sqH,
    fun _ => sqV.mono fun z hz hzE => hz hzE.1, ?_, unH, ?_⟩
  · refine measure_mono_null ?_ hcar
    intro z hz
    rw [mem_compl_iff] at hz ⊢
    intro hzU
    apply hz
    rcases hzU with hzH | hzV
    · exact Or.inl hzH
    · by_cases hzBH : z ∈ BH
      · exact Or.inl hzBH
      · exact Or.inr ⟨hzV, hzBH⟩
  · intro ε hε
    constructor
    · by_cases hav : Nonempty (Models n k .horizontal)
      · exact piece .horizontal BH hav hBH carH sqH ε hε
      · rw [unH hav, Measure.restrict_empty]
        exact hasTypedMeasureCover_zero .horizontal ε
    · by_cases hav : Nonempty (Models n k .vertical)
      · exact piece .vertical (BV \ BH) hav (hBV.diff hBH) carV
          (sqV.mono fun z hz hzE => hz hzE.1) ε hε
      · rw [unV hav, Set.empty_sdiff, Measure.restrict_empty]
        exact hasTypedMeasureCover_zero .vertical ε
  · intro hav
    rw [unV hav, Set.empty_sdiff]

/-- **Typed refinement, measure version.** Choose the
finite-norm typed carrier, replace horizontal graphs by Borel closure extensions
(`graph_borel_envelope`), assign each point to its first type, apply graph-source with the
full original `μ` (its Hausdorff-null exceptions are `μ`-null by absolute continuity), and
refine each restriction by intrinsic sufficiency. The restrictions are locally Radon (Mathlib
instances), absolutely continuous, and inherit the bounded envelope pieces as Borel
sigma-finite carriers. -/
theorem typed_refinement_measure_skeleton : TypedRefinementMeasureStatement := by
  intro n hn k hk hkn μ hμ hreg hrect
  obtain ⟨hac, I, J, εH, H, εV, V, hHV⟩ := hrect
  obtain ⟨envH, envV⟩ := graph_borel_envelope n k
  choose H' hHsub hHmeas hHfin using fun i => envH (εH i) (H i)
  obtain ⟨srcH, srcV⟩ := graph_source_square_finite n hn k hk hkn
  have hBH : MeasurableSet (⋃ i, (H' i).image) := MeasurableSet.iUnion hHmeas
  have hBV : MeasurableSet (⋃ j, (V j).image) :=
    MeasurableSet.iUnion fun j => (envV _ (V j)).1
  refine typedRefinementMeasure_of_assignment hn hk hkn hac _ _ hBH hBV ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine measure_mono_null ?_ hHV
    intro z hz
    rw [mem_compl_iff] at hz ⊢
    intro hzU
    apply hz
    rcases hzU with hzH | hzV
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hzH
      exact Or.inl (mem_iUnion.2 ⟨i, hHsub i hi⟩)
    · exact Or.inr hzV
  · exact (ae_mem_iUnion_imp _ fun i => ae_forall_squareEnergy_lt_top hac fun R hR =>
      srcH _ (H' i) μ hμ hreg R hR).mono fun z hz hzB => hz hzB 1 one_pos
  · exact (ae_mem_iUnion_imp _ fun j => ae_forall_squareEnergy_lt_top hac fun R hR =>
      srcV _ (V j) μ hμ hreg R hR).mono fun z hz hzB => hz hzB 1 one_pos
  · refine hasBorelSigmaFiniteHausdorffCarrier_of_cover (fun i => (H' i).image) ?_
      (fun i => (H' i).image) (fun _ => subset_rfl) hHmeas hHfin
    rw [Measure.restrict_apply hBH.compl, compl_inter_self, measure_empty]
  · refine hasBorelSigmaFiniteHausdorffCarrier_of_cover (fun j => (V j).image) ?_
      (fun j => (V j).image) (fun _ => subset_rfl) (fun j => (envV _ (V j)).1)
      (fun j => (envV _ (V j)).2)
    rw [Measure.restrict_apply hBV.compl]
    exact measure_mono_null (fun z hz => hz.1 hz.2.1) measure_empty
  · intro hav
    exact iUnion_eq_empty.2 fun i => absurd (nonempty_horizontalModels_of_graph (H' i) hk) hav
  · intro hav
    exact iUnion_eq_empty.2 fun j => absurd (nonempty_verticalModels_of_graph (V j)) hav

end ParabolicRectifiability.Characterization
