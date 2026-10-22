import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapters
import ParabolicRectifiability.Characterization.Proofs.GraphSource.SquareFinitenessComponents
import ParabolicRectifiability.Characterization.Statements.Branches
import ParabolicRectifiability.Characterization.Assembly.CoveringLemmas

/-! # Square finiteness for graph sources

`b2_graph_source_square_finite` proves `GraphSourceStatement`, the statement of
`graph_source_square_finite`, in the following steps:

1. On a typed reference carrier, for a **finite** ambient source `μ`, `S^1_{μ,T} < ∞` off an
   `H_P^k`-null set (`b2_reference_source_null`): reference estimates give the ADR carrier and
   `S^1_σ < ∞` `σ`-a.e.; `SourceTransferStatement` transfers this to `μ` at `σ`-a.e. carrier
   point; `ADRHausdorffComparisonStatement` turns `σ`-null into `H_P^k`-null.
2. Vertical graphs (`k < n + 2`): the graph image is a reference carrier (vertical adapter).
   Horizontal graphs: countably many compact pieces cover the image modulo `H_P^k`, each lies in
   a reference carrier (horizontal adapter), always with the **same full source** `μ`.
3. Locally finite `μ`: the finite sources `μ⌊P̄(0,N)` have the same square up to endpoint `1`
   on `P(0,N-1)` (`b2_squareEnergy_restrict_closedBall`); the exceptional sets are countably
   many `H_P^k`-null sets. No inequality reversing source restriction is used.
4. Every endpoint `R > 0`: `SquareFinitenessEndpointStatement` (finite annuli).
5. `k = n + 2`: the square vanishes (`AmbientEnergyZeroStatement`); horizontal graphs do not
   exist there, and the horizontal branch is handled uniformly by step 2.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-- Step 1: on a typed reference carrier, a finite ambient source has finite own-type square
`S^1` off an `H_P^k`-null set. -/
theorem b2_reference_source_null :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ L : ℝ, 1 ≤ L →
    ∀ ρ : Reference n k L, Nonempty (Models n k ρ.kind) →
    ∀ μ : Measure (Space n), IsFiniteMeasure μ →
      hausdorffP n k (ρ.carrier ∩ {z | squareEnergy μ k ρ.kind 1 z = ⊤}) = 0 := by
  intro n hn k hk hkn L hL ρ hT μ hμ
  obtain ⟨c, C, hρ⟩ := b2_reference_adr_square n hn k hk hkn L hL
  obtain ⟨hcar, hsq⟩ := hρ ρ
  have htr := b2_input_source_transfer n hn k c C ρ.carrier ρ.measure hcar ρ.kind hT hsq μ hμ
  obtain ⟨a, b, -, -, hcomp⟩ := b2_adr_hausdorff_comparison k c C
  have hnull : ρ.measure (ρ.carrier ∩ {z | squareEnergy μ k ρ.kind 1 z = ⊤}) = 0 := by
    rw [ae_iff] at htr
    refine measure_mono_null ?_ htr
    rintro z ⟨hzΓ, hz⟩ h
    have h' := h hzΓ
    rw [mem_ofPred_eq.mp hz] at h'
    exact lt_irrefl _ h'
  have hle := (hcomp n hn ρ.carrier ρ.measure hcar
    (ρ.carrier ∩ {z | squareEnergy μ k ρ.kind 1 z = ⊤})).2
  rw [hnull, mul_zero] at hle
  have hsub : ρ.carrier ∩ {z | squareEnergy μ k ρ.kind 1 z = ⊤} ⊆
      (ρ.carrier ∩ {z | squareEnergy μ k ρ.kind 1 z = ⊤}) ∩ ρ.carrier :=
    fun z hz => ⟨hz, hz.1⟩
  exact nonpos_iff_eq_zero.1 ((measure_mono hsub).trans hle)

/-- Step 2, horizontal graphs, finite source. -/
theorem b2_horizontal_finite_source_null :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 → ∀ (ε : ℝ) (G : HorizontalGraph n k ε),
    ∀ μ : Measure (Space n), IsFiniteMeasure μ →
      hausdorffP n k (G.image ∩ {z | squareEnergy μ k .horizontal 1 z = ⊤}) = 0 := by
  intro n hn k hk hkn ε G μ hμ
  obtain ⟨L, hL, hHref⟩ := b2_horizontal_graph_reference n k hk ε
  obtain ⟨J, Gc, hGc, hnull⟩ := b2_horizontal_compact_cover n k ε G
  have hpiece : ∀ j : J,
      hausdorffP n k ((Gc j).image ∩ {z | squareEnergy μ k .horizontal 1 z = ⊤}) = 0 := by
    intro j
    obtain ⟨H, hH⟩ := hHref (Gc j) (hGc j).1 (hGc j).2
    have hT : Nonempty (Models n k (Reference.horizontal H : Reference n k L).kind) :=
      HorizontalModel.nonempty_iff.mpr H.available
    have h0 := b2_reference_source_null n hn k hk hkn L hL (Reference.horizontal H) hT μ hμ
    exact measure_mono_null (Set.inter_subset_inter_left _ hH) h0
  refine measure_mono_null ?_ (measure_union_null hnull (measure_iUnion_null hpiece))
  rintro z ⟨hzG, hzN⟩
  by_cases hz : z ∈ ⋃ j, (Gc j).image
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hz
    exact Or.inr (Set.mem_iUnion.2 ⟨j, hj, hzN⟩)
  · exact Or.inl ⟨hzG, hz⟩

/-- Step 2, vertical graphs (`k < n + 2`), finite source. -/
theorem b2_vertical_finite_source_null :
    ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n + 2 →
    ∀ (ε : ℝ) (G : GeneralRegularVerticalGraph n k ε),
    ∀ μ : Measure (Space n), IsFiniteMeasure μ →
      hausdorffP n k (G.image ∩ {z | squareEnergy μ k .vertical 1 z = ⊤}) = 0 := by
  intro n hn k hk hlt ε G μ hμ
  obtain ⟨V, hV⟩ := b2_vertical_graph_reference n k hlt ε G
  obtain ⟨g, K, B, -, -, -, hKB⟩ := G.regular
  have hK0 : (0 : ℝ) ≤ K := NNReal.coe_nonneg K
  have hB0 : (0 : ℝ) ≤ B := NNReal.coe_nonneg B
  have hL : (1 : ℝ) ≤ 1 + ε := by linarith
  have hT : Nonempty (Models n k (Reference.vertical V : Reference n k (1 + ε)).kind) :=
    nonempty_verticalModels_of_graph G
  have h0 := b2_reference_source_null n hn k hk hlt.le (1 + ε) hL (Reference.vertical V) hT μ hμ
  have hc : (Reference.vertical V : Reference n k (1 + ε)).carrier = G.image := hV
  rw [hc] at h0
  exact h0

/-- Step 3: from finite sources to every locally finite source, at endpoint `1`. -/
theorem b2_null_of_finite_sources {n k : ℕ} (T : FamilyKind) (E : Set (Space n))
    (h : ∀ ν : Measure (Space n), IsFiniteMeasure ν →
      hausdorffP n k (E ∩ {z | squareEnergy ν k T 1 z = ⊤}) = 0)
    (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ) :
    hausdorffP n k (E ∩ {z | squareEnergy μ k T 1 z = ⊤}) = 0 := by
  have hN : ∀ N : ℕ, hausdorffP n k (E ∩ {z | squareEnergy
      (μ.restrict (Metric.closedBall (point 0 0) (N : ℝ))) k T 1 z = ⊤}) = 0 := by
    intro N
    have hfin : IsFiniteMeasure (μ.restrict (Metric.closedBall (point 0 0) (N : ℝ))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top⟩
    exact h _ hfin
  refine measure_mono_null ?_ (measure_iUnion_null hN)
  rintro z ⟨hzE, hz⟩
  obtain ⟨N, hN'⟩ := exists_nat_gt (dist z (point 0 0) + 1)
  refine Set.mem_iUnion.2 ⟨N, hzE, ?_⟩
  have heq := b2_squareEnergy_restrict_closedBall n k T μ (point 0 0) (N : ℝ) 1 z hN'.le
  rw [mem_ofPred_eq, heq]
  exact hz

/-- Step 4: every positive endpoint, for a locally Radon source. -/
theorem b2_endpoint_null {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (T : FamilyKind) (μ : Measure (Space n)) (hfin : IsFiniteMeasureOnCompacts μ)
    (hreg : μ.InnerRegular) (E : Set (Space n))
    (h1 : hausdorffP n k (E ∩ {z | squareEnergy μ k T 1 z = ⊤}) = 0) (R : ℝ) (hR : 0 < R) :
    hausdorffP n k (E ∩ {z | squareEnergy μ k T R z = ⊤}) = 0 := by
  have hend := b2_input_square_finiteness_endpoint n hn k hk hkn T μ hfin hreg
  refine measure_mono_null ?_ h1
  rintro z ⟨hzE, hz⟩
  refine ⟨hzE, ?_⟩
  rw [mem_ofPred_eq] at hz ⊢
  by_contra hne
  have h2 := (hend z R 1 hR one_pos).2 (lt_top_iff_ne_top.2 hne)
  rw [hz] at h2
  exact lt_irrefl _ h2

/-- Square finiteness for graph sources: the statement `GraphSourceStatement`. -/
theorem b2_graph_source_square_finite : GraphSourceStatement := by
  intro n hn k hk hkn
  refine ⟨fun ε G μ hfin hreg R hR => ?_, fun ε G μ hfin hreg R hR => ?_⟩
  · exact b2_endpoint_null hn hk hkn .horizontal μ hfin hreg G.image
      (b2_null_of_finite_sources .horizontal G.image
        (b2_horizontal_finite_source_null n hn k hk hkn ε G) μ hfin) R hR
  · by_cases hlt : k < n + 2
    · exact b2_endpoint_null hn hk hkn .vertical μ hfin hreg G.image
        (b2_null_of_finite_sources .vertical G.image
          (b2_vertical_finite_source_null n hn k hk hlt ε G) μ hfin) R hR
    · have hk2 : k = n + 2 := by omega
      subst hk2
      have hzero := (b2_input_ambient_energy_zero n hn μ hfin hreg .vertical
        (nonempty_verticalModels_of_graph G)).2 R hR
      have hempty : G.image ∩ {z | squareEnergy μ (n + 2) .vertical R z = ⊤} = ∅ := by
        ext z
        simp [hzero z]
      rw [hempty, measure_empty]

end ParabolicRectifiability.Characterization
