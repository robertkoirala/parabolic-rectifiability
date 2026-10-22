import ParabolicRectifiability.Foundations.GraphDomainCover
import ParabolicRectifiability.Metric.BaseVolume

/-! # First-graph assignment and the trace estimate

Proofs of `horizontal_assignment_proof` and `vertical_assignment_proof`, the statements
`Enhancements.GraphDomainTree.horizontal_assignment` and `vertical_assignment`.

Route: the first-graph traces `F_j = (K ∩ Γ_j) \ ⋃_{i<j} Γ_i` (order of `ℕ`) are Borel
because `K` and the graph images are, pairwise disjoint, and `⋃ F_j = K ∩ ⋃ Γ_j`. The trace
preimages are the actual graph preimages; they are bounded because the inverse projection is
`1`-Lipschitz and `F_j ⊆ K`. For Borel `U`, the preimage of `F_j ∩ U` has image inside
`F_j ∩ U`, so the lower comparison gives `λ_j ≤ c H(F_j ∩ U)`, and countable additivity on
the disjoint Borel sets `F_j ∩ U ⊆ K ∩ U` gives the sum bound. Any `c ∈ [0, ∞]`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Enhancements.GraphDomainTree

open ParabolicRectifiability.Foundations

/-! ## The first-graph traces of an abstract countable family -/

/-- The first-graph trace `F_j = (K ∩ Γ_j) \ ⋃_{i<j} Γ_i` of a family indexed by `J ⊆ ℕ`. -/
def gdb78_firstTrace {X : Type*} (K : Set X) (J : Set ℕ) (Γ : J → Set X) (j : J) : Set X :=
  (K ∩ Γ j) \ ⋃ (i : J) (_ : (i : ℕ) < j), Γ i

theorem gdb78_firstTrace_measurable {X : Type*} [MeasurableSpace X] (K : Set X) {J : Set ℕ}
    (Γ : J → Set X) (hK : MeasurableSet K) (hΓ : ∀ j, MeasurableSet (Γ j)) (j : J) :
    MeasurableSet (gdb78_firstTrace K J Γ j) :=
  (hK.inter (hΓ j)).diff (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hΓ i)

theorem gdb78_firstTrace_subset {X : Type*} (K : Set X) {J : Set ℕ} (Γ : J → Set X) (j : J) :
    gdb78_firstTrace K J Γ j ⊆ K ∩ Γ j :=
  sdiff_subset

theorem gdb78_firstTrace_disjoint {X : Type*} (K : Set X) {J : Set ℕ} (Γ : J → Set X) :
    Pairwise fun i j => Disjoint (gdb78_firstTrace K J Γ i) (gdb78_firstTrace K J Γ j) := by
  have key : ∀ i j : J, (i : ℕ) < j →
      Disjoint (gdb78_firstTrace K J Γ i) (gdb78_firstTrace K J Γ j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact hxj.2 (mem_iUnion₂.2 ⟨i, hij, hxi.1.2⟩)
  intro i j hne
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · exact key i j h
  · exact absurd (Subtype.ext h) hne
  · exact (key j i h).symm

theorem gdb78_iUnion_firstTrace {X : Type*} (K : Set X) {J : Set ℕ} (Γ : J → Set X) :
    (⋃ j, gdb78_firstTrace K J Γ j) = K ∩ ⋃ j, Γ j := by
  classical
  apply Subset.antisymm
  · exact iUnion_subset fun j =>
      (gdb78_firstTrace_subset K Γ j).trans (inter_subset_inter_right K (subset_iUnion Γ j))
  · rintro x ⟨hxK, hx⟩
    have hex : ∃ m : ℕ, ∃ hm : m ∈ J, x ∈ Γ ⟨m, hm⟩ := by
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact ⟨j, j.2, hj⟩
    obtain ⟨hm, hxm⟩ := Nat.find_spec hex
    refine mem_iUnion.2 ⟨⟨Nat.find hex, hm⟩, ⟨hxK, hxm⟩, ?_⟩
    intro hx'
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx'
    exact Nat.find_min hex hi ⟨i.2, hxi⟩

theorem gdb78_firstTrace_null {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X)
    {J : Set ℕ} (Γ : J → Set X) (hcov : μ (K \ ⋃ j, Γ j) = 0) :
    μ (K \ ⋃ j, gdb78_firstTrace K J Γ j) = 0 := by
  rw [gdb78_iUnion_firstTrace]
  refine measure_mono_null ?_ hcov
  rintro x ⟨hxK, hx⟩
  exact ⟨hxK, fun h => hx ⟨hxK, h⟩⟩

/-! ## Summation and boundedness -/

/-- Countable additivity on the disjoint Borel sets `F_j ∩ U ⊆ K ∩ U`, for any `c ∈ [0, ∞]`. -/
theorem gdb78_tsum_le {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X) {J : Set ℕ}
    (c : ℝ≥0∞) (F : J → Set X) (hFm : ∀ j, MeasurableSet (F j)) (hFK : ∀ j, F j ⊆ K)
    (hdisj : Pairwise fun i j => Disjoint (F i) (F j)) (U : Set X) (hU : MeasurableSet U)
    (a : J → ℝ≥0∞) (ha : ∀ j, a j ≤ c * μ (F j ∩ U)) :
    ∑' j, a j ≤ c * μ (K ∩ U) := by
  calc ∑' j, a j ≤ ∑' j, c * μ (F j ∩ U) := ENNReal.tsum_le_tsum ha
    _ = c * ∑' j, μ (F j ∩ U) := ENNReal.tsum_mul_left
    _ = c * μ (⋃ j, F j ∩ U) := by
        rw [measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left)
          (fun j => (hFm j).inter hU)]
    _ ≤ c * μ (K ∩ U) := by
        gcongr
        exact iUnion_subset fun j => inter_subset_inter_left U (hFK j)

/-- A set whose pairwise distances are dominated by distances of points of a bounded set is
bounded. -/
theorem gdb78_isBounded {Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z] (S : Set Y)
    (K : Set Z) (hK : Bornology.IsBounded K)
    (hS : ∀ y ∈ S, ∀ y' ∈ S, ∃ z ∈ K, ∃ z' ∈ K, dist y y' ≤ dist z z') :
    Bornology.IsBounded S := by
  refine Metric.isBounded_iff.2 ⟨Metric.diam K, ?_⟩
  intro y hy y' hy'
  obtain ⟨z, hz, z', hz', h⟩ := hS y hy y' hy'
  exact h.trans (Metric.dist_le_diam_of_mem hK hz hz')

/-! ## The horizontal assignment -/

/-- The horizontal trace preimage of `F ∩ U` is the base image of the graph-map preimage. -/
theorem gdb78_horizontalPreimage_inter {n k : ℕ} {ε : ℝ} (G : HorizontalGraph n k ε)
    (F U : Set (Space n)) :
    horizontalPreimage G F ∩ horizontalPreimage G U =
      Subtype.val '' (horizontalGraphMap G ⁻¹' (F ∩ U)) := by
  ext u
  constructor
  · rintro ⟨⟨h, h1⟩, ⟨h', h2⟩⟩
    exact ⟨⟨u, h⟩, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨w.2, h1⟩, ⟨w.2, h2⟩⟩

/-- Proof of `horizontal_assignment`: first-graph assignment and trace estimate. -/
theorem horizontal_assignment_proof {n k : ℕ} {ε : ℝ} (c : ℝ≥0∞) (K : Set (Space n))
    (hKm : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (J : Set ℕ) (G : J → HorizontalGraph n k ε)
    (himage : ∀ j, MeasurableSet (G j).image)
    (_hpre : ∀ j (F : Set (Space n)), MeasurableSet F → MeasurableSet (horizontalPreimage (G j) F))
    (hproj : ∀ j (u w : (G j).domain), dist (u : (G j).direction) (w : (G j).direction) ≤
      dist (horizontalGraphMap (G j) u) (horizontalGraphMap (G j) w))
    (hlow : ∀ j (A : Set (G j).domain), volume (Subtype.val '' A : Set (G j).direction) ≤
      c * hausdorffP n k (horizontalGraphMap (G j) '' A))
    (hcov : hausdorffP n k (K \ ⋃ j, (G j).image) = 0) :
    ∃ F : J → Set (Space n),
      (∀ j, MeasurableSet (F j)) ∧ (∀ j, F j ⊆ K ∩ (G j).image) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      hausdorffP n k (K \ ⋃ j, F j) = 0 ∧
      (∀ j, Bornology.IsBounded (horizontalPreimage (G j) (F j))) ∧
      ∀ U : Set (Space n), MeasurableSet U →
        ∑' j, volume (horizontalPreimage (G j) (F j) ∩ horizontalPreimage (G j) U) ≤
          c * hausdorffP n k (K ∩ U) := by
  let Γ : J → Set (Space n) := fun j => (G j).image
  have hFm := gdb78_firstTrace_measurable K Γ hKm himage
  have hFsub := gdb78_firstTrace_subset K Γ
  refine ⟨gdb78_firstTrace K J Γ, hFm, hFsub, gdb78_firstTrace_disjoint K Γ,
    gdb78_firstTrace_null (hausdorffP n k) K Γ hcov, ?_, ?_⟩
  · intro j
    refine gdb78_isBounded _ K hKb ?_
    rintro u ⟨h, hu⟩ u' ⟨h', hu'⟩
    exact ⟨_, (hFsub j hu).1, _, (hFsub j hu').1, hproj j ⟨u, h⟩ ⟨u', h'⟩⟩
  · intro U hU
    refine gdb78_tsum_le (hausdorffP n k) K c _ hFm (fun j => (hFsub j).trans inter_subset_left)
      (gdb78_firstTrace_disjoint K Γ) U hU _ ?_
    intro j
    rw [gdb78_horizontalPreimage_inter]
    refine (hlow j _).trans ?_
    gcongr
    exact image_preimage_subset _ _

/-! ## The vertical assignment -/

/-- Proof of `vertical_assignment`: first-graph assignment and trace estimate. -/
theorem vertical_assignment_proof {n k : ℕ} {ε : ℝ} (c : ℝ≥0∞) (K : Set (Space n))
    (hKm : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (J : Set ℕ) (G : J → GeneralRegularVerticalGraph n k ε)
    (himage : ∀ j, MeasurableSet (G j).image)
    (_hpre : ∀ j (F : Set (Space n)), MeasurableSet F → MeasurableSet ((G j).map ⁻¹' F))
    (hproj : ∀ j (p q : SubspaceSpace (G j).direction), dist p q ≤ dist ((G j).map p) ((G j).map q))
    (hlow : ∀ j (A : Set (SubspaceSpace (G j).direction)),
      intrinsicParabolicVolume (G j).direction A ≤ c * hausdorffP n k ((G j).map '' A))
    (hcov : hausdorffP n k (K \ ⋃ j, (G j).image) = 0) :
    ∃ F : J → Set (Space n),
      (∀ j, MeasurableSet (F j)) ∧ (∀ j, F j ⊆ K ∩ (G j).image) ∧
      (Pairwise fun i j => Disjoint (F i) (F j)) ∧
      hausdorffP n k (K \ ⋃ j, F j) = 0 ∧
      (∀ j, Bornology.IsBounded ((G j).map ⁻¹' F j)) ∧
      ∀ U : Set (Space n), MeasurableSet U →
        ∑' j, intrinsicParabolicVolume (G j).direction ((G j).map ⁻¹' F j ∩ (G j).map ⁻¹' U) ≤
          c * hausdorffP n k (K ∩ U) := by
  let Γ : J → Set (Space n) := fun j => (G j).image
  have hFm := gdb78_firstTrace_measurable K Γ hKm himage
  have hFsub := gdb78_firstTrace_subset K Γ
  refine ⟨gdb78_firstTrace K J Γ, hFm, hFsub, gdb78_firstTrace_disjoint K Γ,
    gdb78_firstTrace_null (hausdorffP n k) K Γ hcov, ?_, ?_⟩
  · intro j
    refine gdb78_isBounded _ K hKb ?_
    intro p hp q hq
    exact ⟨_, (hFsub j hp).1, _, (hFsub j hq).1, hproj j p q⟩
  · intro U hU
    refine gdb78_tsum_le (hausdorffP n k) K c _ hFm (fun j => (hFsub j).trans inter_subset_left)
      (gdb78_firstTrace_disjoint K Γ) U hU _ ?_
    intro j
    rw [← preimage_inter]
    refine (hlow j _).trans ?_
    gcongr
    exact image_preimage_subset _ _

end ParabolicRectifiability.Enhancements.GraphDomainTree
