import ParabolicRectifiability.Measure.Neck.DecompositionTree.TreeDepth

/-!
# The global measure identity of the decomposition tree

Proof of `StepTree.measure_eq_error`, as `StepTree.measure_eq_error_proof`.

The error sets `e_v`, the core assignments `S_v⁰` and the residual `A_∞` of the tree are
pairwise disjoint Borel sets whose union is exactly the root source `S` (follow a point of
`S` down the local partitions: it either stops in some `e_v` or `S_v⁰`, or lies in a
source at every depth, i.e. in `A_∞`). Since `ν` is carried by `S`, countable additivity
of restrictions gives `ν = ∑_v ν|e_v + ∑_v ν|S_v⁰ + ν|A_∞` directly; the residual
restriction is retained. The error bound is `∑_v E B R_v^k ≤ 2 E B R^k` (`StepTree.radius_total_le_proof`), and the
cores and the residual lie in the carrier, so `ν(X \ K) ≤ ∑_v ν(e_v)`. Finiteness of `ν`
is not needed for this exact-partition argument.
-/

noncomputable section

namespace ParabolicRectifiability

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Function

namespace StepTree

variable {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n} {R B Eerr ρ ε : ℝ}
  {ν : Measure (Space n)}

/-- The error set of a vertex avoids every deeper source. -/
theorem ms7_errorSet_disjoint_deeper (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    (hv : v ∈ Tr.vertices) {w : List ℕ} (hw : w ∈ Tr.vertices) (hlen : v.length < w.length) :
    Disjoint (Tr.step v).errorSet (Tr.source w) :=
  Tr.ms7_disjoint_deeper hv (Tr.step v).errorSet_subset
    (fun i hi => Tr.disjoint_errorSet_child v i hi) hw hlen

/-- The core assignment of a vertex avoids every deeper source. -/
theorem ms7_coreSet_disjoint_deeper (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    (hv : v ∈ Tr.vertices) {w : List ℕ} (hw : w ∈ Tr.vertices) (hlen : v.length < w.length) :
    Disjoint (Tr.step v).coreSet (Tr.source w) :=
  Tr.ms7_disjoint_deeper hv (Tr.step v).coreSet_subset
    (fun i hi => Tr.disjoint_coreSet_child v i hi) hw hlen

/-- Pieces `X_v, Y_w` of distinct vertices, inside their sources and avoiding deeper sources,
are disjoint. -/
theorem ms7_pieces_disjoint (Tr : StepTree ν k F S q R B Eerr ρ ε)
    {X Y : List ℕ → Set (Space n)} (hX : ∀ v, X v ⊆ Tr.source v) (hY : ∀ v, Y v ⊆ Tr.source v)
    (hXd : ∀ v ∈ Tr.vertices, ∀ w ∈ Tr.vertices, v.length < w.length →
      Disjoint (X v) (Tr.source w))
    (hYd : ∀ v ∈ Tr.vertices, ∀ w ∈ Tr.vertices, v.length < w.length →
      Disjoint (Y v) (Tr.source w))
    {v w : List ℕ} (hv : v ∈ Tr.vertices) (hw : w ∈ Tr.vertices) (hne : v ≠ w) :
    Disjoint (X v) (Y w) := by
  rcases lt_trichotomy v.length w.length with h | h | h
  · exact (hXd v hv w hw h).mono_right (hY w)
  · exact (Tr.ms7_disjoint_source_of_length_eq _ v w hv hw rfl h.symm hne).mono (hX v) (hY w)
  · exact ((hYd w hw v hv h).mono_right (hX v)).symm

/-- A piece of `v` avoiding all deeper sources avoids the residual set. -/
theorem ms7_disjoint_residual (Tr : StepTree ν k F S q R B Eerr ρ ε) {v : List ℕ}
    {X : Set (Space n)}
    (hX : ∀ w ∈ Tr.vertices, v.length < w.length → Disjoint X (Tr.source w)) :
    Disjoint X (treeResidual Tr.vertices Tr.source) := by
  rw [Set.disjoint_right]
  intro z hzA hzX
  obtain ⟨w, hw, hlen, hzw⟩ := ms7_mem_treeResidual.mp hzA (v.length + 1)
  exact Set.disjoint_left.mp (hX w hw (by omega)) hzX hzw

theorem ms7_measurableSet_residual (Tr : StepTree ν k F S q R B Eerr ρ ε) :
    MeasurableSet (treeResidual Tr.vertices Tr.source) :=
  MeasurableSet.iInter fun _ => MeasurableSet.biUnion (Set.to_countable _) fun v hv =>
    MeasurableSet.iUnion fun _ => Tr.measurableSet_source v hv

/-- The root source is covered by the error sets, the core assignments and the residual. -/
theorem ms7_cover (Tr : StepTree ν k F S q R B Eerr ρ ε) :
    S ⊆ (⋃ v : Tr.vertices, (Tr.step v).errorSet) ∪ (⋃ v : Tr.vertices, (Tr.step v).coreSet) ∪
      treeResidual Tr.vertices Tr.source := by
  intro z hzS
  by_contra hz
  simp only [mem_union, mem_iUnion, not_or, not_exists] at hz
  obtain ⟨⟨he, hc⟩, hA⟩ := hz
  apply hA
  rw [ms7_mem_treeResidual]
  intro j
  induction j with
  | zero => exact ⟨[], Tr.root_mem, rfl, by rw [Tr.source_root]; exact hzS⟩
  | succ j ih =>
    obtain ⟨v, hv, hlen, hzv⟩ := ih
    rcases Tr.cover v hv hzv with (h1 | h2) | h3
    · exact absurd h1 (he ⟨v, hv⟩)
    · exact absurd h2 (hc ⟨v, hv⟩)
    · simp only [mem_iUnion] at h3
      obtain ⟨i, hi, hzi⟩ := h3
      exact ⟨v ++ [i], hi, by simp [hlen], hzi⟩

/-- The exact identity `ν = ∑_v ν|e_v + ∑_v ν|S_v⁰ + ν|A_∞`. -/
theorem ms7_measure_identity (Tr : StepTree ν k F S q R B Eerr ρ ε) (hS : ν Sᶜ = 0) :
    ν = Measure.sum (fun v : Tr.vertices => ν.restrict (Tr.step v).errorSet) +
        Measure.sum (fun v : Tr.vertices => ν.restrict (Tr.step v).coreSet) +
        ν.restrict (treeResidual Tr.vertices Tr.source) := by
  have hdE : ∀ v ∈ Tr.vertices, ∀ w ∈ Tr.vertices, v.length < w.length →
      Disjoint (Tr.step v).errorSet (Tr.source w) :=
    fun v hv w hw h => Tr.ms7_errorSet_disjoint_deeper hv hw h
  have hdC : ∀ v ∈ Tr.vertices, ∀ w ∈ Tr.vertices, v.length < w.length →
      Disjoint (Tr.step v).coreSet (Tr.source w) :=
    fun v hv w hw h => Tr.ms7_coreSet_disjoint_deeper hv hw h
  have hsubE : ∀ v, (Tr.step v).errorSet ⊆ Tr.source v := fun v => (Tr.step v).errorSet_subset
  have hsubC : ∀ v, (Tr.step v).coreSet ⊆ Tr.source v := fun v => (Tr.step v).coreSet_subset
  have hpE : Pairwise (Disjoint on fun v : Tr.vertices => (Tr.step v).errorSet) :=
    fun a b hab => Tr.ms7_pieces_disjoint hsubE hsubE hdE hdE a.2 b.2
      (fun h => hab (Subtype.ext h))
  have hpC : Pairwise (Disjoint on fun v : Tr.vertices => (Tr.step v).coreSet) :=
    fun a b hab => Tr.ms7_pieces_disjoint hsubC hsubC hdC hdC a.2 b.2
      (fun h => hab (Subtype.ext h))
  have hmE : ∀ v : Tr.vertices, MeasurableSet (Tr.step v).errorSet :=
    fun v => (Tr.step v).measurableSet_errorSet
  have hmC : ∀ v : Tr.vertices, MeasurableSet (Tr.step v).coreSet :=
    fun v => (Tr.step v).measurableSet_coreSet
  have hEC : Disjoint (⋃ v : Tr.vertices, (Tr.step v).errorSet)
      (⋃ v : Tr.vertices, (Tr.step v).coreSet) := by
    refine Set.disjoint_iUnion_left.mpr fun v => Set.disjoint_iUnion_right.mpr fun w => ?_
    by_cases h : (v : List ℕ) = w
    · rw [h]; exact (Tr.step w).disjoint_errorSet_coreSet
    · exact Tr.ms7_pieces_disjoint hsubE hsubC hdE hdC v.2 w.2 h
  have hECA : Disjoint ((⋃ v : Tr.vertices, (Tr.step v).errorSet) ∪
      (⋃ v : Tr.vertices, (Tr.step v).coreSet)) (treeResidual Tr.vertices Tr.source) := by
    refine Set.disjoint_union_left.mpr ⟨Set.disjoint_iUnion_left.mpr fun v => ?_,
      Set.disjoint_iUnion_left.mpr fun v => ?_⟩
    · exact Tr.ms7_disjoint_residual fun w hw h => hdE v v.2 w hw h
    · exact Tr.ms7_disjoint_residual fun w hw h => hdC v v.2 w hw h
  have hSeq : S = (⋃ v : Tr.vertices, (Tr.step v).errorSet) ∪
      (⋃ v : Tr.vertices, (Tr.step v).coreSet) ∪ treeResidual Tr.vertices Tr.source := by
    refine Subset.antisymm Tr.ms7_cover (union_subset (union_subset ?_ ?_) ?_)
    · exact iUnion_subset fun v => (hsubE v).trans (Tr.ms7_source_subset_root v.2)
    · exact iUnion_subset fun v => (hsubC v).trans (Tr.ms7_source_subset_root v.2)
    · exact Tr.ms7_residual_subset_root.trans (Tr.ms7_source_subset_root Tr.root_mem)
  calc ν = ν.restrict S := (Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hS)).symm
    _ = ν.restrict ((⋃ v : Tr.vertices, (Tr.step v).errorSet) ∪
          (⋃ v : Tr.vertices, (Tr.step v).coreSet) ∪ treeResidual Tr.vertices Tr.source) :=
        congrArg ν.restrict hSeq
    _ = ν.restrict (⋃ v : Tr.vertices, (Tr.step v).errorSet) +
          ν.restrict (⋃ v : Tr.vertices, (Tr.step v).coreSet) +
          ν.restrict (treeResidual Tr.vertices Tr.source) := by
        rw [Measure.restrict_union hECA Tr.ms7_measurableSet_residual,
          Measure.restrict_union hEC (MeasurableSet.iUnion hmC)]
    _ = _ := by rw [Measure.restrict_iUnion hpE hmE, Measure.restrict_iUnion hpC hmC]

/-- The total error bound `∑_v ν(e_v) ≤ 2 E B R^k`. -/
theorem ms7_error_tsum_le (Tr : StepTree ν k F S q R B Eerr ρ ε) (hR : 0 < R) (hB : 0 < B) :
    ∑' v : Tr.vertices, ν (Tr.step v).errorSet ≤ ENNReal.ofReal (2 * Eerr * B * R ^ k) := by
  have hle : ∀ v : Tr.vertices,
      ν (Tr.step v).errorSet ≤ ENNReal.ofReal (Eerr * B * Tr.radius v ^ k) :=
    fun v => Tr.errorSet_le v v.2
  rcases le_or_gt Eerr 0 with hE | hE
  · have hz : ∀ v : Tr.vertices, ν (Tr.step v).errorSet = 0 := by
      intro v
      refine le_antisymm ((hle v).trans_eq (ENNReal.ofReal_eq_zero.mpr ?_)) zero_le
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hE hB.le)
        (pow_nonneg (Tr.radius_pos v v.2).le k)
    simp [hz]
  · have hEB : 0 ≤ Eerr * B := mul_nonneg hE.le hB.le
    calc ∑' v : Tr.vertices, ν (Tr.step v).errorSet
        ≤ ∑' v : Tr.vertices, ENNReal.ofReal (Eerr * B) * ENNReal.ofReal (Tr.radius v ^ k) :=
          ENNReal.tsum_le_tsum fun v => (hle v).trans_eq (ENNReal.ofReal_mul hEB)
      _ = ENNReal.ofReal (Eerr * B) * ∑' v : Tr.vertices, ENNReal.ofReal (Tr.radius v ^ k) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (Eerr * B) * ENNReal.ofReal (2 * R ^ k) := by
          gcongr; exact Tr.radius_total_le_proof hR
      _ = ENNReal.ofReal (2 * Eerr * B * R ^ k) := by
          rw [← ENNReal.ofReal_mul hEB]; congr 1; ring

/-- Mass outside the carrier is error mass. -/
theorem ms7_carrier_compl_le (Tr : StepTree ν k F S q R B Eerr ρ ε) (hS : ν Sᶜ = 0) :
    ν Tr.carrierᶜ ≤ ∑' v : Tr.vertices, ν (Tr.step v).errorSet := by
  have hsub : Tr.carrierᶜ ⊆ (⋃ v : Tr.vertices, (Tr.step v).errorSet) ∪ Sᶜ := by
    intro z hz
    by_cases hzS : z ∈ S
    · rcases Tr.ms7_cover hzS with (hE | hC) | hA
      · exact Or.inl hE
      · exfalso
        obtain ⟨v, hv⟩ := mem_iUnion.mp hC
        exact hz (Tr.core_subset_carrier v.2 ((Tr.step v).coreSet_subset_core hv))
      · exact absurd (Tr.residual_subset_carrier hA) hz
    · exact Or.inr hzS
  calc ν Tr.carrierᶜ ≤ ν ((⋃ v : Tr.vertices, (Tr.step v).errorSet) ∪ Sᶜ) := measure_mono hsub
    _ ≤ ν (⋃ v : Tr.vertices, (Tr.step v).errorSet) + ν Sᶜ := measure_union_le _ _
    _ = ν (⋃ v : Tr.vertices, (Tr.step v).errorSet) := by rw [hS, add_zero]
    _ ≤ ∑' v : Tr.vertices, ν (Tr.step v).errorSet := measure_iUnion_le _

/-- **`StepTree.measure_eq_error`**: `ν = ∑_v ν|e_v + ∑_v ν|S_v⁰ + ν|A_∞`, with `e(X) ≤ ∑_v E B R_v^k ≤ 2 E B R^k`;
since the core assignments lie in the cores and `A_∞` in the carrier,
`ν(X \ K) ≤ 2 E B R^k`. -/
theorem measure_eq_error_proof {n k : ℕ} {F : FamilyKind} {S : Set (Space n)} {q : Space n}
    {R B Eerr ρ ε : ℝ} {ν : Measure (Space n)} (Tr : StepTree ν k F S q R B Eerr ρ ε)
    (_hν : IsFiniteMeasure ν) (hS : ν Sᶜ = 0) (hR : 0 < R) (hB : 0 < B) :
    ν = Measure.sum (fun v : Tr.vertices => ν.restrict (Tr.step v).errorSet) +
        Measure.sum (fun v : Tr.vertices => ν.restrict (Tr.step v).coreSet) +
        ν.restrict (treeResidual Tr.vertices Tr.source) ∧
      Measure.sum (fun v : Tr.vertices => ν.restrict (Tr.step v).errorSet) univ ≤
        ENNReal.ofReal (2 * Eerr * B * R ^ k) ∧
      ν Tr.carrierᶜ ≤ ENNReal.ofReal (2 * Eerr * B * R ^ k) := by
  refine ⟨Tr.ms7_measure_identity hS, ?_,
    (Tr.ms7_carrier_compl_le hS).trans (Tr.ms7_error_tsum_le hR hB)⟩
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_apply_univ]
  exact Tr.ms7_error_tsum_le hR hB

end StepTree

end ParabolicRectifiability
