import ParabolicRectifiability.Characterization.Proofs.NestedPartitions.DifferentiationStatements

/-! # Partition filtration and cell averages

Proof of the named statement `CdCellAverageStatement` (from `b3_cd_cells`): the partition
filtration, the null union of zero-mass cells, and the cell averages as conditional
expectations.

Route:
* `ℱ_j` is increasing by `nested` (`monotone_nat_of_le_succ`) and below the ambient
  σ-algebra by definition;
* the zero-mass cells of all generations have null union (`measure_iUnion_null`,
  `measure_sUnion_null_iff` for the countable `P j`), retained as the first conclusion;
* the cell average is constant on each cell and `0` off `R`, so every preimage satisfies the
  cell condition, and a set satisfying the cell condition and constant on `Rᶜ` is a countable
  union of cells plus `Rᶜ` or `∅`; hence `a_j` is `ℱ_j`-measurable;
* integrability: `∫⁻|a_j| = Σ_Q ∫⁻_Q |a_j| ≤ Σ_Q ∫⁻_Q |h| = ∫⁻|h|` (`ρ Rᶜ = 0`,
  `lintegral_iUnion`), with `∫⁻_Q |a_j| = |∫_Q h|` on cells of positive mass and `0` otherwise;
* identification by `ae_eq_condExp_of_forall_setIntegral_eq`: for `S ∈ ℱ_j`,
  `∫_S f = Σ_Q ∫_{S ∩ Q} f` (`integral_iUnion`), and `S ∩ Q` is `Q` or `∅`, where
  `∫_Q a_j = ∫_Q h` (a zero-mass cell contributes `0` to both sides).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.Characterization.CoordinateDifferentiationTree

variable {Y : Type*} [m : MeasurableSpace Y] {R : Set Y} {P : ℕ → Set (Set Y)}

/-- The cell of a point of a cell `Q ∈ P j` is `Q`. -/
theorem bp2_cd_cells_partitionCell_eq (hP : IsExactNestedBorelPartitions R P) {j : ℕ}
    {Q : Set Y} (hQ : Q ∈ P j) {z : Y} (hz : z ∈ Q) : partitionCell (P j) z = Q := by
  ext x
  simp only [partitionCell, mem_sUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨Q', ⟨hQ', hzQ'⟩, hxQ'⟩
    rwa [(hP.pairwiseDisjoint j).elim_set hQ' hQ z hzQ' hz] at hxQ'
  · exact fun hx => ⟨Q, ⟨hQ, hz⟩, hx⟩

/-- The cell of a point outside `R` is empty. -/
theorem bp2_cd_cells_partitionCell_eq_empty (hP : IsExactNestedBorelPartitions R P) (j : ℕ)
    {z : Y} (hz : z ∉ R) : partitionCell (P j) z = ∅ := by
  ext x
  simp only [partitionCell, mem_sUnion, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨Q, ⟨hQ, hzQ⟩, -⟩
  apply hz
  rw [← hP.sUnion_eq j]
  exact mem_sUnion_of_mem hzQ hQ

theorem bp2_cd_cells_measurableSet_R (hP : IsExactNestedBorelPartitions R P) :
    MeasurableSet R := by
  rw [← hP.sUnion_eq 0]
  exact MeasurableSet.sUnion (hP.countable 0) (hP.measurableSet 0)

theorem bp2_cd_cells_average_of_mem (ρ : Measure Y) (hP : IsExactNestedBorelPartitions R P)
    (h : Y → ℝ) {j : ℕ} {Q : Set Y} (hQ : Q ∈ P j) {z : Y} (hz : z ∈ Q) :
    b3_cd_average ρ P h j z = (ρ Q).toReal⁻¹ * ∫ x in Q, h x ∂ρ := by
  rw [b3_cd_average, bp2_cd_cells_partitionCell_eq hP hQ hz]

theorem bp2_cd_cells_average_of_not_mem (ρ : Measure Y) (hP : IsExactNestedBorelPartitions R P)
    (h : Y → ℝ) (j : ℕ) {z : Y} (hz : z ∉ R) : b3_cd_average ρ P h j z = 0 := by
  simp [b3_cd_average, bp2_cd_cells_partitionCell_eq_empty hP j hz]

/-- A set satisfying the cell condition of generation `j`, and containing or missing `Rᶜ`, is
measurable: it is a countable union of cells together with `Rᶜ` or `∅`. -/
theorem bp2_cd_cells_measurableSet_of_cells (hP : IsExactNestedBorelPartitions R P) (j : ℕ)
    {S : Set Y} (hS : ∀ Q ∈ P j, Q ⊆ S ∨ Disjoint Q S) (hRc : Rᶜ ⊆ S ∨ Disjoint Rᶜ S) :
    MeasurableSet S := by
  have hR := bp2_cd_cells_measurableSet_R hP
  have hdec : S = ⋃₀ {Q | Q ∈ P j ∧ Q ⊆ S} ∪ (S ∩ Rᶜ) := by
    ext x
    constructor
    · intro hx
      by_cases hxR : x ∈ R
      · rw [← hP.sUnion_eq j, mem_sUnion] at hxR
        obtain ⟨Q, hQ, hxQ⟩ := hxR
        refine Or.inl ⟨Q, ⟨hQ, ?_⟩, hxQ⟩
        exact (hS Q hQ).resolve_right fun hd => Set.disjoint_left.1 hd hxQ hx
      · exact Or.inr ⟨hx, hxR⟩
    · rintro (⟨Q, ⟨-, hQS⟩, hxQ⟩ | ⟨hx, -⟩)
      · exact hQS hxQ
      · exact hx
  rw [hdec]
  refine MeasurableSet.union (MeasurableSet.sUnion ((hP.countable j).mono fun Q hQ => hQ.1)
    fun Q hQ => hP.measurableSet j Q hQ.1) ?_
  rcases hRc with hc | hc
  · rw [inter_eq_right.2 hc]
    exact hR.compl
  · rw [inter_comm, hc.inter_eq]
    exact MeasurableSet.empty

theorem bp2_cd_cells_filtration_le (j : ℕ) : b3_cd_filtration P j ≤ m := by
  intro S hS
  exact hS.1

theorem bp2_cd_cells_filtration_mono (hP : IsExactNestedBorelPartitions R P) :
    Monotone (b3_cd_filtration P) := by
  refine monotone_nat_of_le_succ fun j => ?_
  intro S hS
  refine ⟨hS.1, fun Q hQ => ?_⟩
  obtain ⟨Q', hQ', hQQ'⟩ := hP.nested j Q hQ
  rcases hS.2 Q' hQ' with hc | hc
  · exact Or.inl (hQQ'.trans hc)
  · exact Or.inr (hc.mono_left hQQ')

/-- The cell average of generation `j` is `ℱ_j`-measurable. -/
theorem bp2_cd_cells_average_measurable (ρ : Measure Y) (hP : IsExactNestedBorelPartitions R P)
    (h : Y → ℝ) (j : ℕ) : Measurable[b3_cd_filtration P j] (b3_cd_average ρ P h j) := by
  intro B _
  have hcell : ∀ Q ∈ P j, Q ⊆ b3_cd_average ρ P h j ⁻¹' B ∨
      Disjoint Q (b3_cd_average ρ P h j ⁻¹' B) := by
    intro Q hQ
    by_cases hne : ∃ z ∈ Q, b3_cd_average ρ P h j z ∈ B
    · obtain ⟨z, hzQ, hzB⟩ := hne
      left
      intro x hx
      show b3_cd_average ρ P h j x ∈ B
      rwa [bp2_cd_cells_average_of_mem ρ hP h hQ hx, ← bp2_cd_cells_average_of_mem ρ hP h hQ hzQ]
    · right
      exact Set.disjoint_left.2 fun x hx hxB => hne ⟨x, hx, hxB⟩
  refine ⟨bp2_cd_cells_measurableSet_of_cells hP j hcell ?_, hcell⟩
  by_cases hne : ∃ z ∈ Rᶜ, b3_cd_average ρ P h j z ∈ B
  · obtain ⟨z, hzR, hzB⟩ := hne
    left
    intro x hx
    show b3_cd_average ρ P h j x ∈ B
    rwa [bp2_cd_cells_average_of_not_mem ρ hP h j hx,
      ← bp2_cd_cells_average_of_not_mem ρ hP h j hzR]
  · right
    exact Set.disjoint_left.2 fun x hx hxB => hne ⟨x, hx, hxB⟩

theorem bp2_cd_cells_restrict_eq {ρ : Measure Y} (hρR : ρ Rᶜ = 0) : ρ.restrict R = ρ :=
  Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hρR)

theorem bp2_cd_cells_pairwise (hP : IsExactNestedBorelPartitions R P) (j : ℕ) :
    Pairwise fun a b : ↥(P j) => Disjoint (a : Set Y) (b : Set Y) :=
  fun a b hab => (hP.pairwiseDisjoint j) a.2 b.2 (Subtype.coe_injective.ne hab)

theorem bp2_cd_cells_lintegral_eq_tsum {ρ : Measure Y} (hP : IsExactNestedBorelPartitions R P)
    (hρR : ρ Rᶜ = 0) (j : ℕ) (g : Y → ℝ≥0∞) :
    ∫⁻ x, g x ∂ρ = ∑' Q : ↥(P j), ∫⁻ x in (Q : Set Y), g x ∂ρ := by
  have : Countable ↥(P j) := (hP.countable j).to_subtype
  calc ∫⁻ x, g x ∂ρ = ∫⁻ x in R, g x ∂ρ := by rw [bp2_cd_cells_restrict_eq hρR]
    _ = ∫⁻ x in ⋃ Q : ↥(P j), (Q : Set Y), g x ∂ρ := by rw [← sUnion_eq_iUnion, hP.sUnion_eq j]
    _ = _ := lintegral_iUnion (s := fun Q : ↥(P j) => (Q : Set Y))
        (fun Q => hP.measurableSet j Q Q.2) (bp2_cd_cells_pairwise hP j) g

theorem bp2_cd_cells_setIntegral_eq_tsum {ρ : Measure Y} (hP : IsExactNestedBorelPartitions R P)
    (hρR : ρ Rᶜ = 0) (j : ℕ) {f : Y → ℝ} (hf : Integrable f ρ) {S : Set Y}
    (hS : MeasurableSet S) :
    ∫ x in S, f x ∂ρ = ∑' Q : ↥(P j), ∫ x in S ∩ (Q : Set Y), f x ∂ρ := by
  have : Countable ↥(P j) := (hP.countable j).to_subtype
  have hdisj : Pairwise fun a b : ↥(P j) => Disjoint (S ∩ (a : Set Y)) (S ∩ (b : Set Y)) :=
    fun a b hab => Disjoint.mono inter_subset_right inter_subset_right
      (bp2_cd_cells_pairwise hP j hab)
  calc ∫ x in S, f x ∂ρ = ∫ x in S ∩ R, f x ∂ρ := by
        rw [← Measure.restrict_restrict hS, bp2_cd_cells_restrict_eq hρR]
    _ = ∫ x in ⋃ Q : ↥(P j), S ∩ (Q : Set Y), f x ∂ρ := by
        rw [← inter_iUnion, ← sUnion_eq_iUnion, hP.sUnion_eq j]
    _ = _ := integral_iUnion (s := fun Q : ↥(P j) => S ∩ (Q : Set Y))
        (fun Q => hS.inter (hP.measurableSet j Q Q.2)) hdisj hf.integrableOn

/-- On a cell, `∫⁻_Q |a_j| ≤ ∫⁻_Q |h|`. -/
theorem bp2_cd_cells_lintegral_cell_le (ρ : Measure Y) [IsFiniteMeasure ρ]
    (hP : IsExactNestedBorelPartitions R P) (h : Y → ℝ) {j : ℕ} {Q : Set Y} (hQ : Q ∈ P j) :
    ∫⁻ x in Q, ‖b3_cd_average ρ P h j x‖ₑ ∂ρ ≤ ∫⁻ x in Q, ‖h x‖ₑ ∂ρ := by
  have hQm := hP.measurableSet j Q hQ
  have hconst : ∫⁻ x in Q, ‖b3_cd_average ρ P h j x‖ₑ ∂ρ =
      ∫⁻ _ in Q, ‖(ρ Q).toReal⁻¹ * ∫ x in Q, h x ∂ρ‖ₑ ∂ρ :=
    setLIntegral_congr_fun hQm fun x hx => by rw [bp2_cd_cells_average_of_mem ρ hP h hQ hx]
  rw [hconst, setLIntegral_const]
  refine le_trans ?_ (enorm_integral_le_lintegral_enorm _)
  by_cases h0 : ρ Q = 0
  · rw [h0, mul_zero]
    exact zero_le
  · have hfin : ρ Q ≠ ∞ := measure_ne_top ρ Q
    have ht : 0 < (ρ Q).toReal := ENNReal.toReal_pos h0 hfin
    have key : ‖(ρ Q).toReal⁻¹‖ₑ * ρ Q = 1 := by
      rw [Real.enorm_eq_ofReal (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht,
        ENNReal.ofReal_toReal hfin, ENNReal.inv_mul_cancel h0 hfin]
    rw [enorm_mul, mul_comm ‖(ρ Q).toReal⁻¹‖ₑ, mul_assoc, key, mul_one]

/-- The cell average is integrable. -/
theorem bp2_cd_cells_average_integrable {ρ : Measure Y} [IsFiniteMeasure ρ] (hρR : ρ Rᶜ = 0)
    (hP : IsExactNestedBorelPartitions R P) {h : Y → ℝ} (hh : Integrable h ρ) (j : ℕ) :
    Integrable (b3_cd_average ρ P h j) ρ := by
  refine ⟨((bp2_cd_cells_average_measurable ρ hP h j).stronglyMeasurable.mono
    (bp2_cd_cells_filtration_le j)).aestronglyMeasurable, ?_⟩
  show ∫⁻ x, ‖b3_cd_average ρ P h j x‖ₑ ∂ρ < ∞
  rw [bp2_cd_cells_lintegral_eq_tsum hP hρR j]
  calc ∑' Q : ↥(P j), ∫⁻ x in (Q : Set Y), ‖b3_cd_average ρ P h j x‖ₑ ∂ρ
      ≤ ∑' Q : ↥(P j), ∫⁻ x in (Q : Set Y), ‖h x‖ₑ ∂ρ :=
        ENNReal.tsum_le_tsum fun Q => bp2_cd_cells_lintegral_cell_le ρ hP h Q.2
    _ = ∫⁻ x, ‖h x‖ₑ ∂ρ := (bp2_cd_cells_lintegral_eq_tsum hP hρR j _).symm
    _ < ∞ := hh.2

/-- On a cell, `∫_Q a_j = ∫_Q h` (both vanish on a zero-mass cell). -/
theorem bp2_cd_cells_setIntegral_cell_eq (ρ : Measure Y) [IsFiniteMeasure ρ]
    (hP : IsExactNestedBorelPartitions R P) (h : Y → ℝ) {j : ℕ} {Q : Set Y} (hQ : Q ∈ P j) :
    ∫ x in Q, b3_cd_average ρ P h j x ∂ρ = ∫ x in Q, h x ∂ρ := by
  have hQm := hP.measurableSet j Q hQ
  have hconst : ∫ x in Q, b3_cd_average ρ P h j x ∂ρ =
      ∫ _ in Q, ((ρ Q).toReal⁻¹ * ∫ x in Q, h x ∂ρ) ∂ρ :=
    setIntegral_congr_fun hQm fun x hx => bp2_cd_cells_average_of_mem ρ hP h hQ hx
  rw [hconst, setIntegral_const, smul_eq_mul]
  by_cases h0 : ρ Q = 0
  · rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    simp
  · rw [measureReal_def, ← mul_assoc,
      mul_inv_cancel₀ (ENNReal.toReal_pos h0 (measure_ne_top ρ Q)).ne', one_mul]

/-- For `S ∈ ℱ_j` and a cell `Q`, `∫_{S ∩ Q} a_j = ∫_{S ∩ Q} h`. -/
theorem bp2_cd_cells_setIntegral_inter_cell (ρ : Measure Y) [IsFiniteMeasure ρ]
    (hP : IsExactNestedBorelPartitions R P) (h : Y → ℝ) {j : ℕ} {S : Set Y}
    (hS : ∀ Q ∈ P j, Q ⊆ S ∨ Disjoint Q S) (Q : ↥(P j)) :
    ∫ x in S ∩ (Q : Set Y), b3_cd_average ρ P h j x ∂ρ = ∫ x in S ∩ (Q : Set Y), h x ∂ρ := by
  rcases hS Q Q.2 with hQS | hQS
  · rw [inter_eq_right.2 hQS]
    exact bp2_cd_cells_setIntegral_cell_eq ρ hP h Q.2
  · rw [inter_comm, hQS.inter_eq]
    simp only [Measure.restrict_empty, integral_zero_measure]

/-- `CdCellAverageStatement`: the partition filtration is an increasing
sequence of sub-σ-algebras, the zero-mass cells have null union, and the cell averages are
integrable versions of the conditional expectations `𝔼[h | ℱ_j]`. -/
theorem bp2_cd_cells_proof : CdCellAverageStatement := by
  intro Y m R ρ hρ hρR P hP h hh
  have := hρ
  refine ⟨bp2_cd_cells_filtration_mono hP, bp2_cd_cells_filtration_le, ?_, fun j =>
    ⟨bp2_cd_cells_average_integrable hρR hP hh j, ?_⟩⟩
  · exact measure_iUnion_null fun j =>
      (measure_sUnion_null_iff ((hP.countable j).mono fun Q hQ => hQ.1)).2 fun Q hQ => hQ.2
  · refine ae_eq_condExp_of_forall_setIntegral_eq (bp2_cd_cells_filtration_le j) hh
      (fun s _ _ => (bp2_cd_cells_average_integrable hρR hP hh j).integrableOn)
      (fun S hS _ => ?_)
      (bp2_cd_cells_average_measurable ρ hP h j).stronglyMeasurable.aestronglyMeasurable
    rw [bp2_cd_cells_setIntegral_eq_tsum hP hρR j (bp2_cd_cells_average_integrable hρR hP hh j)
        hS.1, bp2_cd_cells_setIntegral_eq_tsum hP hρR j hh hS.1]
    exact tsum_congr fun Q => bp2_cd_cells_setIntegral_inter_cell ρ hP h hS.2 Q

end ParabolicRectifiability.Characterization.CoordinateDifferentiationTree
