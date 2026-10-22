import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # Basic properties of the slabs

Proof of `SlabBasicsStatement`.

For a direct partition `P` of `supp μ` from the top scale `R`:
* the cell addresses `{Q | Q.2 ∈ 𝒵_{Q.1}}` lie in `⋃ j, (j, ·) '' 𝒵_j`, a countable union of
  countable sets (`center_countable`);
* every slab `(Q ∩ P(a,R)) × [ℓ_Q/10, ℓ_Q)` is Borel (`measurable_cell`, `measurableSet_ball`,
  `measurableSet_Ico`, `MeasurableSet.prod`);
* for a cell `Q`, `Q ⊆ supp μ` (`cell_cover`) and `0 < ℓ_Q/10`, `ℓ_Q = R/10^j ≤ R`
  (`scale_pos`), so the slab lies in `(P(a,R) ∩ supp μ) × (0,R)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- The cell addresses of a direct partition are countable. -/
theorem d1fbasics_isCell_countable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) : {Q : ℕ × Space n | P.IsCell Q}.Countable := by
  refine (Set.countable_iUnion fun j => (P.center_countable j).image (Prod.mk j)).mono ?_
  rintro ⟨j, z⟩ hQ
  exact Set.mem_iUnion.2 ⟨j, z, hQ, rfl⟩

/-- Every slab is Borel. -/
theorem d1fbasics_measurableSet_slab {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) (a : Space n) (R : ℝ) (Q : ℕ × Space n) :
    MeasurableSet (slab P a R Q) :=
  ((P.measurable_cell _ _).inter Metric.isOpen_ball.measurableSet).prod measurableSet_Ico

/-- The scale bounds `0 < ℓ_j/10` and `ℓ_j ≤ ℓ₀`. -/
theorem d1fbasics_scale_bounds {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) (j : ℕ) : 0 < P.scale j / 10 ∧ P.scale j ≤ ℓ₀ := by
  have h0 : 0 < ℓ₀ := P.scale_pos
  have hpow : (1 : ℝ) ≤ 10 ^ j := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 10 ^ j := by positivity
  simp only [DirectPartition.scale, coherentScale]
  refine ⟨div_pos (div_pos h0 hpos) (by norm_num), ?_⟩
  rw [div_le_iff₀ hpos]
  nlinarith

/-- The cell of an address lies in `E`. -/
theorem d1fbasics_cell_subset {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) {Q : ℕ × Space n} (hQ : P.IsCell Q) : P.cellOf Q ⊆ E := by
  intro z hz
  rw [← P.cell_cover Q.1]
  exact Set.mem_iUnion₂.2 ⟨Q.2, hQ, hz⟩

/-- **Slab basics**: the cell addresses are countable, and every slab is a Borel subset of the
tested pairs `(P(a,R) ∩ supp μ) × (0,R)`. -/
theorem d1f_slabBasics_proof : SlabBasicsStatement := by
  intro n μ a R P
  refine ⟨d1fbasics_isCell_countable P, d1fbasics_measurableSet_slab P a R, ?_⟩
  rintro Q hQ ⟨z, r⟩ ⟨⟨hzQ, hza⟩, hr1, hr2⟩
  obtain ⟨hlow, hle⟩ := d1fbasics_scale_bounds P Q.1
  exact ⟨⟨hza, d1fbasics_cell_subset P hQ hzQ⟩, hlow.trans_le hr1, hr2.trans_le hle⟩

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
