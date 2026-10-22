import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.PartitionEnergy

/-! # The unique inner cell

Proof of `d1a_uniqueInner_proof : UniqueInnerStatement`. Let `z ≠ z'` be level-`j` centres and
`x ∈ E ∩ P(z, ℓ_j/4) ∩ C_{j,z'}`. The child-union
identity (`ClosedCellBasics.closedCell_children`) gives a child `v` of `z'` with
`x ∈ C_{j+1,v} ⊆ P(v, 2 ℓ_{j+1}) = P(v, ℓ_j/5)`, so `d(v, z) < ℓ_j/5 + ℓ_j/4 = 9 ℓ_j/20`. The parent
`z'` of `v` is nearest, so `d(v, z') ≤ d(v, z)`, and `d(z, z') < 9 ℓ_j/10 < ℓ_j` contradicts the
separation of the level-`j` net (this is the forced-parent rule, inlined).

The hypothesis `IsClosed E` is not used.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace PartitionEnergy

/-- `ℓ_{j+1} = ℓ_j / 10`. -/
theorem d1auniq_scale_succ (ℓ₀ : ℝ) (j : ℕ) :
    coherentScale ℓ₀ (j + 1) = coherentScale ℓ₀ j / 10 := by
  unfold coherentScale
  rw [pow_succ, div_div]

/-- `ℓ_j > 0` for `ℓ₀ > 0`. -/
theorem d1auniq_scale_pos {ℓ₀ : ℝ} (h : 0 < ℓ₀) (j : ℕ) : 0 < coherentScale ℓ₀ j := by
  unfold coherentScale
  exact div_pos h (pow_pos (by norm_num) j)

/-- **Unique inner cell** (`UniqueInnerStatement`). -/
theorem d1a_uniqueInner_proof : UniqueInnerStatement := by
  intro n E ℓ₀ N _hE hB j z hz z' hz' hzz'
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨_hxE, hxz⟩, hxC⟩
  rw [hB.closedCell_children j z' hz'] at hxC
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hxC
  obtain ⟨hvc, hvpar⟩ := hv
  have hxv' := hB.closedCell_subset_ball (j + 1) v hvc hxv
  rw [Metric.mem_ball] at hxz hxv'
  rw [d1auniq_scale_succ] at hxv'
  have hℓ := d1auniq_scale_pos N.scale_pos j
  have hnear := N.parent_nearest j v hvc z hz
  rw [hvpar] at hnear
  have hsep := N.center_separated j z hz z' hz' hzz'
  have h1 := dist_triangle v x z
  have h2 := dist_triangle z v z'
  rw [dist_comm v x] at h1
  rw [dist_comm z v] at h2
  linarith

end PartitionEnergy

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
