import ParabolicRectifiability.Foundations.Proofs.Rectifiability.Sums

/-! # Typed rectifiability from restrictions

This assembly uses the two rectifiability helpers
`f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous` and
`f2i_isRegularlyRectifiableMeasure_sum`.

* `f2i_le_sum_restrict`: a measure carried by countably many sets is dominated by the sum of
  its restrictions to them (pure measure theory; no measurability of the sets).
* `f2i_isRegularlyRectifiableMeasure_of_restrict_cover`: typed regular rectifiability of every
  restriction to a countable family carrying `μ` gives that of `μ` (countable sums, then
  domination).
* `f2i_isRegularlyRectifiableMeasure_mixed_of_typed`: a typed carrier is a mixed carrier (the
  other family is empty).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.Foundations

/-- If countably many sets `s i` carry `μ`, then `μ ≤ Σ_i μ⌊s i`. -/
theorem f2i_le_sum_restrict {n : ℕ} {ι : Type*} [Countable ι] {μ : Measure (Space n)}
    (s : ι → Set (Space n)) (hs : μ (⋃ i, s i)ᶜ = 0) :
    μ ≤ Measure.sum (fun i => μ.restrict (s i)) := by
  refine Measure.le_iff.mpr fun t ht => ?_
  rw [Measure.sum_apply _ ht]
  have h0 : μ (t \ ⋃ i, s i) = 0 := measure_mono_null (fun _ hz => hz.2) hs
  calc μ t ≤ μ (t ∩ ⋃ i, s i) + μ (t \ ⋃ i, s i) := measure_le_inter_add_sdiff μ t _
    _ = μ (⋃ i, t ∩ s i) := by rw [h0, add_zero, inter_iUnion]
    _ ≤ ∑' i, μ (t ∩ s i) := measure_iUnion_le _
    _ = ∑' i, μ.restrict (s i) t := by simp only [Measure.restrict_apply ht]

/-- Typed regular rectifiability of each restriction `μ⌊s i` to a countable family carrying `μ`
gives typed regular rectifiability of `μ`: S2 for the sum of the restrictions, then S1, since
`μ` is dominated by that sum. -/
theorem f2i_isRegularlyRectifiableMeasure_of_restrict_cover {n k : ℕ} {ι : Type*} [Countable ι]
    (T : FamilyKind) {μ : Measure (Space n)} (s : ι → Set (Space n))
    (hs : μ (⋃ i, s i)ᶜ = 0)
    (hrect : ∀ i, IsRegularlyRectifiableMeasure T k (μ.restrict (s i))) :
    IsRegularlyRectifiableMeasure T k μ :=
  f2i_isRegularlyRectifiableMeasure_of_absolutelyContinuous T
    (f2i_isRegularlyRectifiableMeasure_sum T (fun i => μ.restrict (s i)) fun i _ => hrect i)
    (Measure.absolutelyContinuous_of_le (f2i_le_sum_restrict s hs))

/-- A typed (horizontal or vertical) regularly rectifiable measure is regularly mixed
rectifiable: the other family of the mixed carrier is empty. -/
theorem f2i_isRegularlyRectifiableMeasure_mixed_of_typed {n k : ℕ} (T : FamilyKind)
    {μ : Measure (Space n)} (h : IsRegularlyRectifiableMeasure T k μ) :
    IsRegularlyRectifiableMeasure .mixed k μ := by
  obtain ⟨hac, hcar⟩ := h
  refine ⟨hac, ?_⟩
  cases T with
  | horizontal =>
    obtain ⟨I, ε, H, hH⟩ := hcar
    exact ⟨I, ∅, ε, H, fun _ => 0, fun j => (notMem_empty _ j.2).elim,
      measure_mono_null (compl_subset_compl.mpr subset_union_left) hH⟩
  | vertical =>
    obtain ⟨J, ε, V, hV⟩ := hcar
    exact ⟨∅, J, fun _ => 0, fun i => (notMem_empty _ i.2).elim, ε, V,
      measure_mono_null (compl_subset_compl.mpr subset_union_right) hV⟩
  | mixed => exact hcar

end ParabolicRectifiability.Foundations
