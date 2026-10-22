import ParabolicRectifiability.Examples.Proofs.DecoratedSegment.SegmentStatements

/-! # Decomposing a countable family of horizontal segments into distinct levels

Pad the countable set of heights with the natural numbers before enumerating it.
Taking a section of the union at each height merges overlapping segments; the
resulting planar sections are disjoint Borel sets. Countable additivity of
restricted Hausdorff measure and the supplied one-level identity then give the
measure decomposition, without any finiteness assumption on the total mass.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace ParabolicRectifiability.Examples

open ParabolicRectifiability.BetaP (Plane horizontalSegment)

/-- The distinct level decomposition of any countable family of horizontal segments. -/
theorem e2_sap_levels_proof (hL : E2sapLevelMeasureStatement) : E2sapLevels := by
  classical
  intro I u v b
  let H : Set ℝ := Set.range b ∪ Set.range (fun n : ℕ => (n : ℝ))
  have hH : H.Countable := (Set.countable_range b).union (Set.countable_range _)
  let : Countable H := hH.to_subtype
  let pad : ℕ → H := fun n => ⟨n, Or.inr ⟨n, rfl⟩⟩
  have hpad : Function.Injective pad := by
    intro n m h
    exact Nat.cast_injective (congrArg Subtype.val h)
  let : Infinite H := Infinite.of_injective pad hpad
  let e : ℕ ≃ H := Classical.choice inferInstance
  let c : ℕ → ℝ := fun k => (e k).val
  have hc : Function.Injective c := Subtype.val_injective.comp e.injective
  have hbc (i : I) : ∃ k, c k = b i := by
    let y : H := ⟨b i, Or.inl ⟨i, rfl⟩⟩
    exact ⟨e.symm y, congrArg Subtype.val (e.apply_symm_apply y)⟩
  let F : Set Plane := ⋃ i, horizontalSegment (u i) (v i) (b i)
  have hcoord (j : Fin 2) : Continuous (fun z : Plane => z j) := by fun_prop
  have hF : MeasurableSet F := by
    apply MeasurableSet.iUnion
    intro i
    exact ((isClosed_le continuous_const (hcoord 0)).inter
      ((isClosed_le (hcoord 0) continuous_const).inter
        (isClosed_eq (hcoord 1) continuous_const))).measurableSet
  have hpt (t : ℝ) : Continuous (fun s => e2_sapPt s t) := by
    unfold e2_sapPt
    fun_prop
  let A : ℕ → Set ℝ := fun k => (fun s => e2_sapPt s (c k)) ⁻¹' F
  have hA (k : ℕ) : MeasurableSet (A k) := hF.preimage (hpt (c k)).measurable
  let B : ℕ → Set Plane := fun k => F ∩ {z | z 1 = c k}
  have hB (k : ℕ) : MeasurableSet (B k) :=
    hF.inter (isClosed_eq (hcoord 1) continuous_const).measurableSet
  have hBimage (k : ℕ) : B k = (fun s => e2_sapPt s (c k)) '' A k := by
    ext z
    constructor
    · rintro ⟨hz, ht⟩
      change z 1 = c k at ht
      have heq : e2_sapPt (z 0) (c k) = z := by
        ext j
        fin_cases j <;> simp [e2_sapPt, ht]
      exact ⟨z 0, by change e2_sapPt (z 0) (c k) ∈ F; rwa [heq], heq⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, by simp [e2_sapPt]⟩
  have hdisj : Pairwise (Disjoint on B) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hkl (hc (hz.2.symm.trans hz'.2))
  have hcover : F = ⋃ k, B k := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨k, hk⟩ := hbc i
      exact Set.mem_iUnion.mpr ⟨k, hz, hi.2.2.trans hk.symm⟩
    · intro z hz
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      exact hk.1
  refine ⟨c, A, hc, hA, ?_⟩
  change μH[1].restrict F = Measure.sum (fun k => (volume.restrict (A k)).map
    (fun s => e2_sapPt s (c k)))
  rw [hcover, Measure.restrict_iUnion hdisj hB]
  congr 1
  funext k
  rw [hBimage k]
  exact hL (c k) (A k) (hA k)

end ParabolicRectifiability.Examples
