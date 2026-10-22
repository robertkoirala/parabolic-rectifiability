import ParabolicRectifiability.QuantitativeCharacterization.Statements.PiecesComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceBasic

/-! # The countable-pieces assembly

Proof of `dp2_pieces_assembly` in implication form over the horizontal references, vertical
references, disjoint restrictions and one-reference certificate, with conclusion
`dp2_CountablePiecesStatement`.

* `dp2_pa_nat_family`: a countable family of sets listed as a sequence with empty padding (the
  convention of `Characterization.exists_nat_family`, restated here from mathlib's
  `exists_surjective_nat` so that the closure stays small).
* `dp2_pa_isClosed_carrier`: every `L`-reference carrier, `L ≥ 1`, is closed
  (`ba1_horizontal_basic_proof`, `ba1_vertical_basic_proof`, `univ`).
* `dp2_pa_of_reference_family`: the common core. A countable family of Borel masks `m x`, with
  references `r x`, whose traces `m x ∩ Γ(r x)` carry `μ`, gives the conclusion: enumerate, apply
  the disjoint restrictions, then for a nonzero piece `μ⌊E_j` with `E_j ⊆ m x ∩ Γ(r x)` first establish the concentration
  `(μ⌊E_j)(Γᶜ) = 0`, then deduce `supp (μ⌊E_j) ⊆ Γ` from closedness
  (`Measure.support_subset_of_isClosed`), then apply the one-reference certificate at `L_* = max 2 √(1+n)`.
* Ambient case `k = n + 2`: one mask `univ` with `Reference.ambient`.
* Nonambient case: masks `EH ∩ Γ_{i,ℓ}` (references of the horizontal graphs) and
  `EV ∩ Γ_j` (references of the vertical graphs); `dp2_pa_nonambient_carry` shows they carry `μ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- A countable family of sets listed as a sequence, padding with empty sets. -/
theorem dp2_pa_nat_family {ι X : Type*} [Countable ι] (s : ι → Set X) :
    ∃ B : ℕ → Set X, (∀ j, B j = ∅ ∨ ∃ x, B j = s x) ∧ (⋃ x, s x) ⊆ ⋃ j, B j := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (Option ι)
  refine ⟨fun j => Option.elim (f j) ∅ s, fun j => ?_, fun z hz => ?_⟩
  · show Option.elim (f j) ∅ s = ∅ ∨ ∃ x, Option.elim (f j) ∅ s = s x
    cases f j with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl⟩
  · obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := hf (some x)
    refine mem_iUnion.mpr ⟨j, ?_⟩
    show z ∈ Option.elim (f j) ∅ s
    rw [hj]
    exact hx

/-- Every reference carrier is closed (`L ≥ 1`). -/
theorem dp2_pa_isClosed_carrier {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    ∀ ρ : Reference n k L, IsClosed ρ.carrier
  | .horizontal H => (ba1_horizontal_basic_proof n k L hL H).2.1
  | .vertical V => (ba1_vertical_basic_proof n k L hL V).2.1
  | .ambient _ => isClosed_univ

/-- `2 ≤ L_* = max 2 √(1+n)`. -/
theorem dp2_pa_two_le (n : ℕ) : (2 : ℝ) ≤ max 2 (Real.sqrt (1 + n)) := le_max_left _ _

/-- **Concentration, then support.** A restriction `μ⌊E` with `E` Borel and `E ⊆ Γ`, `Γ` closed,
is concentrated on `Γ`, hence has support in `Γ`. -/
theorem dp2_pa_support_subset {n : ℕ} (μ : Measure (Space n)) {E Γ : Set (Space n)}
    (hE : MeasurableSet E) (hΓ : IsClosed Γ) (hEΓ : E ⊆ Γ) : (μ.restrict E).support ⊆ Γ := by
  have hconc : μ.restrict E Γᶜ = 0 := by
    rw [Measure.restrict_apply' hE]
    exact measure_mono_null (fun z hz => (hz.1 (hEΓ hz.2)).elim) measure_empty
  exact Measure.support_subset_of_isClosed hΓ (mem_ae_iff.mpr hconc)

/-- **The common core.** If the Borel traces `m x ∩ Γ(r x)` of countably many `L_*`-references
carry `μ ≪ H_P^k`, then the disjoint restrictions and the one-reference certificate give the countable
quantitative pieces. -/
theorem dp2_pa_of_reference_family (hP4 : dp2_DisjointRestrictionStatement)
    (hP5 : dp2_OneReferenceCertificateStatement) {n k : ℕ} {ι : Type*} [Countable ι]
    (μ : Measure (Space n)) (hac : μ ≪ hausdorffP n k)
    (r : ι → Reference n k (max 2 (Real.sqrt (1 + n)))) (m : ι → Set (Space n))
    (hm : ∀ x, MeasurableSet (m x)) (hcarry : μ (⋃ x, m x ∩ (r x).carrier)ᶜ = 0) :
    ∃ E : ℕ → Set (Space n), (∀ j, MeasurableSet (E j)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      μ = Measure.sum (fun j => μ.restrict (E j)) ∧
      ∀ j, μ.restrict (E j) ≠ 0 →
        IsQuantitativelyMixedRectifiable k ((2 : ℝ) ^ k) (max 2 (Real.sqrt (1 + n)))
          (μ.restrict (E j)) := by
  have hL1 : (1 : ℝ) ≤ max 2 (Real.sqrt (1 + n)) := le_trans (by norm_num) (dp2_pa_two_le n)
  obtain ⟨B, hBform, hBcov⟩ := dp2_pa_nat_family (fun x => m x ∩ (r x).carrier)
  have hBm : ∀ j, MeasurableSet (B j) := fun j => by
    rcases hBform j with h | ⟨x, h⟩
    · rw [h]; exact MeasurableSet.empty
    · rw [h]; exact (hm x).inter (dp2_pa_isClosed_carrier hL1 (r x)).measurableSet
  have hB0 : μ (⋃ j, B j)ᶜ = 0 := measure_mono_null (compl_subset_compl.mpr hBcov) hcarry
  obtain ⟨E, hEm, hdisj, hEB, hsum⟩ := hP4 n μ B hBm hB0
  refine ⟨E, hEm, hdisj, hsum, fun j hne => ?_⟩
  rcases hBform j with h | ⟨x, h⟩
  · -- an empty padded entry gives the zero piece
    refine (hne ?_).elim
    have hE : E j = ∅ := subset_empty_iff.mp (by rw [← h]; exact hEB j)
    rw [hE, Measure.restrict_empty]
  · have hEB' : E j ⊆ m x ∩ (r x).carrier := by rw [← h]; exact hEB j
    have hEΓ : E j ⊆ (r x).carrier := fun z hz => (hEB' hz).2
    have hsupp := dp2_pa_support_subset μ (hEm j) (dp2_pa_isClosed_carrier hL1 (r x)) hEΓ
    have hacj : μ.restrict (E j) ≪ hausdorffP n k :=
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac
    exact hP5 n k _ (dp2_pa_two_le n) (r x) (μ.restrict (E j)) hacj hsupp

/-- **Nonambient carriage.** Horizontal graphs `H i` covered modulo `H_P^k` by the carriers of
`Hr i ℓ`, and vertical graphs `V j` with the carriers of `Vr j`: the traces `EH ∩ Γ_{i,ℓ}` and
`EV ∩ Γ_j` carry `μ`. Stated over the image and carrier sets only. -/
theorem dp2_pa_nonambient_carry {n k : ℕ} (μ : Measure (Space n)) (hac : μ ≪ hausdorffP n k)
    {EH EV : Set (Space n)} (hEH : MeasurableSet EH) (hEV : MeasurableSet EV)
    (hcompl : μ (EH ∪ EV)ᶜ = 0) {I J : Set ℕ} {K : I → Set ℕ}
    (GH : I → Set (Space n)) (ΓH : ∀ i, K i → Set (Space n))
    (GV : J → Set (Space n)) (ΓV : J → Set (Space n))
    (hHcov : μ.restrict EH (⋃ i, GH i)ᶜ = 0)
    (hHref : ∀ i, hausdorffP n k (GH i \ ⋃ ℓ, ΓH i ℓ) = 0)
    (hVcov : μ.restrict EV (⋃ j, GV j)ᶜ = 0) (hVref : ∀ j, ΓV j = GV j) :
    μ (⋃ x : (Σ i, K i) ⊕ J,
        Sum.elim (fun _ => EH) (fun _ => EV) x ∩
          Sum.elim (fun p : Σ i, K i => ΓH p.1 p.2) ΓV x)ᶜ = 0 := by
  rw [Measure.restrict_apply' hEH] at hHcov
  rw [Measure.restrict_apply' hEV] at hVcov
  have hrem : μ (⋃ i, (GH i \ ⋃ ℓ, ΓH i ℓ)) = 0 :=
    measure_iUnion_null fun i => hac (hHref i)
  refine measure_mono_null ?_
    (measure_union_null (measure_union_null (measure_union_null hcompl hHcov) hrem) hVcov)
  intro z hz
  by_contra hcon
  have hzE : z ∈ EH ∪ EV := not_not.mp fun h => hcon (Or.inl (Or.inl (Or.inl h)))
  rcases hzE with hzH | hzV
  · have hzG : z ∈ ⋃ i, GH i := not_not.mp fun h => hcon (Or.inl (Or.inl (Or.inr ⟨h, hzH⟩)))
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzG
    have hzΓ : z ∈ ⋃ ℓ, ΓH i ℓ :=
      not_not.mp fun h => hcon (Or.inl (Or.inr (mem_iUnion.mpr ⟨i, hi, h⟩)))
    obtain ⟨ℓ, hℓ⟩ := mem_iUnion.mp hzΓ
    exact hz (mem_iUnion.mpr ⟨Sum.inl ⟨i, ℓ⟩, hzH, hℓ⟩)
  · have hzG : z ∈ ⋃ j, GV j := not_not.mp fun h => hcon (Or.inr ⟨h, hzV⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzG
    exact hz (mem_iUnion.mpr ⟨Sum.inr j, hzV, (by rw [hVref j]; exact hj : z ∈ ΓV j)⟩)

/-- **The countable-pieces assembly**, in implication form over the four preceding statements: the type is
that of `dp2_pieces_assembly`. -/
theorem dp2_pieces_assembly_proof :
    dp2_HorizontalReferenceCoverStatement → dp2_VerticalReferenceStatement →
      dp2_DisjointRestrictionStatement → dp2_OneReferenceCertificateStatement →
        dp2_CountablePiecesStatement := by
  intro hP2 hP3 hP4 hP5 n _hn k hk hkn μ _hfin _hinner hac EH EV hEH hEV _hdisj hcompl hHcov
    hVcov
  rcases eq_or_lt_of_le hkn with hamb | hlt
  · -- ambient `k = n + 2`: one mask `univ` and `Reference.ambient`
    refine dp2_pa_of_reference_family hP4 hP5 μ hac (ι := Unit)
      (fun _ => Reference.ambient hamb) (fun _ => univ) (fun _ => MeasurableSet.univ) ?_
    exact measure_mono_null
      (fun z hz => (hz (mem_iUnion.mpr ⟨(), mem_univ z, mem_univ z⟩)).elim) measure_empty
  · -- nonambient: references of the horizontal graphs and of the vertical graphs
    obtain ⟨I, H, hH⟩ := hHcov
    obtain ⟨J, V, hV⟩ := hVcov
    choose K Hr hHr using fun i : I => hP2 n k hk (H i)
    choose Vr hVr using fun j : J => hP3 n k hlt (V j)
    let r : (Σ i, K i) ⊕ J → Reference n k (max 2 (Real.sqrt (1 + n))) :=
      Sum.elim (fun p => .horizontal (Hr p.1 p.2)) (fun j => .vertical (Vr j))
    let m : (Σ i, K i) ⊕ J → Set (Space n) := Sum.elim (fun _ => EH) (fun _ => EV)
    have hm : ∀ x, MeasurableSet (m x) := fun x => by
      cases x with
      | inl _ => exact hEH
      | inr _ => exact hEV
    refine dp2_pa_of_reference_family hP4 hP5 μ hac r m hm ?_
    have hcar : ∀ x, (r x).carrier =
        Sum.elim (fun p : Σ i, K i => (Hr p.1 p.2).carrier) (fun j => (Vr j).carrier) x :=
      fun x => by cases x <;> rfl
    simp only [hcar]
    exact dp2_pa_nonambient_carry μ hac hEH hEV hcompl (fun i => (H i).image)
      (fun i ℓ => (Hr i ℓ).carrier) (fun j => (V j).image) (fun j => (Vr j).carrier) hH hHr hV hVr

end ParabolicRectifiability.QuantitativeCharacterization
