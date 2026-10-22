import ParabolicRectifiability.QuantitativeCharacterization.Statements.ApproximantComponents
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Approximants.MultiplicityBasics
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceBasic

/-! # The typed split and the measure identity

Proof of `dp2_typed_split : dp2_TypedSplitStatement`.

Write `P₀ = P(a,R)`, `Γ_i` for the reference carriers, `P_i` for the model balls and
`trace_T = ⋃_{kind i = T} P_i ∩ Γ_i` (`RegularMixedCovering.typedTrace`).

1. Every carrier is closed (`ba1_horizontal_basic_proof`, `ba1_vertical_basic_proof`, `univ`), the
   model balls are open, so each `trace_T` is a countable union of Borel sets, hence Borel
   (`dp2_ts_measurableSet_typedTrace`).
2. Every reference is horizontal or vertical (the ambient reference is vertical), so the union of
   all `P_i ∩ Γ_i` is `trace_H ∪ trace_V` (`dp2_ts_union_traces`).
3. `F_H = P₀ ∩ trace_H`, `F_V = (P₀ ∩ trace_V) \ trace_H`. These are Borel, disjoint, inside the
   root and inside the traces of their types. `P₀ \ (F_H ∪ F_V)` is inside `P₀ \ ⋃_i P_i ∩ Γ_i`
   (null by hypothesis).
4. Identity: for every `N`, `P₀ = (P₀ ∩ {m ≤ N}) ∪ (P₀ ∩ {m > N})`, and `P₀ ∩ {m ≤ N}` is
   `μ`-a.e. equal to `(F_H ∩ {m ≤ N}) ∪ (F_V ∩ {m ≤ N})`. All pieces are Borel and the unions
   disjoint, so `Measure.restrict_union` and `Measure.restrict_congr_set` give the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- Every reference carrier is closed. -/
theorem dp2_ts_isClosed_carrier {n k : ℕ} {L : ℝ} (hL : 1 ≤ L) (ρ : Reference n k L) :
    IsClosed ρ.carrier := by
  cases ρ with
  | horizontal H => exact (ba1_horizontal_basic_proof n k L hL H).2.1
  | vertical V => exact (ba1_vertical_basic_proof n k L hL V).2.1
  | ambient _ => exact isClosed_univ

/-- Every reference is horizontal or vertical (the ambient reference is vertical). -/
theorem dp2_ts_kind_cases {n k : ℕ} {L : ℝ} (ρ : Reference n k L) :
    ρ.kind = .horizontal ∨ ρ.kind = .vertical := by
  cases ρ <;> simp [Reference.kind]

variable {n k : ℕ} {K L : ℝ} {μ : Measure (Space n)} {a : Space n} {R : ℝ}

/-- The typed traces are Borel: a countable union of open balls meeting closed carriers. -/
theorem dp2_ts_measurableSet_typedTrace (hL : 1 ≤ L) (𝒞 : RegularMixedCovering k K L μ a R)
    (T : FamilyKind) : MeasurableSet (𝒞.typedTrace T) := by
  unfold RegularMixedCovering.typedTrace
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => ?_
  exact (dp2_measurableSet_ball 𝒞 i).inter (dp2_ts_isClosed_carrier hL _).measurableSet

/-- The union of all traces `P_i ∩ Γ_i` lies in the union of the two typed traces. -/
theorem dp2_ts_union_traces (𝒞 : RegularMixedCovering k K L μ a R) :
    (⋃ i, 𝒞.ball i ∩ (𝒞.reference i).carrier) ⊆
      𝒞.typedTrace .horizontal ∪ 𝒞.typedTrace .vertical := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  rcases dp2_ts_kind_cases (𝒞.reference i) with h | h
  · exact Or.inl (mem_iUnion₂.2 ⟨i, h, hi⟩)
  · exact Or.inr (mem_iUnion₂.2 ⟨i, h, hi⟩)

/-- **`dp2_typed_split`**: the typed split and the measure identity. -/
theorem dp2_typed_split_proof : dp2_TypedSplitStatement := by
  intro n k K L hL μ a R 𝒞 hnull
  set P₀ : Set (Space n) := Metric.ball a R with hP₀
  set TH := 𝒞.typedTrace .horizontal with hTH
  set TV := 𝒞.typedTrace .vertical with hTV
  have hmP : MeasurableSet P₀ := Metric.isOpen_ball.measurableSet
  have hmH : MeasurableSet TH := dp2_ts_measurableSet_typedTrace hL 𝒞 _
  have hmV : MeasurableSet TV := dp2_ts_measurableSet_typedTrace hL 𝒞 _
  have hmFH : MeasurableSet (P₀ ∩ TH) := hmP.inter hmH
  have hmFV : MeasurableSet ((P₀ ∩ TV) \ TH) := (hmP.inter hmV).diff hmH
  -- the remainder is null
  have hrem : μ (P₀ \ ((P₀ ∩ TH) ∪ ((P₀ ∩ TV) \ TH))) = 0 := by
    refine measure_mono_null (fun z hz => ?_) hnull
    refine ⟨hz.1, fun hzU => hz.2 ?_⟩
    have hzT := dp2_ts_union_traces 𝒞 hzU
    by_cases h : z ∈ TH
    · exact Or.inl ⟨hz.1, h⟩
    · exact Or.inr ⟨⟨hz.1, hzT.resolve_left h⟩, h⟩
  refine ⟨P₀ ∩ TH, (P₀ ∩ TV) \ TH, ?_, ?_⟩
  · exact
      { measurable_horizontal := hmFH
        measurable_vertical := hmFV
        disjoint := Set.disjoint_left.2 fun z hz hz' => hz'.2 hz.2
        horizontal_subset_root := inter_subset_left
        vertical_subset_root := sdiff_subset.trans inter_subset_left
        horizontal_subset_trace := inter_subset_right
        vertical_subset_trace := sdiff_subset.trans inter_subset_right
        null_remainder := hrem }
  · intro N
    unfold RegularMixedCovering.approximant RegularMixedCovering.residual
    set Le : Set (Space n) := {z | 𝒞.multiplicity z ≤ (N : ℕ∞)} with hLe
    set Gt : Set (Space n) := {z | (N : ℕ∞) < 𝒞.multiplicity z} with hGt
    have hmLe : MeasurableSet Le := dp2_measurableSet_multiplicity_le 𝒞 N
    have hmGt : MeasurableSet Gt := dp2_measurableSet_lt_multiplicity 𝒞 N
    -- `P₀` is a.e. equal to `F_H ∪ F_V`
    have hae : P₀ =ᵐ[μ] ((P₀ ∩ TH) ∪ ((P₀ ∩ TV) \ TH)) := by
      refine ae_eq_set.2 ⟨hrem, ?_⟩
      refine measure_mono_null (fun z hz => ?_) (measure_empty (μ := μ))
      exact absurd (hz.1.elim (fun h => h.1) (fun h => h.1.1)) hz.2
    have hsplit : P₀ = (P₀ ∩ Le) ∪ (P₀ ∩ Gt) := by
      ext z
      simp only [mem_union, mem_inter_iff, hLe, hGt, mem_ofPred_eq]
      constructor
      · intro hz
        rcases le_or_gt (𝒞.multiplicity z) N with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
      · rintro (h | h) <;> exact h.1
    have hdisjPG : Disjoint (P₀ ∩ Le) (P₀ ∩ Gt) :=
      Set.disjoint_left.2 fun z hz hz' => (not_lt.2 (show 𝒞.multiplicity z ≤ (N : ℕ∞) from hz.2))
        (show (N : ℕ∞) < 𝒞.multiplicity z from hz'.2)
    have hae2 : P₀ ∩ Le =ᵐ[μ] (((P₀ ∩ TH) ∩ Le) ∪ (((P₀ ∩ TV) \ TH) ∩ Le)) := by
      have h : (P₀ ∩ Le : Set (Space n)) =ᵐ[μ]
          (((P₀ ∩ TH) ∪ ((P₀ ∩ TV) \ TH)) ∩ Le : Set (Space n)) :=
        hae.inter (Filter.EventuallyEq.refl (ae μ) Le)
      rwa [union_inter_distrib_right] at h
    have hdisjFHV : Disjoint ((P₀ ∩ TH) ∩ Le) (((P₀ ∩ TV) \ TH) ∩ Le) :=
      Set.disjoint_left.2 fun z hz hz' => hz'.1.2 hz.1.2
    calc μ.restrict P₀ = μ.restrict ((P₀ ∩ Le) ∪ (P₀ ∩ Gt)) := by rw [← hsplit]
      _ = μ.restrict (P₀ ∩ Le) + μ.restrict (P₀ ∩ Gt) :=
          Measure.restrict_union hdisjPG (hmP.inter hmGt)
      _ = μ.restrict (((P₀ ∩ TH) ∩ Le) ∪ (((P₀ ∩ TV) \ TH) ∩ Le)) + μ.restrict (P₀ ∩ Gt) := by
          rw [Measure.restrict_congr_set hae2]
      _ = (μ.restrict ((P₀ ∩ TH) ∩ Le) + μ.restrict (((P₀ ∩ TV) \ TH) ∩ Le)) +
            μ.restrict (P₀ ∩ Gt) := by
          rw [Measure.restrict_union hdisjFHV (hmFV.inter hmLe)]

end ParabolicRectifiability.QuantitativeCharacterization
