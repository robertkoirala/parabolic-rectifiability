import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Stopping
import ParabolicRectifiability.Measure.Neck.FirstSwitch

/-! # The mixed coefficient is attained by an available type (`d1b_mixedAttainment`)

Proof of `ExactModelStatement → MixedAttainmentStatement`. The base `typeFittingError_mixed_eq` splits the mixed infimum as
`I_T ⊓ I_{T.other}`; the infimum of an unavailable family is `⊤`; an available `T` with
`I_T ≤ I_{T.other}` exists; its exact optimizer (hypothesis `ExactModelStatement`) has fit at most
`I_T`, hence at most that of every mixed model. The proof of `ExactModelStatement` is not used.
Helper prefix `d1bmixed_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Stopping

/-- The fitting infimum of an unavailable family is `⊤`. -/
theorem d1bmixed_typeFittingError_eq_top {n k : ℕ} (μ : Measure (Space n)) (T : NeckType)
    (h : ¬ T.Available n k) (z : Space n) (r : ℝ) :
    typeFittingError μ k T.toFamilyKind z r = ⊤ := by
  have hE : IsEmpty (Models n k T.toFamilyKind) := by
    cases T with
    | horizontal => exact HorizontalModel.isEmpty_of_not_available h
    | vertical => exact VerticalModel.isEmpty_of_not_available h
  unfold typeFittingError
  exact iInf_of_empty _

/-- Some available type has fitting infimum at most that of the other type. -/
theorem d1bmixed_exists_available_le {n : ℕ} (k : ℕ) (hn : 1 ≤ n) (hk1 : 1 ≤ k)
    (hk2 : k < n + 2) (μ : Measure (Space n)) (z : Space n) (r : ℝ) :
    ∃ T : NeckType, T.Available n k ∧
      typeFittingError μ k T.toFamilyKind z r ≤
        typeFittingError μ k T.other.toFamilyKind z r := by
  by_cases hH : NeckType.Available n k NeckType.horizontal
  · by_cases hV : NeckType.Available n k NeckType.vertical
    · rcases le_total (typeFittingError μ k NeckType.horizontal.toFamilyKind z r)
        (typeFittingError μ k NeckType.vertical.toFamilyKind z r) with h | h
      · exact ⟨.horizontal, hH, h⟩
      · exact ⟨.vertical, hV, h⟩
    · refine ⟨.horizontal, hH, ?_⟩
      have := d1bmixed_typeFittingError_eq_top (k := k) μ .vertical hV z r
      show _ ≤ typeFittingError μ k NeckType.vertical.toFamilyKind z r
      rw [this]
      exact le_top
  · have hV : NeckType.Available n k NeckType.vertical := by
      have hH' : ¬ (1 ≤ k ∧ k ≤ n) := hH
      show 2 ≤ k ∧ k ≤ n + 2
      omega
    refine ⟨.vertical, hV, ?_⟩
    have := d1bmixed_typeFittingError_eq_top (k := k) μ .horizontal hH z r
    show _ ≤ typeFittingError μ k NeckType.horizontal.toFamilyKind z r
    rw [this]
    exact le_top

/-- **The mixed coefficient is attained by an available type** (`MixedAttainmentStatement`). -/
theorem d1b_mixedAttainment_proof : ExactModelStatement → MixedAttainmentStatement := by
  intro hE n hn k hk1 hk2 μ hμ z r
  obtain ⟨T, hT, hle⟩ := d1bmixed_exists_available_le k hn hk1 hk2 μ z r
  obtain ⟨L, hL⟩ := hE n k μ hμ T hT z r
  refine ⟨T, hT, L, fun L' => ?_⟩
  calc fit μ L z r ≤ typeFittingError μ k T.toFamilyKind z r := le_iInf hL
    _ = typeFittingError μ k T.toFamilyKind z r ⊓ typeFittingError μ k T.other.toFamilyKind z r :=
        (inf_eq_left.mpr hle).symm
    _ = typeFittingError μ k .mixed z r := (typeFittingError_mixed_eq μ T z r).symm
    _ ≤ fit μ L' z r := iInf_le (fun L => fit μ L z r) L'

end Stopping

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
