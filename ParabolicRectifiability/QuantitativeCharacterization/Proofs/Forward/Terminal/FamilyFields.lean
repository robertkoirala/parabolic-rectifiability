import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The family fields needing no ADR (`d1c_familyFields`)

This module proves `d1c_familyFields_proof`, in implication form:

`StageFactsStatement → CoreEqualityStatement → FamilyFieldsStatement`.

Route. The eight fields of `Choice.FamilyFields` are read off the definitions of
`Choice.family`: the initial radius and plane are definitional (`rfl`); the artificial root
`rootCenter` has spatial part `π_{L_*} x_q ∈ L_*` in both branches; level `0` has the plane `L_*`;
the genuine occurrences at levels `j + 1` are the candidates `cand (j+1) i`, which are admissible
(`StageFacts.cand_admissible`), and their planes are those of the minimizing local fits
(`LocalFits.minimal`). Core limits: a centre of radius `0` is not a terminal centre
(`StageFacts.term_center` gives positive radii there), hence lies in `𝒞₀`, and
`CoreEqualityStatement` supplies candidates of levels tending to infinity converging to it.

Both statements enter only as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section FamilyHelpers

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The level-`j` index set of the coherent family. -/
theorem d1cfamily_index (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) :
    (C.family 𝒢 fits).index j = if j = 0 then {rootCenter 𝒢} else C.candSet j := rfl

/-- The family is indexed by physical points: every centre is its index. -/
theorem d1cfamily_center (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) (a : Space n) : (C.family 𝒢 fits).center j a = a := rfl

/-- The level-`j` plane of the coherent family. -/
theorem d1cfamily_plane (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) (a : Space n) :
    (C.family 𝒢 fits).plane j a =
      if j = 0 then rootPlane 𝒢 else NeckSelection.modelPlane 𝒢.type (fits.model j a) := rfl

/-- The family scales are the construction scales `r_j`. -/
theorem d1cfamily_scale (C : Choice n) (𝒢 : GoodRegion P μ k Λ b) (fits : LocalFits 𝒢)
    (j : ℕ) : (C.family 𝒢 fits).scale j = stageScale 𝒢 j := rfl

/-- Membership in a positive-level index set: exactly the candidates of that stage. -/
theorem d1cfamily_mem_index_succ (C : Choice n) (𝒢 : GoodRegion P μ k Λ b)
    (fits : LocalFits 𝒢) (j : ℕ) (a : Space n) :
    a ∈ (C.family 𝒢 fits).index (j + 1) ↔
      ∃ i, i < C.candCount (j + 1) ∧ C.cand (j + 1) i = a := by
  rw [d1cfamily_index, ite_eq_right (Nat.succ_ne_zero j)]
  simp only [Choice.candSet, Finset.mem_image, Finset.mem_range]

/-- The spatial part of the artificial root lies on the initial plane `L_*` (both branches). -/
theorem d1cfamily_rootCenter_mem (𝒢 : GoodRegion P μ k Λ b) :
    (rootCenter 𝒢).1 ∈ (rootPlane 𝒢).toSet := by
  unfold rootCenter
  split_ifs
  · exact (rootPlane 𝒢).projection_mem 𝒢.root.2.1
  · exact (rootPlane 𝒢).projection_mem 𝒢.root.2.1

end FamilyHelpers

/-- **The family fields needing
no ADR**, from the stage facts and the core equality (both as hypotheses). -/
theorem d1c_familyFields_proof :
    StageFactsStatement → CoreEqualityStatement → FamilyFieldsStatement := by
  intro hSF hCE n E ℓ₀ P μ k Λ b 𝒢 fits C hC
  have sf := hSF n E ℓ₀ P μ k Λ b 𝒢 C hC
  have ce := hCE n E ℓ₀ P μ k Λ b 𝒢 C hC
  refine
    { initialRadius_eq := rfl
      initialPoint_mem := d1cfamily_rootCenter_mem 𝒢
      core_limit := ?_
      level_zero_plane := ?_
      initialPlane_fit := rfl
      genuine_mem := ?_
      genuine_scale := ?_
      genuine_fit := ?_ }
  · -- core limits
    intro z hz hz0
    have hzc : z ∈ 𝒢.limitCore := by
      rcases (show z ∈ 𝒢.limitCore ∨ C.IsTermCenter z from hz) with hz | hz
      · exact hz
      · exact absurd hz0 (sf.term_center z hz).1.ne'
    obtain ⟨level, idx, hli, htend, hlim⟩ := ce.2 z hzc
    refine ⟨level, fun m => C.cand (level m) (idx m), fun m => ?_, htend, hlim⟩
    obtain ⟨hl1, hlt⟩ := hli m
    obtain ⟨l, hl⟩ : ∃ l, level m = l + 1 := ⟨level m - 1, by omega⟩
    show C.cand (level m) (idx m) ∈ (C.family 𝒢 fits).index (level m)
    rw [hl, d1cfamily_mem_index_succ]
    exact ⟨idx m, by rw [← hl]; exact hlt, rfl⟩
  · -- level zero carries the initial plane
    intro a _
    rw [d1cfamily_plane, ite_eq_left rfl]
    rfl
  · -- genuine occurrences lie in the root cell
    intro j a ha
    obtain ⟨i, hi, rfl⟩ := (d1cfamily_mem_index_succ C 𝒢 fits j a).1 ha
    exact (sf.cand_admissible (j + 1) (Nat.succ_pos j) i hi).1
  · -- genuine occurrences have admissible stopping scale
    intro j a ha
    obtain ⟨i, hi, rfl⟩ := (d1cfamily_mem_index_succ C 𝒢 fits j a).1 ha
    rw [d1cfamily_center, d1cfamily_scale]
    exact (sf.cand_admissible (j + 1) (Nat.succ_pos j) i hi).2
  · -- genuine planes are those of the minimizing original-source fits
    intro j a _
    refine ⟨fits.model (j + 1) a, ?_, fun M' => ?_⟩
    · rw [d1cfamily_plane, ite_eq_right (Nat.succ_ne_zero j)]
    · rw [d1cfamily_center, d1cfamily_scale]
      exact fits.minimal (j + 1) a M'

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
