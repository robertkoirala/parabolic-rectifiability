import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.LastWitness

/-! # The last witness

This module proves `d1d_witnessSelection_proof : WitnessSelectionStatement`. The exported witness contract is
weaker than "last nonzero": the proof chooses the last nonzero index and a genuine occurrence of a
contributing pair, and exports only what the statement states.

Route.
* Every root term is `ofReal (planeComparison x r L_* L_*) = 0`, so `E_0(w) = 0`
  (`ENNReal.iSup_eq_zero`). The same holds for the level-zero same-level term.
* `S = (range (N + 1)).filter (E_j(w) ≠ 0)`. If `S` is empty, every `E_j(w)`, `j ≤ N`, vanishes.
  Otherwise its maximum `J` is positive (as `E_0(w) = 0`), `J = j₀ + 1`, and maximality gives the
  zeros on `(J, N]`.
* `E_{j₀+1} = max(same_{j₀}, adjacent_{j₀}) ≠ 0`. If the same-level supremum is nonzero, a
  nonzero term exists, so `j₀ ≥ 1` and its first member is an occurrence of level `j₀` within
  `12 r_{j₀}` of `w`. Otherwise the adjacent supremum is nonzero and its level-`(j₀+1)` member is
  the witness.

The plane-comparison identity `d1dwit_planeComparison_self` repeats the one-line proof of the base
`planeComparison_self`, which lies outside this
module's import closure; importing it would pull the whole source-construction chain.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Witness

section Helpers

variable {n m : ℕ} {ι : Type*} {W : Type*} [PseudoMetricSpace W]

/-- `d_{x,r}(L, L) = 0` (the base `planeComparison_self`). -/
theorem d1dwit_planeComparison_self (x : Spatial n) (r : ℝ) (L : AffineSpatialPlane n m) :
    planeComparison x r L L = 0 := by
  simp [planeComparison]

/-- The root comparison `E_0(w)` vanishes when the level-zero planes are the initial plane. -/
theorem d1dwit_root_zero (pos : Space n → W) (F : CoherentFamily n m ι) (w : W)
    (h0 : ∀ a ∈ F.index 0, F.plane 0 a = F.initialPlane) :
    F.comparisonEnergy pos 0 w = 0 := by
  change F.rootComparisonTerm pos w = 0
  unfold CoherentFamily.rootComparisonTerm
  refine ENNReal.iSup_eq_zero.2 fun a => ENNReal.iSup_eq_zero.2 fun ha =>
    ENNReal.iSup_eq_zero.2 fun _ => ?_
  rw [h0 a ha, d1dwit_planeComparison_self, ENNReal.ofReal_zero]

/-- The level-zero same-level comparison vanishes when the level-zero planes are the initial
plane. -/
theorem d1dwit_same_zero (pos : Space n → W) (F : CoherentFamily n m ι) (w : W)
    (h0 : ∀ a ∈ F.index 0, F.plane 0 a = F.initialPlane) :
    F.sameLevelComparisonTerm pos 0 w = 0 := by
  unfold CoherentFamily.sameLevelComparisonTerm
  refine ENNReal.iSup_eq_zero.2 fun a => ENNReal.iSup_eq_zero.2 fun ha =>
    ENNReal.iSup_eq_zero.2 fun b => ENNReal.iSup_eq_zero.2 fun hb =>
      ENNReal.iSup_eq_zero.2 fun _ => ?_
  rw [h0 a ha, h0 b hb, d1dwit_planeComparison_self, ENNReal.ofReal_zero]

/-- A nonzero same-level comparison at level `j` has a level-`j` occurrence within `12 r_j` of
`w` (the first member of a contributing pair). -/
theorem d1dwit_same_incident (pos : Space n → W) (F : CoherentFamily n m ι) (w : W) (j : ℕ)
    (hne : F.sameLevelComparisonTerm pos j w ≠ 0) :
    ∃ a ∈ F.index j, dist (pos (F.center j a)) w ≤ 12 * F.scale j := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  apply hne
  unfold CoherentFamily.sameLevelComparisonTerm
  refine ENNReal.iSup_eq_zero.2 fun a => ENNReal.iSup_eq_zero.2 fun ha =>
    ENNReal.iSup_eq_zero.2 fun b => ENNReal.iSup_eq_zero.2 fun _ =>
      ENNReal.iSup_eq_zero.2 fun hc => ?_
  exact absurd hc.2.1 (not_le.2 (hcon a ha))

/-- A nonzero adjacent comparison at scale `r_j` has a level-`(j+1)` occurrence within `12 r_j`
of `w` (the finer member of a contributing pair). -/
theorem d1dwit_adjacent_incident (pos : Space n → W) (F : CoherentFamily n m ι) (w : W) (j : ℕ)
    (hne : F.adjacentComparisonTerm pos j w ≠ 0) :
    ∃ a ∈ F.index (j + 1), dist (pos (F.center (j + 1) a)) w ≤ 12 * F.scale j := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  apply hne
  unfold CoherentFamily.adjacentComparisonTerm
  refine ENNReal.iSup_eq_zero.2 fun a => ENNReal.iSup_eq_zero.2 fun ha =>
    ENNReal.iSup_eq_zero.2 fun b => ENNReal.iSup_eq_zero.2 fun _ =>
      ENNReal.iSup_eq_zero.2 fun hc => ?_
  exact absurd hc.2.1 (not_le.2 (hcon a ha))

/-- A nonzero comparison `E_{j₀+1}(w)` has an occurrence `(i, a)`, `i ∈ {j₀, j₀ + 1}`, `i ≥ 1`,
within `12 r_{j₀}` of `w`. -/
theorem d1dwit_witness_of_ne_zero (pos : Space n → W) (F : CoherentFamily n m ι) (w : W)
    (h0 : ∀ a ∈ F.index 0, F.plane 0 a = F.initialPlane) (j₀ : ℕ)
    (hJ : F.comparisonEnergy pos (j₀ + 1) w ≠ 0) :
    ∃ (i : ℕ) (a : ι), 1 ≤ i ∧ j₀ ≤ i ∧ i ≤ j₀ + 1 ∧ a ∈ F.index i ∧
      dist (pos (F.center i a)) w ≤ 12 * F.scale j₀ := by
  change max (F.sameLevelComparisonTerm pos j₀ w) (F.adjacentComparisonTerm pos j₀ w) ≠ 0 at hJ
  by_cases hs : F.sameLevelComparisonTerm pos j₀ w = 0
  · rw [hs, max_eq_right zero_le] at hJ
    obtain ⟨a, ha, hd⟩ := d1dwit_adjacent_incident pos F w j₀ hJ
    exact ⟨j₀ + 1, a, Nat.le_add_left 1 j₀, Nat.le_succ j₀, le_rfl, ha, hd⟩
  · have hj₀ : j₀ ≠ 0 := by
      rintro rfl
      exact hs (d1dwit_same_zero pos F w h0)
    obtain ⟨a, ha, hd⟩ := d1dwit_same_incident pos F w j₀ hs
    exact ⟨j₀, a, Nat.one_le_iff_ne_zero.2 hj₀, le_rfl, Nat.le_succ j₀, ha, hd⟩

end Helpers

/-- **The last witness** (`WitnessSelectionStatement`): the proof selects
the last nonzero comparison index `J = j₀ + 1 ≤ N` and an occurrence of a contributing pair. -/
theorem d1d_witnessSelection_proof : WitnessSelectionStatement := by
  intro n m ι W _ pos F w N h0
  refine ⟨d1dwit_root_zero pos F w h0, ?_⟩
  classical
  by_cases hall : ∀ j ≤ N, F.comparisonEnergy pos j w = 0
  · exact Or.inl hall
  · right
    simp only [not_forall] at hall
    obtain ⟨j, hjN, hj⟩ := hall
    have hjS : j ∈ (Finset.range (N + 1)).filter (fun j => F.comparisonEnergy pos j w ≠ 0) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hjN), hj⟩
    obtain ⟨J, hJS, hmax⟩ :=
      Finset.exists_max_image ((Finset.range (N + 1)).filter
        (fun j => F.comparisonEnergy pos j w ≠ 0)) (fun j => j) ⟨j, hjS⟩
    obtain ⟨hJr, hJ⟩ := Finset.mem_filter.1 hJS
    have hJN : J < N + 1 := Finset.mem_range.1 hJr
    rcases J with _ | j₀
    · exact absurd (d1dwit_root_zero pos F w h0) hJ
    · refine ⟨j₀, by omega, ?_, d1dwit_witness_of_ne_zero pos F w h0 j₀ hJ⟩
      intro j' hj' hj'N
      by_contra hz
      have hmem : j' ∈ (Finset.range (N + 1)).filter
          (fun j => F.comparisonEnergy pos j w ≠ 0) :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hj'N), hz⟩
      have hle : j' ≤ j₀ + 1 := hmax j' hmem
      omega

end Witness

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
