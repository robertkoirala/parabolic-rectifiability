import ParabolicRectifiability.QuantitativeCharacterization.Statements.PiecesComponents
import ParabolicRectifiability.Characterization.Proofs.GraphSource.HorizontalCompactCover
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Plateau.Completion
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalCarrier

/-! # Horizontal references at `L_* = max 2 √(1+n)`

Proves `dp2_horizontal_reference_cover_proof`, with the implication type
`dp2_SharpChartStatement → dp2_HorizontalReferenceCoverStatement`.

Proof idea (it mirrors `Characterization.b2_horizontal_graph_reference`):
1. compact patches `Gc j` from `Characterization.b2_horizontal_compact_cover_proof`;
2. the sharp chart (hypothesis) for each patch, weakened to `L_*` (`dp2_hr_weaken`);
3. `b2_whitney_plateau_completion_proof` at `L_*`;
4. `Characterization.b2_horizontalReference_map_mem_carrier_proof` puts each trace point in
   `(H j).carrier`, so `(Gc j).image ⊆ (H j).carrier` and the remainder shrinks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-- The constant `L_* = max 2 √(1+n)` is at least `1`. -/
theorem dp2_hr_one_le (n : ℕ) : (1 : ℝ) ≤ max 2 (Real.sqrt (1 + n)) :=
  le_trans (by norm_num) (le_max_left _ _)

/-- The sharp chart constants `(1, √(1+n), 1)` weaken to `L_*`. -/
theorem dp2_hr_weaken {n k : ℕ} (F : Spatial k → Spatial n) (D : Set (Spatial k))
    (τ : Spatial k → ℝ)
    (hbil : ∀ u v : Spatial k, dist u v ≤ dist (F u) (F v) ∧
      dist (F u) (F v) ≤ Real.sqrt (1 + n) * dist u v)
    (htr : ∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ dist u v ^ 2) :
    (∀ u v : Spatial k, dist u v ≤ max 2 (Real.sqrt (1 + n)) * dist (F u) (F v) ∧
      dist (F u) (F v) ≤ max 2 (Real.sqrt (1 + n)) * dist u v) ∧
    (∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ max 2 (Real.sqrt (1 + n)) ^ 2 * dist u v ^ 2) := by
  have h1 := dp2_hr_one_le n
  refine ⟨fun u v => ⟨?_, ?_⟩, fun u hu v hv => ?_⟩
  · calc dist u v ≤ dist (F u) (F v) := (hbil u v).1
      _ = 1 * dist (F u) (F v) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 dist_nonneg
  · calc dist (F u) (F v) ≤ Real.sqrt (1 + n) * dist u v := (hbil u v).2
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  · have hsq : (1 : ℝ) ≤ max 2 (Real.sqrt (1 + n)) ^ 2 := one_le_pow₀ h1
    calc |τ u - τ v| ≤ dist u v ^ 2 := htr u hu v hv
      _ = 1 * dist u v ^ 2 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- **Horizontal references** (`dp2_horizontal_reference_cover`): given the
sharp chart, every slope-one horizontal graph is covered modulo `H_P^k` by the carriers of
countably many horizontal `L_*`-references. -/
theorem dp2_horizontal_reference_cover_proof :
    dp2_SharpChartStatement → dp2_HorizontalReferenceCoverStatement := by
  intro hP1 n k hk G
  obtain ⟨J, Gc, hGc, hnull⟩ := Characterization.b2_horizontal_compact_cover_proof n k 1 G
  have hkn : k ≤ n := by
    have h := Submodule.finrank_le G.direction
    rw [G.rank_eq, finrank_euclideanSpace_fin] at h
    exact h
  have hpatch : ∀ j : J, ∃ H : HorizontalReference n k (max 2 (Real.sqrt (1 + n))),
      (Gc j).image ⊆ H.carrier := by
    intro j
    obtain ⟨F, D, τ, hbil, htr, hDne, hDc, hsub⟩ := hP1 n k (Gc j)
    obtain ⟨hbil', htr'⟩ := dp2_hr_weaken F D τ hbil htr
    obtain ⟨H, hF, hD, hτ⟩ :=
      b2_whitney_plateau_completion_proof n k hk hkn _ F hbil' D (hDne (hGc j).1)
        (hDc (hGc j).2) τ htr'
    refine ⟨H, fun z hz => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hsub hz
    have huH : u ∈ H.domain := by rw [hD]; exact hu
    have hmem := Characterization.b2_horizontalReference_map_mem_carrier_proof n k _ H u huH
    have hmap : H.map u = point (F u) (τ u) := by
      show point (H.spatialMap u) (H.height u) = point (F u) (τ u)
      rw [hF, hτ u hu]
    rw [hmap] at hmem
    exact hmem
  choose H hH using hpatch
  refine ⟨J, H, measure_mono_null ?_ hnull⟩
  exact sdiff_subset_sdiff_right (iUnion_mono hH)

end ParabolicRectifiability.QuantitativeCharacterization
