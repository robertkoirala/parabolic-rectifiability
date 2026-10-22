import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Coverage

/-! # The slabs cover the tested pairs

Proof of `SlabCoverStatement`.

Every tested pair `(z,r)`, `z ∈ P(a,R) ∩ supp μ`, `0 < r < R`, lies in the exact slab
`(Q ∩ P(a,R)) × [ℓ_Q/10, ℓ_Q)` of a forest cell `Q`:
* the level `j` is the least `j` with `R/10^{j+1} ≤ r` (`Nat.find`); minimality gives
  `r < R/10^j` (for `j = 0` from `r < R`). At `r = ℓ_m`, `m ≥ 1`, this is level `m - 1`;
* the cell address is `(j, w)` with `w ∈ 𝒵_j` and `z ∈ cell j w` (`cell_cover`);
* the top ancestor `z₀ ∈ 𝒵_0` with `cell j w ⊆ cell 0 z₀` comes from iterating `parent`
  (`parent_mem`, `cell_subset_parent`); `z` witnesses `cell 0 z₀ ∩ P(a,R) ≠ ∅`.

No uniqueness is claimed (that is `SlabDisjointStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Coverage

open ParabolicRectifiability.Foundations

/-- **Level choice**: for `0 < r < R` there is a level `j` with `R/10^{j+1} ≤ r < R/10^j`
(the least `j` with `R/10^{j+1} ≤ r`). -/
theorem d1fscover_exists_level {R r : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ j : ℕ, R / 10 ^ (j + 1) ≤ r ∧ r < R / 10 ^ j := by
  classical
  have hR : 0 < R := hr.trans hrR
  have hex : ∃ j : ℕ, R / 10 ^ (j + 1) ≤ r := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R / r) (by norm_num : (1 : ℝ) < 10)
    refine ⟨N, ?_⟩
    have h10 : (0 : ℝ) < 10 ^ N := by positivity
    have h1 : R / 10 ^ N < r := by
      rw [div_lt_iff₀ hr] at hN
      rw [div_lt_iff₀ h10, mul_comm]
      exact hN
    have h2 : R / 10 ^ (N + 1) ≤ R / 10 ^ N :=
      div_le_div_of_nonneg_left hR.le h10
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (Nat.le_succ N))
    exact h2.trans h1.le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hj : Nat.find hex with _ | m
  · simpa using hrR
  · have hmin : ¬ R / 10 ^ (m + 1) ≤ r :=
      Nat.find_min hex (m := m) (by rw [hj]; exact Nat.lt_succ_self m)
    exact not_le.mp hmin

/-- **Top ancestor**: every level-`j` cell lies in a level-`0` cell (iterate `parent`). -/
theorem d1fscover_top_ancestor {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ}
    (P : DirectPartition E ℓ₀) :
    ∀ (j : ℕ) (w : Space n), w ∈ P.center j → ∃ z₀ ∈ P.center 0, P.cell j w ⊆ P.cell 0 z₀ := by
  intro j
  induction j with
  | zero => exact fun w hw => ⟨w, hw, subset_rfl⟩
  | succ j ih =>
    intro w hw
    obtain ⟨z₀, hz₀, hsub⟩ := ih (P.parent j w) (P.parent_mem j w hw)
    exact ⟨z₀, hz₀, (P.cell_subset_parent j w hw).trans hsub⟩

/-- The side `ℓ_j = ℓ₀/10^j` and `ℓ_j/10 = ℓ₀/10^{j+1}`. -/
theorem d1fscover_scale {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} (P : DirectPartition E ℓ₀)
    (j : ℕ) : P.scale j = ℓ₀ / 10 ^ j ∧ P.scale j / 10 = ℓ₀ / 10 ^ (j + 1) := by
  refine ⟨rfl, ?_⟩
  show ℓ₀ / 10 ^ j / 10 = ℓ₀ / 10 ^ (j + 1)
  rw [pow_succ, div_div]

/-- **Slab cover**: every tested pair lies in the slab of a forest cell. -/
theorem d1f_slabCover_proof : SlabCoverStatement := by
  intro n μ a R P p hp
  simp only [rootPairs, Set.mem_prod, Set.mem_inter_iff, Set.mem_Ioo] at hp
  obtain ⟨⟨hza, hzE⟩, hr0, hrR⟩ := hp
  obtain ⟨j, hj1, hj2⟩ := d1fscover_exists_level hr0 hrR
  have hz : p.1 ∈ ⋃ w ∈ P.center j, P.cell j w := by
    rw [P.cell_cover j]
    exact hzE
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨z₀, hz₀, hsub⟩ := d1fscover_top_ancestor P j w hw
  obtain ⟨hs1, hs2⟩ := d1fscover_scale P j
  have hF : P.InForest a R (j, w) := by
    unfold DirectPartition.InForest DirectPartition.IsBelow
    exact ⟨z₀, hz₀, ⟨p.1, hsub hzw, hza⟩, hw, Nat.zero_le j, hsub⟩
  have hS : p ∈ slab P a R (j, w) := by
    show p.1 ∈ P.cell j w ∩ Metric.ball a R ∧ p.2 ∈ Ico (P.scale j / 10) (P.scale j)
    refine ⟨Set.mem_inter hzw hza, Set.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · rw [hs2]
      exact hj1
    · rw [hs1]
      exact hj2
  exact ⟨(j, w), hF, hS⟩

end Coverage

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
