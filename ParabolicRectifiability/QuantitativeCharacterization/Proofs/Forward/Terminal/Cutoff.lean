import ParabolicRectifiability.QuantitativeCharacterization.Statements.Forward.Terminal

/-! # The cutoff

Proof of `d1c_cutoff_proof`, with the statement `StopScaleLipschitzStatement` as hypothesis
(implication form; only its nonnegativity clause is used).

Route: unfold `stageCutoff`. If `ρ(z) > 0`, the set `{j ≥ 1 | r_j ≤ ρ(z)/100}` is nonempty
(`r_j → 0`), so its `sInf` `J` belongs to it (`Nat.sInf_mem`): `f = r_J ≤ ρ/100`. Minimality
(`Nat.notMem_of_lt_sInf`) gives `ρ/100 < r_{J-1} = 10 r_J` for `J ≥ 2`; for `J = 1`,
`10 r_1 = r_0 = 48 ℓ_*` and `ρ/100 ≤ ℓ_*/100 < 48 ℓ_*`. Without `ρ ≥ 0` the defining set could be
empty (then `f = r_0 > 0` and `100 f ≤ ρ` fails), which is why the premise is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ParabolicRectifiability.QuantitativeCharacterization

namespace Forward

namespace Terminal

section

variable {n : ℕ} {E : Set (Space n)} {ℓ₀ : ℝ} {P : DirectPartition E ℓ₀} {μ : Measure (Space n)}
  {k : ℕ} {Λ b : ℝ}

/-- The construction scales are positive. -/
theorem d1ccut_stageScale_pos (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) : 0 < stageScale 𝒢 j := by
  have h := d1c_rootScale_pos 𝒢
  unfold stageScale coherentScale
  positivity

/-- `r_0 = 48 ℓ_*`. -/
theorem d1ccut_stageScale_zero (𝒢 : GoodRegion P μ k Λ b) :
    stageScale 𝒢 0 = 48 * 𝒢.rootScale := by
  unfold stageScale coherentScale
  simp

/-- `r_j = 10 r_{j+1}`. -/
theorem d1ccut_stageScale_succ (𝒢 : GoodRegion P μ k Λ b) (j : ℕ) :
    stageScale 𝒢 j = 10 * stageScale 𝒢 (j + 1) := by
  unfold stageScale coherentScale
  have h : (10 : ℝ) ^ j ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- The construction scales become arbitrarily small at positive levels. -/
theorem d1ccut_stageScale_small (𝒢 : GoodRegion P μ k Λ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, 1 ≤ j ∧ stageScale 𝒢 j ≤ ε := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (48 * 𝒢.rootScale / ε) (by norm_num : (1 : ℝ) < 10)
  refine ⟨m + 1, by omega, ?_⟩
  have h10 : (0 : ℝ) < 10 ^ m := by positivity
  have hm' : stageScale 𝒢 m < ε := by
    unfold stageScale coherentScale
    rw [div_lt_iff₀ h10]
    rw [div_lt_iff₀ hε] at hm
    linarith [mul_comm ((10 : ℝ) ^ m) ε]
  have hs := d1ccut_stageScale_succ 𝒢 m
  have hp := d1ccut_stageScale_pos 𝒢 (m + 1)
  linarith

/-- The cutoff index: the least `j ≥ 1` with `r_j ≤ ρ / 100`. -/
def d1ccut_index (𝒢 : GoodRegion P μ k Λ b) (ρ : ℝ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ stageScale 𝒢 j ≤ ρ / 100}

/-- For `ρ > 0` the cutoff index exists, `r_J ≤ ρ / 100`, and `ρ / 100 < r_{J-1}` when `J ≥ 2`. -/
theorem d1ccut_index_spec (𝒢 : GoodRegion P μ k Λ b) {ρ : ℝ} (hρ : 0 < ρ) :
    1 ≤ d1ccut_index 𝒢 ρ ∧ stageScale 𝒢 (d1ccut_index 𝒢 ρ) ≤ ρ / 100 ∧
      (2 ≤ d1ccut_index 𝒢 ρ → ρ / 100 < stageScale 𝒢 (d1ccut_index 𝒢 ρ - 1)) := by
  have hne : {j : ℕ | 1 ≤ j ∧ stageScale 𝒢 j ≤ ρ / 100}.Nonempty := by
    obtain ⟨j, hj1, hj⟩ := d1ccut_stageScale_small 𝒢 (div_pos hρ (by norm_num : (0 : ℝ) < 100))
    exact ⟨j, hj1, hj⟩
  have hmem : d1ccut_index 𝒢 ρ ∈ {j : ℕ | 1 ≤ j ∧ stageScale 𝒢 j ≤ ρ / 100} := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun h2 => ?_⟩
  have hlt : d1ccut_index 𝒢 ρ - 1 < sInf {j : ℕ | 1 ≤ j ∧ stageScale 𝒢 j ≤ ρ / 100} := by
    show d1ccut_index 𝒢 ρ - 1 < d1ccut_index 𝒢 ρ
    omega
  have hnot := Nat.notMem_of_lt_sInf hlt
  simp only [Set.mem_ofPred_eq, not_and, not_le] at hnot
  exact hnot (by omega)

/-- For `ρ(z) ≠ 0` the cutoff is the scale of the cutoff index. -/
theorem d1ccut_cutoff_eq (𝒢 : GoodRegion P μ k Λ b) {z : Space n} (hz : 𝒢.stopScale z ≠ 0) :
    stageCutoff 𝒢 z = stageScale 𝒢 (d1ccut_index 𝒢 (𝒢.stopScale z)) := by
  unfold stageCutoff
  rw [ite_eq_right hz]
  rfl

/-- `ρ(z) = 0` gives `f(z) = 0`. -/
theorem d1ccut_cutoff_zero (𝒢 : GoodRegion P μ k Λ b) {z : Space n} (hz : 𝒢.stopScale z = 0) :
    stageCutoff 𝒢 z = 0 := by
  unfold stageCutoff
  rw [ite_eq_left hz]

end

/-- **The cutoff** (`d1c_cutoff`). -/
theorem d1c_cutoff_proof : StopScaleLipschitzStatement → CutoffStatement := by
  intro hLip n E ℓ₀ P μ k Λ b 𝒢
  have hnonneg := (hLip n E ℓ₀ P μ k Λ b 𝒢).1
  refine ⟨fun z => ?_, fun z hz => d1ccut_cutoff_zero 𝒢 hz, fun z => ?_, fun z hpos hle => ?_⟩
  · by_cases hz : 𝒢.stopScale z = 0
    · rw [d1ccut_cutoff_zero 𝒢 hz, hz]
      norm_num
    · have hpos : 0 < 𝒢.stopScale z := lt_of_le_of_ne (hnonneg z) (Ne.symm hz)
      obtain ⟨-, h2, -⟩ := d1ccut_index_spec 𝒢 hpos
      rw [d1ccut_cutoff_eq 𝒢 hz]
      refine ⟨(d1ccut_stageScale_pos 𝒢 _).le, ?_⟩
      linarith
  · by_cases hz : 𝒢.stopScale z = 0
    · exact Or.inl (d1ccut_cutoff_zero 𝒢 hz)
    · exact Or.inr ⟨_, d1ccut_cutoff_eq 𝒢 hz⟩
  · have hz : 𝒢.stopScale z ≠ 0 := ne_of_gt hpos
    obtain ⟨h1, h2, h3⟩ := d1ccut_index_spec 𝒢 hpos
    refine ⟨d1ccut_index 𝒢 (𝒢.stopScale z), h1, d1ccut_cutoff_eq 𝒢 hz, h2, ?_⟩
    by_cases hJ : 2 ≤ d1ccut_index 𝒢 (𝒢.stopScale z)
    · have hlt := h3 hJ
      have hs := d1ccut_stageScale_succ 𝒢 (d1ccut_index 𝒢 (𝒢.stopScale z) - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ d1ccut_index 𝒢 (𝒢.stopScale z))] at hs
      linarith
    · have hJ1 : d1ccut_index 𝒢 (𝒢.stopScale z) = 1 := by omega
      rw [hJ1]
      have hs := d1ccut_stageScale_succ 𝒢 0
      have h0 := d1ccut_stageScale_zero 𝒢
      have hr := d1c_rootScale_pos 𝒢
      linarith

end Terminal

end Forward

end ParabolicRectifiability.QuantitativeCharacterization
