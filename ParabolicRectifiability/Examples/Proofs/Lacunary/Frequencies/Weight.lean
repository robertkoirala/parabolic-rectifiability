import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # Weighted geometric majorant and tails for the lacunary series -/

noncomputable section

open Filter Topology

namespace ParabolicRectifiability.Examples

theorem e2_lacunaryWeight_proof : E2LacunaryWeightStatement := by
  intro a N h
  have hpos : ∀ j, 0 < a j / Real.sqrt (N j) := fun j =>
    div_pos (h.amplitude_pos j)
      (Real.sqrt_pos.mpr (by exact_mod_cast h.frequency_pos j))
  have hdec : ∀ j, a (j + 1) / Real.sqrt (N (j + 1)) ≤ a j / Real.sqrt (N j) / 1000 := by
    intro j
    have := h.amplitude_decay j
    rwa [div_div, mul_comm (Real.sqrt _)]
  have hk : ∀ j k : ℕ, a (j + k) / Real.sqrt (N (j + k)) ≤
      a j / Real.sqrt (N j) * (1 / 1000) ^ k := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a (j + (k + 1)) / Real.sqrt (N (j + (k + 1)))
          = a ((j + k) + 1) / Real.sqrt (N ((j + k) + 1)) := rfl
        _ ≤ a (j + k) / Real.sqrt (N (j + k)) / 1000 := hdec _
        _ ≤ a j / Real.sqrt (N j) * (1 / 1000) ^ k / 1000 := by gcongr
        _ = a j / Real.sqrt (N j) * (1 / 1000) ^ (k + 1) := by ring
  have hgeo : ∀ c : ℝ, Summable (fun k : ℕ => c * (1 / 1000 : ℝ) ^ k) := fun c =>
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c
  have hbound : ∀ j, a j / Real.sqrt (N j) ≤ a 0 / Real.sqrt (N 0) * (1 / 1000) ^ j := by
    intro j
    simpa using hk 0 j
  have hsum : Summable (fun j => a j / Real.sqrt (N j)) :=
    Summable.of_nonneg_of_le (fun j => (hpos j).le) hbound (hgeo _)
  refine ⟨hpos, hdec, hbound, hsum, ?_⟩
  intro j
  have hle : ∀ i, a (j + 1 + i) / Real.sqrt (N (j + 1 + i)) ≤
      a j / Real.sqrt (N j) / 1000 * (1 / 1000) ^ i := by
    intro i
    have := hk j (i + 1)
    calc _ = a (j + (i + 1)) / Real.sqrt (N (j + (i + 1))) := by rw [add_assoc, add_comm 1 i]
      _ ≤ _ := this
      _ = _ := by ring
  have hs2 : Summable (fun i => a (j + 1 + i) / Real.sqrt (N (j + 1 + i))) :=
    (summable_nat_add_iff (j + 1)).mpr hsum |>.congr (fun i => by rw [add_comm i])
  calc ∑' i, a (j + 1 + i) / Real.sqrt (N (j + 1 + i))
      ≤ ∑' i : ℕ, a j / Real.sqrt (N j) / 1000 * (1 / 1000 : ℝ) ^ i :=
        hs2.tsum_le_tsum hle (hgeo _)
    _ = a j / Real.sqrt (N j) / 1000 * (1 - 1 / 1000)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = a j / Real.sqrt (N j) / 999 := by ring

end ParabolicRectifiability.Examples
