import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # Assembly of `IsLacunaryData` for the lacunary frequency recursion

Proof of `E2LacunaryAssemblyStatement` (`e2_lacunaryState_assembly_proof`).
The one-step inequalities enter only as the hypothesis `E2LacunaryStepStatement`. -/

namespace ParabolicRectifiability.Examples

theorem e2_lacunaryState_assembly_proof : E2LacunaryAssemblyStatement := by
  intro hF a hpos hle
  have hsum : ∀ j, (e2_lacunaryState a j).2 =
      ∑ i ∈ Finset.range j, a i * Real.sqrt (e2_lacunaryFrequency a i : ℝ) := by
    intro j
    induction j with
    | zero => simp [e2_lacunaryState]
    | succ j ih => rw [Finset.sum_range_succ, ← ih]; rfl
  have hnn : ∀ j, 0 ≤ (e2_lacunaryState a j).2 := fun j => by
    rw [hsum]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hpos i).le (Real.sqrt_nonneg _)
  have hNpos : ∀ j, 0 < (e2_lacunaryState a j).1 := by
    intro j
    induction j with
    | zero => simp [e2_lacunaryState]
    | succ j ih => exact (hF a hpos j _ ih (hnn j)).1
  refine ⟨hpos, hle, hNpos, ?_, ?_, ?_⟩
  · intro j
    exact (hF a hpos j _ (hNpos j) (hnn j)).2.1
  · intro j
    cases j with
    | zero =>
      rw [Finset.sum_range_zero, mul_zero]
      exact div_nonneg (hpos 0).le (by norm_num)
    | succ j =>
      have h := (hF a hpos j _ (hNpos j) (hnn j)).2.2.1
      rw [← hsum (j + 1)]
      exact h
  · intro j
    exact (hF a hpos j _ (hNpos j) (hnn j)).2.2.2

end ParabolicRectifiability.Examples
