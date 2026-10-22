import ParabolicRectifiability.Examples.Proofs.Lacunary.FrequencyStatements

/-! # Weierstrass M-test for the lacunary cosine series -/

namespace ParabolicRectifiability.Examples

open Filter

/-- Proof of `E2LacunaryWeierstrassStatement`. -/
theorem e2_lacunary_weierstrass_proof : E2LacunaryWeierstrassStatement := by
  intro ε a N hnn hsum
  have hbd : ∀ j (t : ℝ),
      |a j / Real.sqrt (N j) * Real.cos (N j * t)| ≤ a j / Real.sqrt (N j) := by
    intro j t
    rw [abs_mul, abs_of_nonneg (hnn j)]
    exact mul_le_of_le_one_right (hnn j) (Real.abs_cos_le_one _)
  refine ⟨fun t => Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => hbd j t) hsum, ?_⟩
  have hu : Summable (fun j => |ε| * (a j / Real.sqrt (N j))) := hsum.mul_left _
  have h := tendstoUniformly_tsum_nat
    (f := fun (j : ℕ) (t : ℝ) => ε * (a j / Real.sqrt (N j) * Real.cos (N j * t)))
    hu (by
      intro j t
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hbd j t) (abs_nonneg _))
  have e1 : (fun (M : ℕ) (t : ℝ) =>
      ε * ∑ j ∈ Finset.range M, a j / Real.sqrt (N j) * Real.cos (N j * t)) =
      fun (M : ℕ) (t : ℝ) =>
        ∑ j ∈ Finset.range M, ε * (a j / Real.sqrt (N j) * Real.cos (N j * t)) := by
    funext M t; rw [Finset.mul_sum]
  have e2 : lacunaryFunction ε a N =
      fun t => ∑' j, ε * (a j / Real.sqrt (N j) * Real.cos (N j * t)) := by
    funext t; unfold lacunaryFunction; rw [tsum_mul_left]
  rw [e1, e2]
  exact h

end ParabolicRectifiability.Examples
