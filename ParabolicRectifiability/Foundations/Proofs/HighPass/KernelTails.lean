import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.DerivMoments

/-! # Rapid tails of the high-pass kernel

Proof of `fhpbc_b2_kernelTails`, in implication form over `FhpbcKernelBasicStatement` and
`FhpbcInverseHalfAsymptoticStatement`, which the type itself contains.

Route: for `|t| ≥ 1` (so `t ≠ 0`), the basic kernel facts give
`K^{(j)}(t) = I^{(j)}(t) - ∫ η^{(j)}(s) I(t-s) ds`; the asymptotic expansion with `ρ = η^{(j)}`
(the Schwartz map
`(derivCLM ℝ ℝ)^[j] η`) and order `N' = max N (j+1)` expands the convolution; the moments
`∫ s^k η^{(j)} = (-1)^j j! δ_{kj}` (`fhpbb2t_moment_iterate`, from `η̂ ≡ 1` near `0` by
`fhpbb2t_cutoff_moment`) collapse the expansion to `I^{(j)}(t)`, which cancels, leaving the
remainder `C |t|^{-N'} ≤ max C 0 · |t|^{-N}`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Nat Topology SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.FractionalKernel

/-- The moment sum of the asymptotic expansion for `ρ = η^{(j)}` collapses to its `k = j` term `I^{(j)}(t)`. -/
theorem fhpbb2t_sum_collapse (η : 𝓢(ℝ, ℝ))
    (h0 : ∀ k : ℕ, ∫ s : ℝ, s ^ k * η s = if k = 0 then 1 else 0) (j N : ℕ) (hj : j < N)
    (t : ℝ) :
    ∑ k ∈ Finset.range N,
        ((-1 : ℝ) ^ k / (k.factorial : ℝ) *
            ∫ s : ℝ, s ^ k * ((⇑(SchwartzMap.derivCLM ℝ ℝ))^[j] η) s) *
          iteratedDeriv k fhp_inverseHalfKernel t =
      iteratedDeriv j fhp_inverseHalfKernel t := by
  rw [Finset.sum_eq_single j]
  · rw [fhpbb2t_moment_iterate η h0 j j, ite_eq_left rfl]
    have hf : (j.factorial : ℝ) ≠ 0 := by positivity
    have hone : (-1 : ℝ) ^ j / (j.factorial : ℝ) * ((-1 : ℝ) ^ j * (j.factorial : ℝ)) = 1 := by
      calc (-1 : ℝ) ^ j / (j.factorial : ℝ) * ((-1 : ℝ) ^ j * (j.factorial : ℝ))
          = ((-1 : ℝ) ^ j * (-1) ^ j) * ((j.factorial : ℝ) / (j.factorial : ℝ)) := by ring
        _ = 1 := by rw [← mul_pow, div_self hf]; norm_num
    rw [hone, one_mul]
  · intro k _ hk
    rw [fhpbb2t_moment_iterate η h0 j k, ite_eq_right hk, mul_zero, zero_mul]
  · intro hjN
    exact absurd (Finset.mem_range.mpr hj) hjN

/-- **Rapid tails** (`fhpbc_b2_kernelTails`): rapid tails of `K = I - η * I` and all
its derivatives, `|K^{(j)}(t)| ≤ C |t|^{-N}` for `|t| ≥ 1`, from the basic kernel facts and the asymptotic expansion. -/
theorem fhpbc_b2_kernelTails_proof :
    FhpbcKernelBasicStatement → FhpbcInverseHalfAsymptoticStatement →
      FhpbcKernelTailsStatement := by
  intro hB hA η hη j N
  obtain ⟨-, -, -, hη1⟩ := id hη
  have h0 := fhpbb2t_cutoff_moment η hη1
  have hcoe : ⇑((⇑(SchwartzMap.derivCLM ℝ ℝ))^[j] η) = iteratedDeriv j ⇑η :=
    fhpbb2b_coe_iterate j η
  obtain ⟨C, hC⟩ := hA ((⇑(SchwartzMap.derivCLM ℝ ℝ))^[j] η) (max N (j + 1))
  refine ⟨max C 0, fun t ht => ?_⟩
  have ht0 : t ≠ 0 := abs_pos.mp (by linarith)
  have hK := (hB η hη).2.2.2 j t ht0
  rw [← hcoe] at hK
  have h1 := hC t ht
  rw [fhpbb2t_sum_collapse η h0 j (max N (j + 1))
    (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)) t] at h1
  have hexp : |t| ^ (-((max N (j + 1) : ℕ) : ℝ)) ≤ |t| ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht
      (neg_le_neg (Nat.cast_le.mpr (le_max_left _ _)))
  calc |iteratedDeriv j (fhp_highPassKernel η) t|
      = |(∫ s : ℝ, ((⇑(SchwartzMap.derivCLM ℝ ℝ))^[j] η) s * fhp_inverseHalfKernel (t - s)) -
          iteratedDeriv j fhp_inverseHalfKernel t| := by
        rw [hK, abs_sub_comm]
    _ ≤ C * |t| ^ (-((max N (j + 1) : ℕ) : ℝ)) := h1
    _ ≤ max C 0 * |t| ^ (-((max N (j + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg t) _)
    _ ≤ max C 0 * |t| ^ (-(N : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp (le_max_right _ _)

end ParabolicRectifiability.Foundations
