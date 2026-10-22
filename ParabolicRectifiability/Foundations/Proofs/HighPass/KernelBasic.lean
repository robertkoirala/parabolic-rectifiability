import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.InverseHalfConvolution

/-! # Basic facts on the high-pass kernel

Proof of `fhpbc_b2_kernelBasic : FhpbcKernelBasicStatement`. The one-dimensional analysis is in
the `FractionalKernel` lemmas used below (`fhpbb2b_*`).

For an admissible cutoff `η` and `K = I - η * I`, `I(t) = |t|^{-1/2}` (value `0` at `0`):
* evenness: `η(-s) = η(s)`, `|-t| = |t|` and the reflection `s ↦ -s` (`integral_neg_eq_self`);
* `K` is smooth on `{0}ᶜ`: `I` is smooth there and `η * I` is smooth everywhere
  (`fhpbb2b_contDiff`, derivatives moved onto `η`);
* near zero: `η * I` is continuous, hence bounded by some `M` on `[-1, 1]`, and
  `|K t| ≤ |t|^{-1/2} + M ≤ (1 + |M|) (1 + |t|^{-1/2})`;
* for `t ≠ 0`: `K^{(j)}(t) = I^{(j)}(t) - ∫ η^{(j)}(s) I(t - s) ds` (`fhpbb2b_iteratedDeriv_sub`).
Only the evenness clause of `fhp_IsFrequencyCutoff` is used.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.FractionalKernel

/-- `K = I - η * I` in explicit form. -/
theorem fhpbb2b_highPassKernel_eq (η : ℝ → ℝ) :
    fhp_highPassKernel η = fun x : ℝ =>
      |x| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |x - s| ^ (-(1 / 2 : ℝ)) := rfl

/-- **Basic kernel facts** (`fhpbc_b2_kernelBasic`). -/
theorem fhpbc_b2_kernelBasic_proof : FhpbcKernelBasicStatement := by
  intro η hη
  refine ⟨fun t => ?_, ?_, ?_, fun j t ht => ?_⟩
  · -- evenness
    show |-t| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |-t - s| ^ (-(1 / 2 : ℝ)) =
      |t| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ))
    rw [abs_neg, ← integral_neg_eq_self (fun s : ℝ => η s * |-t - s| ^ (-(1 / 2 : ℝ))) volume]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    show η (-s) * |-t - -s| ^ (-(1 / 2 : ℝ)) = η s * |t - s| ^ (-(1 / 2 : ℝ))
    rw [hη.1 s, show -t - -s = -(t - s) by ring, abs_neg]
  · -- smoothness on `{0}ᶜ`
    rw [fhpbb2b_highPassKernel_eq]
    intro x hx
    exact ((fhpbb2a_contDiffAt (-(1 / 2 : ℝ)) (Set.mem_compl_singleton_iff.mp hx)).sub
      (fhpbb2b_contDiff η).contDiffAt).contDiffWithinAt
  · -- the bound near zero
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (fhpbb2b_contDiff η).continuous.continuousOn
    refine ⟨1 + |M|, fun t ht => ?_⟩
    rw [fhpbb2b_highPassKernel_eq]
    have hG : |∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ))| ≤ M := by
      have h := hM t (abs_le.mp ht)
      rwa [Real.norm_eq_abs] at h
    have hIt : (0 : ℝ) ≤ |t| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg t) _
    have htri := norm_sub_le (|t| ^ (-(1 / 2 : ℝ)))
      (∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ)))
    simp only [Real.norm_eq_abs, abs_of_nonneg hIt] at htri
    have hexp : (1 + |M|) * (1 + |t| ^ (-(1 / 2 : ℝ))) =
        1 + |t| ^ (-(1 / 2 : ℝ)) + |M| + |M| * |t| ^ (-(1 / 2 : ℝ)) := by ring
    have hMM := le_abs_self M
    have hnn : 0 ≤ |M| * |t| ^ (-(1 / 2 : ℝ)) := mul_nonneg (abs_nonneg M) hIt
    show |(|t| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ)))| ≤
      (1 + |M|) * (1 + |t| ^ (-(1 / 2 : ℝ)))
    rw [hexp]
    linarith
  · -- derivatives away from zero
    exact fhpbb2b_iteratedDeriv_sub η j ht

end ParabolicRectifiability.Foundations
