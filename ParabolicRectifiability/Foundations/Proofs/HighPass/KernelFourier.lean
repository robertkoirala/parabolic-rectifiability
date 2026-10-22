import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Analysis.FractionalKernel.HighPassFourier

/-! # `K ∈ L¹`, `∫ K = 0` and `K̂ = (1 - η̂) |τ|^{-1/2}`

Proves `fhpbc_b2_kernelFourier` under the name `fhpbc_b2_kernelFourier_proof`, in implication
form over `FhpbcKernelBasicStatement`, `FhpbcKernelTailsStatement` and
`FhpbcInverseHalfFourierStatement`, as the type itself states.

Use of the hypotheses: `FhpbcKernelBasicStatement` supplies continuity of `K` off `0` (from
`ContDiffOn ℝ ∞ K {0}ᶜ`) and the near-zero bound; `FhpbcKernelTailsStatement` with `j = 0`,
`N = 2` supplies the tail bound; together they give `K ∈ L¹`
(`FractionalKernel.fhpbb2h_integrable_of_bounds`). The weak identity of `|t|^{-1/2}` is used
through `FractionalKernel.fhpbb2f_inverseHalf_fourier_schwartz` and its general form
`fhpbb2f_weak_fourier` (needed for the modulated tests `τ ↦ e^{-2πiτs} ψ(τ)`), so the
hypothesis `FhpbcInverseHalfFourierStatement` is not consumed. The one-dimensional analysis
(weak identity with absolute bounds, then pointwise identification by
`ae_eq_of_integral_contDiff_smul_eq` and continuity) is in the `FractionalKernel` lemmas used
below; this module identifies
`fhp_highPassKernel η t = |t|^{-1/2} - ∫ η(s) |t - s|^{-1/2} ds` and extracts the cutoff's
condition `η̂ = 1` near `0`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- **The kernel is integrable with mean zero, and its Fourier transform.** For every
admissible cutoff `η`, `K = I - η * I` is integrable, has
integral zero, and `K̂(τ) = (1 - η̂(τ)) |τ|^{-1/2}` for `τ ≠ 0` (Mathlib's phase), given the basic kernel
facts, the rapid tails and the normalized transform of `|t|^{-1/2}`. -/
theorem fhpbc_b2_kernelFourier_proof : FhpbcKernelBasicStatement → FhpbcKernelTailsStatement →
    FhpbcInverseHalfFourierStatement →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      Integrable (fhp_highPassKernel η) ∧
      ∫ t, fhp_highPassKernel η t = 0 ∧
      ∀ τ : ℝ, τ ≠ 0 →
        𝓕 (fun t : ℝ => (fhp_highPassKernel η t : ℂ)) τ =
          (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  intro hB hT _hF η hη
  obtain ⟨_, hsmooth, ⟨C₀, hC₀⟩, _⟩ := hB η hη
  obtain ⟨C₁, hC₁⟩ := hT η hη 0 2
  have hint : Integrable (fhp_highPassKernel η) :=
    FractionalKernel.fhpbb2h_integrable_of_bounds hsmooth.continuousOn hC₀
      (fun t ht => by simpa only [iteratedDeriv_zero, Nat.cast_ofNat] using hC₁ t ht)
  have hdef : ∀ t : ℝ, fhp_highPassKernel η t =
      |t| ^ (-(1 / 2 : ℝ)) - ∫ s : ℝ, η s * |t - s| ^ (-(1 / 2 : ℝ)) := fun t => rfl
  obtain ⟨hzero, hfourier⟩ := FractionalKernel.fhpbb2h_kernelFourier_main hη.2.2.2 hdef hint
  exact ⟨hint, hzero, fun τ _ => hfourier τ⟩

end ParabolicRectifiability.Foundations
