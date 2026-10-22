import ParabolicRectifiability.Foundations.Proofs.HighPass.IntermediateStatements
import ParabolicRectifiability.Foundations.Proofs.HighPass.OneDimUnweighted
import ParabolicRectifiability.Foundations.Proofs.HighPass.OneDimWeighted
import ParabolicRectifiability.Foundations.Proofs.HighPass.SchwartzNormFinite
import ParabolicRectifiability.Foundations.Proofs.HighPass.Marginal
import ParabolicRectifiability.Foundations.Proofs.HighPass.DifferenceBracket
import ParabolicRectifiability.Foundations.Proofs.HighPass.MeanBracket
import ParabolicRectifiability.Foundations.Proofs.HighPass.KernelBasic
import ParabolicRectifiability.Foundations.Proofs.HighPass.InverseHalfAsymptotic
import ParabolicRectifiability.Foundations.Proofs.HighPass.KernelTails
import ParabolicRectifiability.Foundations.Proofs.HighPass.InverseHalfFourier
import ParabolicRectifiability.Foundations.Proofs.HighPass.KernelFourier
import ParabolicRectifiability.Foundations.Proofs.HighPass.TimeConvolution
import ParabolicRectifiability.Foundations.Proofs.HighPass.TestSchwartz
import ParabolicRectifiability.Foundations.Proofs.HighPass.TestIdentity
import ParabolicRectifiability.Foundations.Proofs.HighPass.BMOLogGrowth
import ParabolicRectifiability.Foundations.Proofs.HighPass.BMOConvolution
import ParabolicRectifiability.Foundations.Proofs.HighPass.LowPass
import ParabolicRectifiability.Foundations.Proofs.HighPass.HighPassPairing
import ParabolicRectifiability.Foundations.Proofs.HighPass.CorrectedTest
import ParabolicRectifiability.Foundations.Proofs.HighPass.SchwartzExtension
import ParabolicRectifiability.Foundations.Proofs.HighPass.BracketOfAeEq

/-! # High-pass kernel estimates: intermediate statements

This module states the twenty-one intermediate statements in the proof of the four public
statements of the high-pass chain (`HighPassWeightedPairingStatement` and its siblings): the weighted
pairing estimate (part b1), the high-pass kernel (part b2), the BMO growth of high-pass
convolutions (part c1) and the high-pass pairing (part c2). A statement of the form
`S₁ → S₂ → T` is in implication form: its hypotheses are the named sibling statements it
consumes. The a.e. fibre transfer `fhpa_ae_fibre_halfTimeDeriv_proof` is imported directly.

Parts (b2), (c1) and (c2) use cutoff choice (b) only, as the public statements do.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ContDiff SchwartzMap FourierTransform

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-! ## (b1) The weighted pairing estimate -/

/-- **Unweighted one-dimensional kernel estimate.**
`FhpbcOneDimUnweightedStatement`, i.e. a universal `C ≥ 0` with
`∫⁻ ‖D f‖ₑ ≤ C ∫⁻ (‖f‖ₑ + ‖f'‖ₑ)` for every `C¹` `f : ℝ → ℂ`, where
`D f(t) = κ ∫ |h|^{-3/2} (f t - f (t-h)) dh` (`fhpbc_halfDeriv1D`).
Route: if the right side is `∞` there is nothing to prove. Pointwise, at a time where the
`h`-integrand is integrable, `‖D f t‖ ≤ κ ∫_{|h|≤1} |h|^{-3/2} ‖f t - f (t-h)‖ + κ ∫_{|h|>1}
|h|^{-3/2} (‖f t‖ + ‖f (t-h)‖)` (elsewhere `D f t = 0`). Local part: `f t - f (t-h) =
∫_0^1 h f'(t - α h) dα` (`intervalIntegral.integral_eq_sub_of_hasDerivAt`), Tonelli
(`lintegral_lintegral_swap`) and translation invariance give `∫ ‖f t - f (t-h)‖ dt ≤ |h| ‖f'‖₁`,
and `∫_{|h|≤1} |h|^{-1/2} = 4`. Far part: `∫_{|h|>1} |h|^{-3/2} = 4`, translation invariance.
Constant: `C = 8 κ` suffices. Mathlib: `lintegral_mono`, `lintegral_lintegral_swap`,
`lintegral_add_right_eq_self`-type translation invariance (`Measure.IsAddRightInvariant`),
`integral_rpow`/`intervalIntegral.integral_rpow`, `FractionalKernel.kappa_pos`. -/
theorem fhpbc_b1_oneDimUnweighted : FhpbcOneDimUnweightedStatement := by
  exact fhpbc_b1_oneDimUnweighted_proof

/-- **Weighted one-dimensional estimate for mean-zero functions.**
`FhpbcOneDimWeightedStatement`: a universal `C ≥ 0` with
`∫⁻ (1 + √|t|) ‖D f t‖ₑ ≤ C ∫⁻ (1 + |t|) (‖f t‖ₑ + ‖f' t‖ₑ)` for integrable `C¹` `f` with
`∫ f = 0`.
Route: split `D = D_loc + D_far` at `|h| = 1` (pointwise as for the unweighted estimate).
Local part: as for the unweighted estimate,
with the weight comparison `1 + √|t| ≤ 2 (1 + √|t - α h|)` for `|h| ≤ 1`, `α ∈ [0,1]`, then
`√|s| ≤ 1 + |s|`. Far part: `D_far f = c₀ f - κ a * f` with `a(h) = 1_{|h|>1} |h|^{-3/2}`,
`c₀ = κ ∫ a`; the first term is bounded by `c₀ ∫ (1 + |t|) |f|`. Since `∫ f = 0`,
`a * f (t) = ∫ f(s) [a(t-s) - a(t)] ds`, so Tonelli reduces to the shift-weight bound
`∫ (1 + √|t|) |a(t-s) - a(t)| dt ≤ C (1 + |s|)`: on `|t| ≤ 2|s| + 4` bound the two terms
separately by `‖a‖₁ (1 + √(2|s|+4))`; on the complement both arguments exceed `1` in absolute
value, `|t - s| ≥ |t|/2`, and the mean value theorem gives `|a(t-s) - a(t)| ≤ (3/2) 2^{5/2} |s|
|t|^{-5/2}`, whose weighted integral over `|t| > 2|s| + 4` is `≤ C |s| / (|s| + 2) ≤ C`.
Mathlib: `exists_hasDerivAt_eq_slope`/`norm_image_sub_le_of_norm_deriv_le_segment'`,
`integrableOn_Ioi_rpow_of_lt`, `integral_comp_sub_right`, `lintegral_lintegral_swap`. -/
theorem fhpbc_b1_oneDimWeighted : FhpbcOneDimWeightedStatement := by
  exact fhpbc_b1_oneDimWeighted_proof

/-- **Schwartz tests have finite weighted norm.**
`FhpbcSchwartzNormFiniteStatement`: `fhp_weightedTestNorm θ < ⊤` for every
`θ : 𝓢(FourierSpace m, ℂ)`, every `m`.
Route: `1 + |t| ≤ 1 + ‖x‖` and `‖Dθ x (e_t)‖ ≤ ‖fderiv ℝ θ x‖` (`‖timeVector m‖ = 1`); then
`SchwartzMap.integrable_pow_mul` (`k = 0, 1`) for `θ` and for `SchwartzMap.fderivCLM ℝ θ`
(`SchwartzMap.fderivCLM_apply`), and `Integrable.lintegral_lt_top` /
`lintegral_ofReal_le_lintegral_enorm`-type comparisons. `m = 0` is included. -/
theorem fhpbc_b1_schwartzNormFinite : FhpbcSchwartzNormFiniteStatement := by
  exact fhpbc_b1_schwartzNormFinite_proof

/-- **The spatial marginal of a spatially compact Schwartz test.**
`FhpbcMarginalStatement`: for `θ` supported spatially in a compact `A`, the
marginal `F(s) = ∫ θ(u,s) du` is `C¹`, integrable, `∫ F = ∫ θ`,
`∫⁻ (1 + |s|) (‖F s‖ₑ + ‖F' s‖ₑ) ≤ N(θ)`, and `∫ testKernel θ (u,t) du = D F (t)` for every `t`.
Route: differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`
with the bound `1_A(u) · sup ‖fderiv ℝ θ‖`, since `θ(u,·) ≡ 0` for `u ∉ A`), `F' s = ∫ ∂_t θ(u,s)
du` with `∂_t θ = fderiv ℝ θ x (timeVector m)` (chain rule along `s ↦ toLp 2 (u,s)`), continuity
of `F'` by `continuous_of_dominated`. Fubini through the measure-preserving coordinates
(`fourierCoordinates_symm_measurePreserving_prod`, `integral_prod`, `lintegral_prod`) for
`∫ F = ∫ θ` and the weighted bound (`‖F s‖ ≤ ∫ ‖θ(u,s)‖ du`, same for `F'`). Kernel identity: at
fixed `t`, Fubini in `(u,h)` (`integral_integral_swap`), with the majorant `1_A(u) ·
testKernelControl θ · cancellationWeight h` (`norm_testKernelIntegrand_le`,
`integrable_cancellationWeight`) and `timeShift_toLp`. -/
theorem fhpbc_b1_marginal : FhpbcMarginalStatement := by
  exact fhpbc_b1_marginal_proof

/-- **The difference term of the split, quantitatively** (using the unweighted estimate;
split at the spatial base point `0`).
For parabolic Lipschitz `G` and compact `A` there is `C ≥ 0` such that for every
Schwartz `θ` supported spatially in `A`, `t ↦ ∫ (G(u,t) - G(0,t)) testKernel θ (u,t) du` is
a.e. strongly measurable and `∫⁻ ‖·‖ₑ ≤ C N(θ)`. (No mean-zero condition.)
Route: `|G(u,t) - G(0,t)| ≤ L ‖u‖ ≤ L ρ_A` on `A` (same time; `dist_point`), the kernel vanishes
for `u ∉ A` (`θ(u,·) ≡ 0`); `‖∫ ·‖ₑ ≤ ∫⁻ ‖·‖ₑ` (`enorm_integral_le_lintegral_enorm`); Tonelli in
`(t,u)` (`lintegral_lintegral_swap`, joint measurability from `stronglyMeasurable_testKernel`);
on each fibre `f_u(s) = θ(u,s)` (smooth, `deriv f_u s = fderiv ℝ θ (u,s) (timeVector m)`),
`testKernel θ (u,t) = D f_u (t)` (unfold, `timeShift_toLp`), and the unweighted estimate; then the coordinates
(`fourierCoordinates_symm_measurePreserving_prod`, `lintegral_prod`) and `1 ≤ 1 + |t|` give
`≤ L ρ_A C_U N(θ)`. Measurability: `StronglyMeasurable.integral_prod_right'`.
Hypothesis: `FhpbcOneDimUnweightedStatement` (the first argument). -/
theorem fhpbc_b1_differenceBracket : FhpbcOneDimUnweightedStatement →
    ∀ (m : ℕ) (G : FourierSpace m → ℝ),
      (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
      ∀ A : Set (Spatial m), IsCompact A → ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ : 𝓢(FourierSpace m, ℂ), fhp_IsSpatiallySupportedIn (⇑θ) A →
          AEStronglyMeasurable (fun t : ℝ => ∫ u : Spatial m,
            ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
              testKernel θ (WithLp.toLp 2 (u, t))) ∧
          ∫⁻ t : ℝ, ‖∫ u : Spatial m,
              ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
                testKernel θ (WithLp.toLp 2 (u, t))‖ₑ ≤
            ENNReal.ofReal C * fhp_weightedTestNorm (⇑θ) := by
  exact fhpbc_b1_differenceBracket_proof

/-- **The mean term of the split, quantitatively** (using the weighted estimate; growth
`|G(0,t)| ≤ |G(0,0)| + L √|t|`).
For parabolic Lipschitz `G` and compact `A` there is `C ≥ 0` such that for every
Schwartz `θ` supported spatially in `A` with `∫ θ = 0`,
`t ↦ G(0,t) ∫ testKernel θ (u,t) du` is a.e. strongly measurable and `∫⁻ ‖·‖ₑ ≤ C N(θ)`.
Route: `FhpbcMarginalStatement` gives `∫ testKernel θ (u,t) du = D F(t)` with `F` the marginal (`C¹`, integrable,
`∫ F = ∫ θ = 0`, `∫⁻ (1 + |s|) (‖F‖ₑ + ‖F'‖ₑ) ≤ N(θ)`); the growth bound (`dist_point` with
`max 0 √|t| = √|t|`) gives `‖G(0,t)‖ ≤ max(|G(0,0)|, L) (1 + √|t|)`; the weighted estimate finishes with
`C = max(|G(0,0)|, L) C_W`. Measurability: continuity of `t ↦ G(0,t)` and
`StronglyMeasurable.integral_prod_right'` for the kernel marginal.
Hypotheses: `FhpbcOneDimWeightedStatement`, `FhpbcMarginalStatement` (the first two
arguments). -/
theorem fhpbc_b1_meanBracket : FhpbcOneDimWeightedStatement → FhpbcMarginalStatement →
    ∀ (m : ℕ) (G : FourierSpace m → ℝ),
      (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
      ∀ A : Set (Spatial m), IsCompact A → ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ : 𝓢(FourierSpace m, ℂ), fhp_IsSpatiallySupportedIn (⇑θ) A → ∫ x, θ x = 0 →
          AEStronglyMeasurable (fun t : ℝ => (G (WithLp.toLp 2 (0, t)) : ℂ) *
            ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t))) ∧
          ∫⁻ t : ℝ, ‖(G (WithLp.toLp 2 (0, t)) : ℂ) *
              ∫ u : Spatial m, testKernel θ (WithLp.toLp 2 (u, t))‖ₑ ≤
            ENNReal.ofReal C * fhp_weightedTestNorm (⇑θ) := by
  exact fhpbc_b1_meanBracket_proof

/-! ## (b2) The high-pass kernel, cutoff choice (b) -/

/-- **Basic kernel facts.**
`FhpbcKernelBasicStatement`: evenness of `K`; `ContDiffOn ℝ ∞ K {0}ᶜ`; the
near-zero bound `|K t| ≤ C (1 + |t|^{-1/2})` for `|t| ≤ 1`; and for `t ≠ 0`,
`K^{(j)}(t) = I^{(j)}(t) - ∫ η^{(j)}(s) I(t-s) ds`.
Route: evenness from `η (-s) = η s`, `I (-t) = I t` and `integral_comp_neg`. Smoothness of
`η * I`: write `(η * I)(t) = ∫ η(t - r) I(r) dr` (`integral_sub_left_eq_self`) and differentiate
under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) with the majorant
`sup_{|t'-t|<1} |η^{(j+1)}(t' - r)| |I(r)| ≤ C (1 + |t|)^2 (1 + |r|)^{-2} |r|^{-1/2}` (Schwartz
decay of the iterated derivatives `SchwartzMap.derivCLM`); induct on `j` and conclude with
`contDiff_of_differentiable_iteratedDeriv`. `I` is smooth on `{0}ᶜ` (`Real.contDiffAt_rpow_const`,
`contDiffAt_abs`). The difference rule on the open set `{0}ᶜ` (`iteratedDerivWithin_of_isOpen`,
`iteratedDerivWithin_sub`). Near zero: `η * I` is continuous, hence bounded on `[-1,1]`, and
`|I t| ≤ |t|^{-1/2}` (value `0` at `0`). -/
theorem fhpbc_b2_kernelBasic : FhpbcKernelBasicStatement := by
  exact fhpbc_b2_kernelBasic_proof

/-- **Asymptotic expansion of `ρ * I` with remainder `O(|t|^{-N})`** (a physical-space
route for the tails).
`FhpbcInverseHalfAsymptoticStatement`.
Route: for `|t| ≥ 1` split `∫ ρ(s) I(t-s) ds` at `|s| ≤ |t|/2`. On `|s| ≤ |t|/2` the segment
`[t-s, t]` stays in `|·| ≥ |t|/2`, where `I` is smooth with `|I^{(k)}(ξ)| = c_k |ξ|^{-1/2-k}`;
Taylor with Lagrange remainder of order `N` (`taylor_mean_remainder_lagrange_iteratedDeriv`)
gives `I(t-s) = Σ_{k<N} I^{(k)}(t) (-s)^k / k! + R`, `|R| ≤ c_N 2^{N+1/2} |t|^{-1/2-N} |s|^N`.
The polynomial terms restored to all of `ℝ` and the region `|s| > |t|/2` cost
`C_M |t|^{-M}` by Schwartz decay of `ρ` (`SchwartzMap.le_seminorm`), using
`sup_t ∫ (1 + |s|)^{-2} |t - s|^{-1/2} ds < ∞`. Never expand across `s = t`. -/
theorem fhpbc_b2_inverseHalfAsymptotic : FhpbcInverseHalfAsymptoticStatement := by
  exact fhpbc_b2_inverseHalfAsymptotic_proof

/-- **Rapid tails of `K` and its derivatives.**
`FhpbcKernelTailsStatement`.
Route: for `t ≠ 0`, `FhpbcKernelBasicStatement` gives `K^{(j)} = I^{(j)} - η^{(j)} * I`; apply
`FhpbcInverseHalfAsymptoticStatement` to
`ρ = η^{(j)}` (the Schwartz map `(SchwartzMap.derivCLM ℝ)^[j] η`) with `N' = max N (j+1)`.
Moments: `∫ s^k η^{(j)}(s) ds = (-1)^j j!` if `k = j` and `0` otherwise, because
`𝓕(η^{(j)})(τ) = (2πiτ)^j η̂(τ)` equals `(2πiτ)^j` near `τ = 0` (`fourier_iteratedDeriv`) and
`∫ (-2πis)^k ρ(s) ds = (𝓕ρ)^{(k)}(0)` (`iteratedDeriv_fourier`); equivalently by repeated
integration by parts and the vanishing moments of `η`. The expansion collapses to
`I^{(j)}(t)`, which cancels.
Hypotheses: `FhpbcKernelBasicStatement`, `FhpbcInverseHalfAsymptoticStatement`. -/
theorem fhpbc_b2_kernelTails :
    FhpbcKernelBasicStatement → FhpbcInverseHalfAsymptoticStatement →
      FhpbcKernelTailsStatement := by
  exact fhpbc_b2_kernelTails_proof

/-- **The normalized Fourier transform of `|t|^{-1/2}`.**
`FhpbcInverseHalfFourierStatement`:
`∫ |t|^{-1/2} ψ̂(t) dt = ∫ |τ|^{-1/2} ψ(τ) dτ` for every `ψ : 𝓢(ℝ, ℂ)`.
Route (real Gamma integrals only): `|t|^{-1/2} = Γ(1/4)^{-1} ∫_0^∞ λ^{-3/4} e^{-λ t²} dλ`
(`integral_rpow_mul_exp_neg_mul_rpow` / `Real.Gamma_eq_integral` after `μ = λ t²`); Fubini
(absolutely convergent: `∫∫ λ^{-3/4} e^{-λt²} |ψ̂(t)| = Γ(1/4) ∫ |t|^{-1/2} |ψ̂|`); the Gaussian
transform (`fourier_gaussian_pi'` / `fourierIntegral_gaussian`) and the multiplication formula
`∫ ĝ ψ = ∫ g ψ̂` (`VectorFourier.integral_fourierIntegral_smul_eq_flip`); then
`∫_0^∞ λ^{-3/4} (π/λ)^{1/2} e^{-π²τ²/λ} dλ = Γ(1/4) |τ|^{-1/2}` (substitution
`μ = π²τ²/λ`). A damped route would need `∫_0^∞ t^{-1/2} e^{-zt} = √π z^{-1/2}` for complex `z`;
Mathlib's `integral_cpow_mul_exp_neg_mul_Ioi` takes real `r`, so the Gaussian route is preferred. -/
theorem fhpbc_b2_inverseHalfFourier : FhpbcInverseHalfFourierStatement := by
  exact fhpbc_b2_inverseHalfFourier_proof

/-- **`K ∈ L¹`, `∫ K = 0` and `K̂ = (1 - η̂) |τ|^{-1/2}`.**
For an admissible cutoff, `Integrable K`, `∫ K = 0`, and
`𝓕 K τ = (1 - η̂ τ) |τ|^{-1/2}` for `τ ≠ 0`.
Route: integrability from the near-zero bound (`FhpbcKernelBasicStatement`) and the `j = 0`,
`N = 2` tail (`FhpbcKernelTailsStatement`), with
measurability from `ContinuousOn` on the co-null open set `{0}ᶜ`. For a real compact smooth test
`g` (complexified to a Schwartz `ψ`): `∫ K ψ̂ = ∫ I ψ̂ - ∫ (η * I) ψ̂`, and by absolute Fubini and
evenness of `η`, `∫ (η * I) ψ̂ = ∫ I 𝓕(η̂ ψ)`; `FhpbcInverseHalfFourierStatement` twice gives `∫ K ψ̂ = ∫ (1 - η̂) |τ|^{-1/2} ψ`.
With `∫ K ψ̂ = ∫ K̂ ψ` (`VectorFourier.integral_fourierIntegral_smul_eq_flip`), the continuous
`K̂` (`Real.continuous_fourierIntegral`/`VectorFourier.fourierIntegral_continuous`) and the
locally integrable `M` agree a.e. (`ae_eq_of_integral_contDiff_smul_eq`), hence on the open set
`τ ≠ 0` where both are continuous. Finally `∫ K = K̂(0) = lim_{τ → 0} M(τ) = 0`, since `M = 0`
near `0` (`η̂ ≡ 1` there).
Hypotheses: `FhpbcKernelBasicStatement`, `FhpbcKernelTailsStatement`,
`FhpbcInverseHalfFourierStatement`. -/
theorem fhpbc_b2_kernelFourier : FhpbcKernelBasicStatement → FhpbcKernelTailsStatement →
    FhpbcInverseHalfFourierStatement →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      Integrable (fhp_highPassKernel η) ∧
      ∫ t, fhp_highPassKernel η t = 0 ∧
      ∀ τ : ℝ, τ ≠ 0 →
        𝓕 (fun t : ℝ => (fhp_highPassKernel η t : ℂ)) τ =
          (1 - 𝓕 (fun t : ℝ => (η t : ℂ)) τ) * ((|τ| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  exact fhpbc_b2_kernelFourier_proof

/-- **Time convolution with an `L¹` kernel** (generic in the kernel).
`FhpbcTimeConvolutionStatement`: for integrable `k : ℝ → ℝ` and real compact
smooth `φ` on `ℝ^m × ℝ`, `k *_t φ` is smooth, supported spatially in a compact set, integrable,
`∫ k *_t φ = (∫ k)(∫ φ)`, and `𝓕(k *_t φ)(ζ) = k̂(τ) φ̂(ζ)` with `τ = (ofLp ζ).2`.
Route: smoothness by moving derivatives to `φ` (all derivatives dominated by
`|k(s)| sup ‖D^n φ‖`): either iterate `hasFDerivAt_integral_of_dominated_of_fderiv_le` for
vector-valued `φ`, or write `k *_t φ` as a Mathlib convolution of `φ` with the finite measures
`map (s ↦ s • e_t) (k^± ds)` and use `HasCompactSupport.contDiff_convolution_right`. Spatial
support: the spatial projection of `tsupport φ` (compact, `fourierCoordinatesHomeomorph`).
Integrability and the integral: Tonelli/Fubini with the measure-preserving shear
`(x,s) ↦ (x - s e_t, s)`. Fourier: Fubini and `⟪s • timeVector m, ζ⟫ = s τ`
(`VectorFourier.fourierIntegral_comp_add_right`). -/
theorem fhpbc_b2_timeConvolution : FhpbcTimeConvolutionStatement := by
  exact fhpbc_b2_timeConvolution_proof

/-- **The high-pass test is Schwartz and has finite norm.**
For an admissible cutoff and real compact smooth `φ`, there is
`Θ : 𝓢(FourierSpace m, ℂ)` with `Θ x = (K *_t φ)(x)` for every `x`, and
`N(K *_t φ) < ∞`.
Route (Fourier): the multiplier `M̃(ξ,τ) = (1 - η̂(τ)) |τ|^{-1/2}` is smooth (it vanishes near
`τ = 0`) with bounded derivatives, so `Function.HasTemperateGrowth`; put
`Θ = 𝓕⁻ (SchwartzMap.smulLeftCLM M̃ (𝓕 φ_ℂ))`. By `FhpbcTimeConvolutionStatement` and the kernel facts,
`𝓕 (K *_t φ) = K̂(τ) φ̂ = M̃ φ̂ = 𝓕 Θ` (at `τ = 0` both vanish), both functions are continuous and
integrable with integrable transforms, so `Continuous.fourierInv_fourier_eq` identifies them.
(Physical alternative: `∂^α (K *_t φ) = K *_t ∂^α φ` with the rapid tails of `K`.) Finite norm:
`N(K *_t φ) = N(Θ)` (`Θ = ofRealCLM ∘ (K *_t φ)`, so the time derivatives have equal norms) and
`FhpbcSchwartzNormFiniteStatement`.
Hypotheses: `FhpbcKernelFactsStatement`, `FhpbcTimeConvolutionStatement`,
`FhpbcSchwartzNormFiniteStatement`. -/
theorem fhpbc_b2_testSchwartz : FhpbcKernelFactsStatement → FhpbcTimeConvolutionStatement →
    FhpbcSchwartzNormFiniteStatement →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      ∀ (m : ℕ) (φ : FourierSpace m → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∃ Θ : 𝓢(FourierSpace m, ℂ),
          ∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) ∧
        fhp_weightedTestNorm (fhp_timeConvolution (fhp_highPassKernel η) φ) < ⊤ := by
  exact fhpbc_b2_testSchwartz_proof

/-- **The identity `|D_t|^{1/2} (K *_t φ) = (1 - η *_t) φ`.**
For an admissible cutoff, real compact smooth `φ` and **any** Schwartz `Θ` with
`Θ x = (K *_t φ)(x)` for every `x`, `halfTimeDeriv m Θ = φ - η *_t φ` almost everywhere.
Route: `𝓕 (halfTimeDeriv m Θ) = |τ|^{1/2} 𝓕Θ` (`coeFn_fourier_halfTimeDeriv`), and
`𝓕Θ = K̂(τ) φ̂ = (1 - η̂(τ)) |τ|^{-1/2} φ̂` (`FhpbcTimeConvolutionStatement`, kernel facts), so the product is
`(1 - η̂(τ)) φ̂` (also at `τ = 0`). The Schwartz map
`Φ = 𝓕⁻ (SchwartzMap.smulLeftCLM (1 - η̂ ∘ τ) (𝓕 φ_ℂ))` has this transform, equals
`φ - η *_t φ` pointwise (`FhpbcTimeConvolutionStatement` with `k = η`, Fourier inversion), and `halfTimeDeriv m Θ = Φ.toLp`
by injectivity of `Lp.fourierTransformₗᵢ` (`SchwartzMap.toLp_fourier_eq`); then
`SchwartzMap.coeFn_toLp`.
Hypotheses: `FhpbcKernelFactsStatement`, `FhpbcTimeConvolutionStatement`. -/
theorem fhpbc_b2_testIdentity : FhpbcKernelFactsStatement → FhpbcTimeConvolutionStatement →
    ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
      ∀ (m : ℕ) (φ : FourierSpace m → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∀ Θ : 𝓢(FourierSpace m, ℂ),
          (∀ x, Θ x = (fhp_timeConvolution (fhp_highPassKernel η) φ x : ℂ)) →
          (halfTimeDeriv m Θ : FourierSpace m → ℂ) =ᵐ[volume]
            fun x => ((φ x - fhp_timeConvolution η φ x : ℝ) : ℂ) := by
  exact fhpbc_b2_testIdentity_proof

/-! ## (c1) Logarithmic growth of BMO functions -/

/-- **BMO growth on translated fixed cylinders.**
`FhpbcBMOLogGrowthStatement` (the first clause of `HighPassBMOLogStatement`).
Route: with `f = g ∘ Ψ⁻¹` on `Space m` and `Ψ = fourierToParabolic m` measure preserving
(`fourierToParabolic_measurePreserving`), the cylinder `A × [a+j, b+j]` lies in the single
parabolic ball `B_j = B(point 0 (c + j), R₀)` with `c = (a+b)/2` and a fixed `R₀` (`A` bounded,
`mem_ball_point`), and `|B_j| = |B_0|` (`parabolicVolume_ball`). Then
`∫_{B_j} |f| ≤ |B_0| (B + |f_{B_j}|)` and `|f_{B_j} - f_{B_0}| ≤ C_m B (1 + log(1 + √|j| / R₀))`
by chaining concentric doublings on both sides (step `|f_{B(p,r)} - f_{B(p,2r)}| ≤ 2^{m+2} B`,
`parabolicVolume_ball_two_mul`) and one nested-ball comparison
`B(q, 2^k R₀) ⊂ B(p, 2^{k+1} R₀)` when `dist p q ≤ 2^k R₀`. If `a > b` the set is empty.
The concentric step and telescoping are proved, for `HasStandardParabolicBMOBound`, in
`b1bmo_avg_step` and `b1bmo_avg_tele`. -/
theorem fhpbc_c1_logGrowth : FhpbcBMOLogGrowthStatement := by
  exact fhpbc_c1_logGrowth_proof

/-- **The high-pass convolution of a BMO function.**
For `g` with finite parabolic BMO seminorm and an admissible cutoff: the absolute
local bound `∫⁻_S ∫⁻ |K(s)| |g(x - s e_t)| < ∞` for every compact `S`, a.e. absolute convergence,
`LocallyIntegrable (K *_t g)`, and invariance under adding constants (a.e.); this is the
second clause of `HighPassBMOLogStatement`.
Route: `S ⊂ A × [a,b]` with `A` a closed ball; Tonelli (`lintegral_lintegral_swap`, with
`AEMeasurable` of `(x,s) ↦ g(x - s e_t)` from the measure-preserving shear) and
`∫⁻_S |g(x - s e_t)| dx ≤ ∫⁻_{A × [a-s, b-s]} |g| ≤ C (1 + log(3 + |s|))` (`FhpbcBMOLogGrowthStatement` with
`j = ⌊-s⌋`); then `∫ |K(s)| (1 + log(3 + |s|)) ds < ∞` from `K ∈ L¹` and the tail
`|K(s)| ≤ C |s|^{-2}` for `|s| ≥ 1`. A.e. convergence: finite lintegrals on the compact
exhaustion `closedBall 0 n` (`ae_lt_top`, `ae_iUnion_iff`-type). Local integrability:
`AEStronglyMeasurable.integral_prod_right'` and the same bound. Constants: at every point of
absolute convergence, `∫ K (g + c) = ∫ K g + c ∫ K` and `∫ K = 0`.
Hypotheses: `FhpbcBMOLogGrowthStatement`, `FhpbcKernelFactsStatement`. -/
theorem fhpbc_c1_convolution : FhpbcBMOLogGrowthStatement → FhpbcKernelFactsStatement →
    ∀ (m : ℕ) (g : FourierSpace m → ℝ),
      (∃ B : ℝ, HasStandardParabolicBMOBound m (g ∘ (fourierToParabolic m).symm) B) →
      ∀ η : 𝓢(ℝ, ℝ), fhp_IsFrequencyCutoff η →
        (∀ S : Set (FourierSpace m), IsCompact S →
          ∫⁻ x in S, ∫⁻ s : ℝ, ‖fhp_highPassKernel η s‖ₑ * ‖g (x - s • timeVector m)‖ₑ < ⊤) ∧
        (∀ᵐ x ∂(volume : Measure (FourierSpace m)),
          Integrable (fun s : ℝ => fhp_highPassKernel η s * g (x - s • timeVector m))) ∧
        LocallyIntegrable (fhp_timeConvolution (fhp_highPassKernel η) g) ∧
        ∀ c : ℝ, fhp_timeConvolution (fhp_highPassKernel η) (fun x => g x + c) =ᵐ[volume]
          fhp_timeConvolution (fhp_highPassKernel η) g := by
  exact fhpbc_c1_convolution_proof

/-! ## (c2) The high-pass pairing -/

/-- **The low-pass side.**
`FhpbcLowPassStatement`.
Route: `|G(x - s e_t)| ≤ |G x| + L √|s|` (`dist_point`: the time shift moves `Ψ x` by `√|s|`),
so `s ↦ η(s) G(x - s e_t)` is integrable (`SchwartzMap.integrable_pow_mul`-type decay of `η`).
Continuity: the time shift is a parabolic isometry, so
`|η *_t G(x) - η *_t G(y)| ≤ L ‖η‖₁ d_P(Ψ x, Ψ y)`. For compact smooth `φ` supported in
`A × [-T,T]`: `|η *_t φ (u,t)| ≤ ‖φ‖_∞ ∫_{|t - s| ≤ T} |η(s)| ds` decays faster than any power,
vanishes off `A × ℝ`, and `|G| ≤ C_A + L √|t|` there, so `G (η *_t φ)` is integrable; the
identity is absolute Fubini (`integral_integral_swap`), the substitution `y = x - s e_t`
(measure preserving) and `s ↦ -s` with `η` even. -/
theorem fhpbc_c2_lowPass : FhpbcLowPassStatement := by
  exact fhpbc_c2_lowPass_proof

/-- **The high-pass side.**
`FhpbcHighPassPairingStatement`.
Route: `∫ |g(x)| ∫ |K(s)| |φ(x - s e_t)| ds dx = ∫ |φ(y)| ∫ |K(s)| |g(y - s e_t)| ds dy`
(Tonelli, the shear, `s ↦ -s` and evenness of `K`), finite by the absolute local bound of (c1)
on `S = tsupport φ` and `‖φ‖_∞`; then the same substitutions with Fubini
(`integral_integral_swap`) give `∫ g (K *_t φ) = ∫ (K *_t g) φ`.
Hypotheses: `HighPassBMOLogStatement` (public statement (c1); only its second clause
is used) and `FhpbcKernelFactsStatement` (evenness, integrability). -/
theorem fhpbc_c2_highPassPairing : HighPassBMOLogStatement → FhpbcKernelFactsStatement →
    FhpbcHighPassPairingStatement := by
  exact fhpbc_c2_highPassPairing_proof

/-- **Corrected compact tests.**
`FhpbcCorrectedTestStatement`.
Route: `θ = Re ∘ Θ` is smooth with Schwartz decay; fix `ρ(u,t) = ρ₁(u) ρ₂(t)` compact smooth with
`∫ ρ = 1` and `A' = A ∪ spatial projection of tsupport ρ`; with a smooth `χ` equal to `1` on
`[-1,1]` and `0` off `[-2,2]`, put `χ_n(t) = χ(t/(n+1))`, `a_n = ∫ χ_n θ`,
`θ_n = χ_n θ - a_n ρ`. Then `θ_n` is compact smooth (`A` compact), `∫ θ_n = 0`, `|a_n| ≤ ‖θ‖₁ =: D`,
`a_n → ∫ θ = 0` and `θ_n → θ` pointwise (dominated convergence); `N(θ_n - θ) → 0` by dominated
convergence from `N(θ) < ∞` (`FhpbcSchwartzNormFiniteStatement` on `Θ`), `|χ_n'| ≤ ‖χ'‖_∞`
and `N(ρ) < ∞`.
Hypothesis: `FhpbcSchwartzNormFiniteStatement` (for `N(θ) < ∞` through `Θ`). -/
theorem fhpbc_c2_correctedTest : FhpbcSchwartzNormFiniteStatement →
    FhpbcCorrectedTestStatement := by
  exact fhpbc_c2_correctedTest_proof

/-- **The representation extends to spatially compact Schwartz tests.**
`FhpbcSchwartzExtensionStatement`.
Route: `g θ` is integrable: `|θ(u,t)| ≤ C (1 + |t|)^{-2} 1_A(u)` (Schwartz decay of `Θ`) and
`FhpbcBMOLogGrowthStatement` on the unit cylinders `A × [j, j+1]`,
`Σ (1 + |j|)^{-2} (1 + log(2 + |j|)) < ∞`. Take the corrected tests `θ_n` of
`FhpbcCorrectedTestStatement`. For each `n`, the representation clause on `θ_n` and the window
limit of (b1) on the Schwartz test `realCompactTest θ_n` give `T_G(θ_n) = ∫ g θ_n` (uniqueness
of limits). By linearity of `halfTimeDeriv` (a.e. on fibres, as in `fhpa_ae_fibre_halfTimeDeriv`) and the integrability
clauses of (b1), `T_G(θ_n) - T_G(Θ) = T_G(θ_n - Θ)`, and the (b1) bound on the Schwartz test
`θ_n - Θ` (supported spatially in `A'`, mean zero) gives `|·| ≤ C N(θ_n - θ) → 0`. Dominated
convergence (`|g θ_n| ≤ |g| (|θ| + D |ρ|)`) gives `∫ g θ_n → ∫ g θ`.
Hypotheses: `HighPassWeightedPairingStatement` (public statement (b1)),
`FhpbcBMOLogGrowthStatement`, `FhpbcCorrectedTestStatement`. -/
theorem fhpbc_c2_schwartzExtension : HighPassWeightedPairingStatement →
    FhpbcBMOLogGrowthStatement → FhpbcCorrectedTestStatement →
    FhpbcSchwartzExtensionStatement := by
  exact fhpbc_c2_schwartzExtension_proof

/-- **The bracket of a test whose half derivative is a real function**
(the bracket defining `T_G(θ)` is then `G (1 - η*) φ`).
`FhpbcBracketOfAeEqStatement`.
Route: transport the a.e. identity along the measure-preserving coordinates and slice with time
outside (`fhpab12_timeFirst_measurePreserving`, `Measure.ae_ae_of_ae_prod`, exactly as in
`fhpa_ae_fibre_halfTimeDeriv`),
so for a.e. `t` the spatial integrands agree a.e. and `halfTimeSpatialBracket G Θ t =
∫ G(u,t) ψ(u,t) du`; then `integral_prod` through the coordinates and `integral_ofReal`. -/
theorem fhpbc_c2_bracketOfAeEq : FhpbcBracketOfAeEqStatement := by
  exact fhpbc_c2_bracketOfAeEq_proof

end ParabolicRectifiability.Foundations
