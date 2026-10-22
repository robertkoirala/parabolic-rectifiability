import ParabolicRectifiability.Analysis.HalfTimeDerivative.TestKernel
import ParabolicRectifiability.Foundations.HalfTimeDerivative
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.FibreKernel
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.DifferenceTail
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.MarginalDecay
import ParabolicRectifiability.Foundations.Proofs.HighPassBracket.SqrtGrowth

/-! # The bracket of a parabolic Lipschitz function is in `L¹(dt)`

This module holds the five intermediate statements (`fhpa_ae_fibre_halfTimeDeriv`,
`fhpa_integrable_mul_testKernel`, `fhpa_integrable_differenceBracket`,
`fhpa_spatialIntegral_testKernel_decay`, `fhpa_integrable_sqrtGrowth_mul_decay`) in the proof of
`HalfTimeBracketIntegrableStatement`. They are assembled in `fhpa_halfTimeBracketIntegrable`.

Fix a parabolic Lipschitz `G`, a real compact smooth test
`φ` with `∫ φ = 0`, and the pointwise test kernel `K = testKernel φ`
(see `testKernel`), which equals the `L²` derivative
`halfTimeDeriv m φ` only almost everywhere (`testKernel_ae_halfTimeDeriv`). The proof is:

1. **a.e. fibre transfer** (`fhpa_ae_fibre_halfTimeDeriv`): for a.e. `t`, the spatial fibre of
   `halfTimeDeriv m φ` equals that of `K` a.e. in `u`; so the integrand and the bracket of the
   statement agree, for a.e. `t`, with the kernel integrand and the kernel bracket.
2. **Spatial integrability** (`fhpa_integrable_mul_testKernel`): `K(·,t)` is bounded and
   vanishes off the compact spatial projection of `supp φ`, so `c · K(·,t)` is integrable for
   every continuous `c` and every `t`.
3. **The split**, with `u₀ = 0`:
   `∫ G(u,t) K(u,t) du = ∫ [G(u,t) - G(0,t)] K(u,t) du + G(0,t) ∫ K(u,t) du`.
4. **The `|t|^{-3/2}` tail of the difference term** (`fhpa_integrable_differenceBracket`).
5. **The `|t|^{-5/2}` tail of the mean term** (`fhpa_spatialIntegral_testKernel_decay`, which
   uses `∫ φ = 0`) **and the growth `1 + √|t|`** (`fhpa_integrable_sqrtGrowth_mul_decay`).
-/

noncomputable section

open MeasureTheory
open scoped NNReal ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- **a.e. fibre transfer of the kernel identity** (from `testKernel_ae_halfTimeDeriv`).

For every complex Schwartz test `ψ` on `ℝ^m × ℝ` (all `m`), for almost every
time `t`, the spatial fibres `u ↦ (halfTimeDeriv m ψ)(u,t)` (the chosen `L²` representative)
and `u ↦ testKernel ψ (u,t)` agree almost everywhere on `ℝ^m`.

Proof route: `testKernel_ae_halfTimeDeriv` gives equality a.e. on `FourierSpace m`; transport
the null set along the measure-preserving coordinate equivalence `FourierSpace m ≃ ℝ^m × ℝ`
(`(u,t) ↦ WithLp.toLp 2 (u,t)`, volume to `volume.prod volume`, e.g.
`fourierCoordinates_measurePreserving_prod`), then `Measure.ae_ae_of_ae_prod` (with the time
variable outside; use `Measure.prod_swap` if the available lemma puts it inside). The proof is
`fhpa_ae_fibre_halfTimeDeriv_proof`. -/
theorem fhpa_ae_fibre_halfTimeDeriv {m : ℕ} (ψ : 𝓢(FourierSpace m, ℂ)) :
    ∀ᵐ t : ℝ, (fun u : Spatial m => halfTimeDeriv m ψ (WithLp.toLp 2 (u, t))) =ᵐ[volume]
      fun u => testKernel ψ (WithLp.toLp 2 (u, t)) := by
  exact fhpa_ae_fibre_halfTimeDeriv_proof ψ

/-- **Spatial integrability against the test kernel.** (`D_t^{1/2}φ` has the same spatial
support projection as `φ`.)

For a real compact smooth test `φ`, every continuous `c : ℝ^m → ℂ` and every
time `t`, the function `u ↦ c(u) · testKernel φ (u,t)` is integrable on `ℝ^m`.

Proof route: `testKernel` is strongly measurable (`stronglyMeasurable_testKernel`, composed
with the continuous section `u ↦ WithLp.toLp 2 (u,t)`) and bounded
(`norm_testKernel_le`); it vanishes for `u` outside the compact set `spatialTestSupport`
(`testKernel_eq_zero_of_notMem_spatialTestSupport`, `isCompact_spatialTestSupport`; the
complexified test has compact support, `tsupport_realCompactTest`); `c` is bounded on that
compact set. Bound by a constant times the indicator of the compact set. The proof is
`fhpa_integrable_mul_testKernel_proof`. -/
theorem fhpa_integrable_mul_testKernel {m : ℕ} (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (c : Spatial m → ℂ) (hcont : Continuous c)
    (t : ℝ) :
    Integrable (fun u : Spatial m => c u * testKernel (realCompactTest φ hφ hc)
      (WithLp.toLp 2 (u, t))) := by
  exact fhpa_integrable_mul_testKernel_proof φ hφ hc c hcont t

/-- **The difference term has an `|t|^{-3/2}` tail**, hence is absolutely integrable.

For `G` parabolic Lipschitz (`LipschitzWith L (G ∘ (fourierToParabolic m).symm)`,
the convention of `HalfTimeBracketIntegrableStatement`) and a real compact smooth test `φ`
(no mean-zero condition), the function
`t ↦ ∫ [G(u,t) - G(0,t)] · testKernel φ (u,t) du` is integrable on `ℝ`.

Proof route: `|G(u,t) - G(0,t)| ≤ L ‖u‖` (same time, `dist_point`); on the compact spatial
projection `A` of `supp φ`, `‖u‖ ≤ ρ_A`, and off `A` the kernel vanishes
(`testKernel_eq_zero_of_notMem_spatialTestSupport`). The kernel is bounded
(`norm_testKernel_le`) and has the tail `‖K(u,t)‖ ≤ c_S |t|^{-3/2}` for `|t| > 2S`
(`norm_testKernel_temporal_tail`, `S` a time-support bound). So the integrand is bounded by
`L ρ_A vol(A) · c · temporalWeight (2S) t`, integrable by `integrable_temporalWeight`.
Measurability: `StronglyMeasurable.integral_prod_right'` (or `_left`) on the jointly
measurable integrand. Spatial rank `m = 0` is included (one-point spatial integral). The proof is `fhpa_integrable_differenceBracket_proof`. -/
theorem fhpa_integrable_differenceBracket {m : ℕ} (G : FourierSpace m → ℝ)
    (hG : ∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm))
    (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun t : ℝ => ∫ u : Spatial m,
      ((G (WithLp.toLp 2 (u, t)) : ℂ) - (G (WithLp.toLp 2 (0, t)) : ℂ)) *
        testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))) := by
  exact fhpa_integrable_differenceBracket_proof G hG φ hφ hc

/-- **The spatially integrated kernel of a mean-zero test has an `|t|^{-5/2}` tail.**
If `ψ(t) = ∫ φ(u,t) du` and `∫ φ = 0`, then
`∫ D_t^{1/2}φ(u,t) du = D_t^{1/2}ψ(t) = O(|t|^{-5/2})`.

For a real compact smooth test `φ` with `∫ φ = 0`, the function
`t ↦ ∫ testKernel φ (u,t) du` is a.e. strongly measurable, bounded by some `C`, and bounded
by `C |t|^{-5/2}` for `|t| > S`, for some `S > 0`.

Proof route: Fubini in `(u,h)` (absolutely convergent: the kernel integrand is dominated by
`testKernelControl φ · cancellationWeight h`, uniformly in `u`, and vanishes for `u` off the
compact spatial projection) gives `∫ K(u,t) du = κ ∫ (ψ(t) - ψ(t-h)) |h|^{-3/2} dh` with
`ψ(t) = ∫ φ(u,t) du`, a smooth compactly supported function of time with `∫ ψ = 0` and time
support in `[-A,A]`. For `|t| > 2A + 1`, `ψ(t) = 0`, so the value is
`-κ ∫_{-A}^{A} ψ(s) |t-s|^{-3/2} ds = -κ ∫ ψ(s) (|t-s|^{-3/2} - |t|^{-3/2}) ds`
(mean zero), and the mean value theorem bounds the bracket by `C |s| |t|^{-5/2}`. The
global bound follows from `norm_testKernel_le` and the compact spatial projection.
Measurability: `StronglyMeasurable.integral_prod_right'` with `stronglyMeasurable_testKernel`. The proof is `fhpa_spatialIntegral_testKernel_decay_proof`. -/
theorem fhpa_spatialIntegral_testKernel_decay {m : ℕ} (φ : FourierSpace m → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (h0 : ∫ x, φ x = 0) :
    AEStronglyMeasurable (fun t : ℝ => ∫ u : Spatial m,
        testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))) ∧
      ∃ C S : ℝ, 0 < S ∧
        (∀ t : ℝ, ‖∫ u : Spatial m,
          testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))‖ ≤ C) ∧
        ∀ t : ℝ, S < |t| →
          ‖∫ u : Spatial m, testKernel (realCompactTest φ hφ hc) (WithLp.toLp 2 (u, t))‖ ≤
            C * |t| ^ (-5 / 2 : ℝ) := by
  exact fhpa_spatialIntegral_testKernel_decay_proof φ hφ hc h0

/-- **Square-root growth against an `|t|^{-5/2}` tail is integrable.**

If `g : ℝ → ℝ` is continuous with `|g t| ≤ a + b √|t|`, and `f : ℝ → ℂ` is
a.e. strongly measurable with `‖f t‖ ≤ C` everywhere and `‖f t‖ ≤ C |t|^{-5/2}` for
`|t| > S` (`S > 0`), then `t ↦ g(t) f(t)` is integrable on `ℝ`.

Proof route: split `ℝ` into `[-S,S]` (bounded by `(a + b √S) C`, finite measure) and its
complement, where the integrand is bounded by `C (a |t|^{-5/2} + b |t|^{-2})`; both powers are
integrable on `{|t| > S}` (`integrableOn_Ioi_rpow_of_lt` and evenness). Pure real analysis.
The proof is `fhpa_integrable_sqrtGrowth_mul_decay_proof`. -/
theorem fhpa_integrable_sqrtGrowth_mul_decay (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ)
    (hgrowth : ∀ t : ℝ, |g t| ≤ a + b * Real.sqrt |t|) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f) (C S : ℝ) (hS : 0 < S) (hbound : ∀ t : ℝ, ‖f t‖ ≤ C)
    (htail : ∀ t : ℝ, S < |t| → ‖f t‖ ≤ C * |t| ^ (-5 / 2 : ℝ)) :
    Integrable (fun t : ℝ => (g t : ℂ) * f t) := by
  exact fhpa_integrable_sqrtGrowth_mul_decay_proof g hg a b hgrowth f hf C S hS hbound htail

end ParabolicRectifiability.Foundations
