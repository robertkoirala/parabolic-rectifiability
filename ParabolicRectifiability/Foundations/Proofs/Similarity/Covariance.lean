import ParabolicRectifiability.Foundations.Statements.HighPassBracket
import ParabolicRectifiability.Decomposition.Carrier.Definitions
import ParabolicRectifiability.Foundations.Proofs.Similarity.HalfTimeCovariance
import ParabolicRectifiability.Foundations.Proofs.Similarity.LipschitzSimilarity

/-! # Similarity covariance of the half-time derivative and of the parabolic Lipschitz bound

Covariance of the homogeneous half-time representative under dilation
(`fsim_representsHomogeneousHalfTimeDerivative_dilation`) and time translation
(`fsim_representsHomogeneousHalfTimeDerivative_timeShift`), and invariance of the parabolic
Lipschitz constant under a base similarity (`fsim_lipschitzWith_baseSimilarity`). They are
assembled into the covariance of the general regular class under the base similarity
`σ = baseSimilarity W (0, t₀) R`, `σ(u,t) = (R⁻¹ u, R⁻² (t - t₀))`, used for the vertical
graphs in the scaling of the quantitative characterization.

For `G_{a,r}(u,t) = r⁻¹ G(a_u + r u, a_t + r² t)` the representative is
`g(a_u + r u, a_t + r² t)`, and `Lip_P G_{a,r} = Lip_P G`. Here `r = R⁻¹`, `a = (0, -R⁻² t₀)`.

The proof of the representation is split in two stages, both scalar, on ordinary
coordinates `FourierSpace m`, so they serve every consumer of
`RepresentsHomogeneousHalfTimeDerivative` (vertical bases componentwise, the standard base
through `fourierToParabolic`):
* **dilation, no translation**, needs no hypothesis on `G`: the symmetric windows
  `[-T,T]` become `[-T/R², T/R²]`, still symmetric.
* **time translation** moves the windows to `[-T - t₀, T - t₀]`; the limits agree
  because the bracket is in `L¹(dt)`, which is `HalfTimeBracketIntegrableStatement`, taken as
  a hypothesis (implication form) and proved by `fhpa_halfTimeBracketIntegrable`.

The BMO part of the Lipschitz/BMO invariance is `hasParabolicBMOBound_baseSimilarity_proof`;
only the Lipschitz part is stated here.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ParabolicRectifiability.Foundations

/-- **Dilation covariance of the homogeneous half-time representative**
(with `a = 0`, `r = R⁻¹` in the scaling formula above).

For `R > 0`, if `g` represents the homogeneous half-time derivative of `G` on
`ℝ^m × ℝ` (`RepresentsHomogeneousHalfTimeDerivative`, any `m`), then `g ∘ δ` represents that of
`R · G ∘ δ`, where `δ(u,t) = (R⁻¹ u, R⁻² t)`. No Lipschitz or other hypothesis on `G`.

Proof route (all kernel identities only almost everywhere, as `testKernel_ae_halfTimeDeriv`).
Local integrability of `g ∘ δ`: `δ` is a linear equivalence (Jacobian `R^{-(m+2)}`). For a test
`φ ∈ D₀`, put `φ_R(v,s) = φ(R v, R² s)` (`φ_R ∈ D₀`). Kernel covariance:
`(|D_t|^{1/2}φ)(u,t) = R⁻¹ (|D_t|^{1/2}φ_R)(R⁻¹u, R⁻²t)` a.e. (substitute `h = R² h'` in
the kernel formula for `testKernel`, then transfer a.e. to `halfTimeDeriv`).
Hence the integrand of `(R·G∘δ, φ)` at time `t` equals that of `(G, φ_R)` at `R⁻² t`,
evaluated at `R⁻¹ u` (a.e. `t`, a.e. `u`): the inner clause transfers; the bracket is
`R^m` times the bracket of `(G, φ_R)` at `R⁻² t`; window integrability transfers with
`[-T,T] ↦ [-R⁻²T, R⁻²T]`; the window pairing at `T` is `R^{m+2}` times the pairing of
`(G, φ_R)` at `R⁻² T` (`Tendsto` composed with `T ↦ R⁻² T → ∞`); finally
`R^{m+2} ∫ g φ_R = ∫ (g ∘ δ) φ` (change of variables). The proof is
`fsim_representsHomogeneousHalfTimeDerivative_dilation_proof`. -/
theorem fsim_representsHomogeneousHalfTimeDerivative_dilation {m : ℕ} (R : ℝ) (hR : 0 < R)
    (G g : FourierSpace m → ℝ) (h : RepresentsHomogeneousHalfTimeDerivative G g) :
    RepresentsHomogeneousHalfTimeDerivative
      (fun x => R * G (WithLp.toLp 2 (R⁻¹ • (WithLp.ofLp x).1, R⁻¹ ^ 2 * (WithLp.ofLp x).2)))
      (fun x => g (WithLp.toLp 2 (R⁻¹ • (WithLp.ofLp x).1, R⁻¹ ^ 2 * (WithLp.ofLp x).2))) := by
  exact fsim_representsHomogeneousHalfTimeDerivative_dilation_proof R hR G g h

/-- **Time-translation covariance of the homogeneous half-time representative**
(fixed translations in time preserve it; the scaling formula with `a = (0, -t₀)`, `r = 1`).

Hypotheses: `HalfTimeBracketIntegrableStatement` (implication form) and `G` parabolic
Lipschitz in the convention of that statement. If `g` represents the
homogeneous half-time derivative of `G`, then `g ∘ τ` represents that of `G ∘ τ`, where
`τ(u,t) = (u, t - t₀)`.

Proof route. Local integrability: `τ` preserves volume. For `φ ∈ D₀` put
`ψ(u,s) = φ(u, s + t₀)` (`ψ ∈ D₀`); the test kernel commutes with time translation
(`testKernel` is translation covariant pointwise; transfer a.e. to `halfTimeDeriv`), so the
integrand of `(G∘τ, φ)` at time `t` is that of `(G, ψ)` at `t - t₀`, a.e. Thus the inner
clause and window integrability transfer, and the window pairing at `T` equals
`∫_{[-T-t₀, T-t₀]} b_ψ`, with `b_ψ` the bracket of `(G, ψ)`. By the hypothesis, `b_ψ ∈ L¹(ℝ)`, so both
`∫_{[-T-t₀,T-t₀]} b_ψ` and `∫_{[-T,T]} b_ψ` tend to `∫_ℝ b_ψ` (dominated convergence or
`intervalIntegral_tendsto_integral`); the latter tends to `∫ g ψ` by `h`, and
`∫ g ψ = ∫ (g ∘ τ) φ` (translation). The proof is
`fsim_representsHomogeneousHalfTimeDerivative_timeShift_proof`. -/
theorem fsim_representsHomogeneousHalfTimeDerivative_timeShift
    (hhp : HalfTimeBracketIntegrableStatement) {m : ℕ} (t₀ : ℝ) (G g : FourierSpace m → ℝ)
    (hG : ∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm))
    (h : RepresentsHomogeneousHalfTimeDerivative G g) :
    RepresentsHomogeneousHalfTimeDerivative
      (fun x => G (WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2 - t₀)))
      (fun x => g (WithLp.toLp 2 ((WithLp.ofLp x).1, (WithLp.ofLp x).2 - t₀))) := by
  exact fsim_representsHomogeneousHalfTimeDerivative_timeShift_proof hhp t₀ G g hG h

/-- **Invariance of the parabolic Lipschitz constant under a base similarity**
(`Lip_P G_{a,r} = Lip_P G`).

For `R > 0`, any centre `p₀` of the vertical base `W × ℝ` and any
`F : W × ℝ → Wᗮ`, if `F` is `L`-Lipschitz for the max parabolic metric then so is
`p ↦ R • F (baseSimilarity W p₀ R p)`, `baseSimilarity W p₀ R p = (R⁻¹(u - u₀), R⁻²(t - t₀))`.

Proof route: `dist_baseSimilarity` gives
`d(σ p, σ q) = R⁻¹ d(p, q)`; `‖R • v‖ = R ‖v‖`; `LipschitzWith.of_dist_le_mul`.
The BMO half of the invariance is `hasParabolicBMOBound_baseSimilarity_proof` (base centre
`(0, t₀)`; image volumes `λ(σ A) = R^{-(m+2)} λ(A)`, pushforward `σ_# λ = R^{m+2} λ`,
`map_baseSimilarityHomeomorph`). The proof of the present statement is
`fsim_lipschitzWith_baseSimilarity_proof`. -/
theorem fsim_lipschitzWith_baseSimilarity {n : ℕ} (W : Submodule ℝ (Spatial n))
    (p₀ : SubspaceSpace W) (R : ℝ) (hR : 0 < R) (F : SubspaceSpace W → W.orthogonal) (L : ℝ≥0)
    (hF : LipschitzWith L F) :
    LipschitzWith L (fun p => R • F (baseSimilarity W p₀ R p)) := by
  exact fsim_lipschitzWith_baseSimilarity_proof W p₀ R hR F L hF

end ParabolicRectifiability.Foundations
