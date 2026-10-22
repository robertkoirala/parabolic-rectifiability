import ParabolicRectifiability.Foundations.HalfTimeDerivative

/-! # Integrability of the spatial bracket for parabolic Lipschitz functions

The proposition `HalfTimeBracketIntegrableStatement`. The proof splits the bracket into a
difference term `[G(u,t) - G(u₀,t)] |D_t|^{1/2}φ` with an `O(|t|^{-3/2})` tail, plus
`G(u₀,t) |D_t|^{1/2}ψ(t)`, `ψ(t) = ∫ φ(u,t) du`, with an `O((1+√|t|) |t|^{-5/2})` tail; thus the
bracket is in `L¹(dt)`. The pairing and its bracket are formalized as
`halfTimeSpatialIntegrand` and `halfTimeSpatialBracket`.

Conventions.
* Ordinary coordinates `FourierSpace m = ℝ^m × ℝ` with Lebesgue measure; all `m`, including
  the zero-dimensional spatial case `m = 0`.
* "Globally parabolic Lipschitz with bound `L`" is
  `LipschitzWith L` for the parabolic metric of `Space m`
  (`max (‖u - u'‖, √|t - t'|)`), read through `fourierToParabolic m`. This is the convention
  of `HasHalfTimeBMOBound`, and it is exactly what each
  orthonormal normal component `normalFourierComponent W F i` of a `LipschitzWith L F` on a
  vertical base `SubspaceSpace W` satisfies (`m = finrank W`): `subspaceFourierToParabolic W`
  composed with `(fourierToParabolic m).symm` is the inverse of the isometry
  `subspaceParabolicIsometry W`, and an orthonormal coordinate is `1`-Lipschitz.
* Tests are real smooth compactly supported functions of total integral zero, complexified by
  `realCompactTest`, as in `RepresentsHomogeneousHalfTimeDerivative`.
* The conclusion is the inner clause of `RepresentsHomogeneousHalfTimeDerivative` together
  with integrability of the bracket on the whole time line (which implies its window clause).
  Absolute integrability on the product is not asserted (it fails for some `G`).
-/

noncomputable section

open MeasureTheory
open scoped NNReal ContDiff

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

/-- **The spatial bracket of a parabolic Lipschitz function is in `L¹(dt)`.**

For every `m` (including `m = 0`), every `G : ℝ^m × ℝ → ℝ` that is globally parabolic
Lipschitz (`LipschitzWith L` for the parabolic metric of `Space m`, read through
`fourierToParabolic m`), and every real smooth compactly supported test `φ` with `∫ φ = 0`:
* for a.e. time `t`, the spatial integrand `u ↦ G(u,t) (|D_t|^{1/2}φ)(u,t)` is integrable;
* the spatial bracket `t ↦ ∫ G(u,t) (|D_t|^{1/2}φ)(u,t) du` is integrable on `ℝ`.

It is used in the time-translation stage of the similarity covariance of the homogeneous
half-time derivative, and in the weighted pairing estimate and the high-pass identity
(`HighPassWeightedPairingStatement`, `HighPassIdentityStatement`). -/
def HalfTimeBracketIntegrableStatement : Prop :=
  ∀ (m : ℕ) (G : FourierSpace m → ℝ),
    (∃ L : ℝ≥0, LipschitzWith L (G ∘ (fourierToParabolic m).symm)) →
    ∀ (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ∫ x, φ x = 0 →
        (∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G (realCompactTest φ hφ hc) t)) ∧
        Integrable (halfTimeSpatialBracket G (realCompactTest φ hφ hc))

end ParabolicRectifiability.Foundations
