import ParabolicRectifiability.Analysis.ParabolicBMO

/-! # The general homogeneous half-time derivative and the general regular class

Definitions only. They express the homogeneous half-time derivative of a function
(its representation clause) and the general regular class of vertical graph functions.

* Tests are real smooth compactly supported functions on the ordinary Euclidean
  coordinates `FourierSpace m` (spatial `ℝ^m` times ordinary time `ℝ`) with total
  integral zero. Smoothness never refers to snowflaked time.
* The half derivative of a test is `halfTimeDeriv` (phase
  `e^{-2πi(u·ξ+tτ)}`, symbol `|τ|^{1/2}`) applied to the test as a complex Schwartz
  function. No second Fourier convention is introduced.
* The pairing integrates in space first, then over the common time window `[-R,R]`,
  and then takes the limit `R → ∞`. Absolute integrability on the product is not
  assumed, and the limit is expressed by `Tendsto`, so no existence theorem is used.
* Because Bochner integrals of non-integrable functions are `0`, the representation
  predicate requires, for each test, that the inner spatial integrand is integrable for
  a.e. time and that the spatial bracket is integrable on every finite window. Without
  these clauses a non-locally-integrable `G` could have every window pairing equal to
  `0` and be represented by `g = 0`. Integrability on the whole
  product is deliberately not required (there is a Lipschitz counterexample).
* Functions on a vertical base `SubspaceSpace W` are tested componentwise in the
  orthonormal normal coordinates `normalFourierComponent`, as in
  `RepresentsHalfTimeDerivative`. The BMO seminorm is the existing vector
  `HasParabolicBMOBound`.

There is no compact-support or `L²` condition. The same derivative, with the real
parabolic BMO seminorm, is also given for real functions on the standard base
`Space m`, for the vertical reference models; there the public bound also requires `F` to be
parabolic Lipschitz.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology ContDiff SchwartzMap

namespace ParabolicRectifiability.Foundations

open ParabolicRectifiability.HalfTimeDerivative

variable {n m : ℕ}

/-- The spatial integrand of the ordered pairing at time `t`:
`u ↦ G(u,t) (|D_t|^{1/2}ψ)(u,t)` on `ℝ^m`. -/
def halfTimeSpatialIntegrand (G : FourierSpace m → ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) (t : ℝ)
    (u : Spatial m) : ℂ :=
  (G (WithLp.toLp 2 (u, t)) : ℂ) * halfTimeDeriv m ψ (WithLp.toLp 2 (u, t))

/-- The spatial bracket of the ordered pairing: `t ↦ ∫_{ℝ^m} G(u,t) (|D_t|^{1/2}ψ)(u,t) du`. -/
def halfTimeSpatialBracket (G : FourierSpace m → ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) (t : ℝ) : ℂ :=
  ∫ u : Spatial m, halfTimeSpatialIntegrand G ψ t u

/-- The ordered windowed pairing, before the limit:
`∫_{[-R,R]} [∫_{ℝ^m} G(u,t) (|D_t|^{1/2}ψ)(u,t) du] dt`.
The inner spatial integral and the common time window are part of the definition.
Changing the representative of the `L²` class `halfTimeDeriv m ψ` on a null set changes
the inner integral only for a null set of times, so the value is well defined. -/
def halfTimeWindowPairing (G : FourierSpace m → ℝ) (ψ : 𝓢(FourierSpace m, ℂ)) (R : ℝ) : ℂ :=
  ∫ t in Set.Icc (-R) R, halfTimeSpatialBracket G ψ t

/-- Scalar representation of the homogeneous half-time derivative in ordinary
coordinates:
`g` is locally integrable and, for every real compact smooth test `φ` of total
integral zero,
* for a.e. time `t` the spatial integrand `u ↦ G(u,t) (|D_t|^{1/2}φ)(u,t)` is integrable;
* for every `R` the spatial bracket is integrable on `[-R,R]`;
* the ordered pairing `T_G(φ)` converges to `∫ g φ`.

The two integrability clauses make the ordered pairing a genuine iterated integral: without
them a Bochner integral of a non-integrable function is `0`, and a non-locally-integrable
`G` would be represented by `g = 0`. The inner clause is needed
separately, since junk inner integrals could make the bracket identically `0`. Absolute
integrability on the whole product is deliberately not required: it fails for some
parabolic Lipschitz `G`. For parabolic Lipschitz `G` both
clauses hold. -/
def RepresentsHomogeneousHalfTimeDerivative (G g : FourierSpace m → ℝ) : Prop :=
  LocallyIntegrable g volume ∧
    ∀ (φ : FourierSpace m → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      ∫ x, φ x = 0 →
        (∀ᵐ t : ℝ, Integrable (halfTimeSpatialIntegrand G (realCompactTest φ hφ hc) t)) ∧
        (∀ R : ℝ, IntegrableOn (halfTimeSpatialBracket G (realCompactTest φ hφ hc))
          (Set.Icc (-R) R)) ∧
        Tendsto (halfTimeWindowPairing G (realCompactTest φ hφ hc)) atTop
          (𝓝 (∫ x, (g x : ℂ) * (φ x : ℂ)))

/-- Vector representation on a vertical base: each orthonormal normal component of `g` represents the
homogeneous derivative of the same component of `G`, in the ordinary coordinates of
`SubspaceSpace W`. The convention is that of `RepresentsHalfTimeDerivative`. -/
def RepresentsGeneralHalfTimeDerivative (W : Submodule ℝ (Spatial n))
    (G g : SubspaceSpace W → W.orthogonal) : Prop :=
  ∀ i : Fin (Module.finrank ℝ W.orthogonal),
    RepresentsHomogeneousHalfTimeDerivative (normalFourierComponent W G i)
      (normalFourierComponent W g i)

/-- General regular vertical function on the vertical base `W × ℝ`:
a parabolic Lipschitz bound `L`, a representative `g` of the homogeneous derivative with
vector parabolic BMO bound `B`, and `L + B ≤ ε`. There is no compact-support or `L²`
condition. If the normal space is zero, the representation is vacuous. -/
def IsGeneralRegularVerticalFunction (W : Submodule ℝ (Spatial n))
    (G : SubspaceSpace W → W.orthogonal) (ε : ℝ) : Prop :=
  ∃ (g : SubspaceSpace W → W.orthogonal) (L B : ℝ≥0),
    LipschitzWith L G ∧ HasParabolicBMOBound W g (B : ℝ) ∧
      RepresentsGeneralHalfTimeDerivative W G g ∧ (L : ℝ) + (B : ℝ) ≤ ε

/-! ## Real functions on the standard base `Space m`

The base `ℝ^m × ℝ` of a vertical reference model carries the parabolic metric of
`Space m` and the coordinate volume `parabolicVolume m`. The derivative is the same
scalar `RepresentsHomogeneousHalfTimeDerivative`, read through the ordinary coordinates
`fourierToParabolic m`. -/

/-- The average of a real function over a parabolic ball of `Space m`. Only positive
radii are used below. -/
def standardBallAverage (m : ℕ) (g : Space m → ℝ) (p : Space m) (r : ℝ) : ℝ :=
  ((parabolicVolume m (Metric.ball p r)).toReal)⁻¹ •
    ∫ q in Metric.ball p r, g q ∂parabolicVolume m

/-- A real parabolic BMO bound on the standard base, with local integrability stated
explicitly (the seminorm over unrestricted centres and positive radii). -/
def HasStandardParabolicBMOBound (m : ℕ) (g : Space m → ℝ) (B : ℝ) : Prop :=
  0 ≤ B ∧ LocallyIntegrable g (parabolicVolume m) ∧
    ∀ p r, 0 < r →
      (∫ q in Metric.ball p r, ‖g q - standardBallAverage m g p r‖ ∂parabolicVolume m) /
          (parabolicVolume m (Metric.ball p r)).toReal ≤ B

/-- Representation of the homogeneous half-time derivative of a real function on the
standard base, read in ordinary coordinates. -/
def RepresentsStandardHalfTimeDerivative (m : ℕ) (F f : Space m → ℝ) : Prop :=
  RepresentsHomogeneousHalfTimeDerivative (fun x => F (fourierToParabolic m x))
    (fun x => f (fourierToParabolic m x))

/-- `[|D_t|^{1/2}F]_{BMO_P} ≤ B` for a real function on the standard base: `F` is
parabolic Lipschitz with some constant, and some representative of the homogeneous
derivative has real parabolic BMO bound `B`.

The Lipschitz clause is the admissibility condition of the derivative;
without it the predicate would admit spurious non-locally-integrable `F`. Its constant is
existential and is **not** charged against `B`: the Lipschitz constant and the BMO
seminorm are bounded separately. -/
def HasHalfTimeBMOBound (m : ℕ) (F : Space m → ℝ) (B : ℝ) : Prop :=
  (∃ L : ℝ≥0, LipschitzWith L F) ∧
    ∃ f : Space m → ℝ, HasStandardParabolicBMOBound m f B ∧
      RepresentsStandardHalfTimeDerivative m F f

/-- `max_α [|D_t|^{1/2}F^α]_{BMO_P} ≤ B` for the Euclidean coordinates of
`F : ℝ^m × ℝ → ℝ^d`: every coordinate satisfies the
real bound, so in particular every coordinate is parabolic Lipschitz (with its own
existential constant, not charged against `B`). -/
def HasCoordinateHalfTimeBMOBound (m d : ℕ) (F : Space m → EuclideanSpace ℝ (Fin d))
    (B : ℝ) : Prop :=
  ∀ α : Fin d, HasHalfTimeBMOBound m (fun z => F z α) B

end ParabolicRectifiability.Foundations
