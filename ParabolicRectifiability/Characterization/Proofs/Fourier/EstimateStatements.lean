import ParabolicRectifiability.Foundations.HalfTimeDerivative
import ParabolicRectifiability.Analysis.FourierAffine.Estimate

/-! # Fourier and BMO estimates: statements

Definitions and the four statements used by the vertical and horizontal reference estimates
of the quantitative characterization (proved in `ba1_bmo_growth`,
`ba1_critical_sobolev_localization`, `ba1_fourier_affine_square`, `ba1_spatial_affine_square`):

* `BMOGrowthStatement`: local `L²` bounds and logarithmic mean growth of parabolic BMO
  functions;
* `CriticalSobolevLocalizationStatement`: localization of a Lipschitz function with BMO
  half-time derivative to an `L²` function of bounded parabolic Sobolev energy, at unit scale;
* `FourierAffineSquareStatement`: the parabolic Fourier affine-square inequality;
* `SpatialAffineSquareStatement`: the spatial affine square of a Lipschitz map, in
  quantitative local form.

**Coordinates and measures.** They are those of the vertical and horizontal reference
estimates where the statements are used. A vertical reference has base `Space m = ℝ^m × Time` with `parabolicVolume m` and coordinatewise real
half-derivative bounds `HasCoordinateHalfTimeBMOBound`, read through the ordinary
coordinates `fourierToParabolic m`. Statements 1 and 2 are therefore stated for **real**
functions on `Space m`, with the existing standard-base predicates
`HasStandardParabolicBMOBound` and `RepresentsStandardHalfTimeDerivative`;
statement 3 is stated for real functions on
the Euclidean analytic space `FourierSpace m`, with the existing affine Carleson energy
`FourierAffine.affineCarlesonEnergy` (coordinate
parabolic balls `coordBall`, normalization `r^{-(m+4)} = r^{-k-2}`) and the existing L²
Fourier transform `𝓕 (realLp hH)`. Vector values `ℝ^d` are the coordinatewise case: the
squared Euclidean norm and the best affine fit split over coordinates, so the vector
assertions follow by summing `d` scalar ones; they are applied coordinatewise.
Statement 4 is vector valued, because it is applied to the spatial map `F : ℝ^k → ℝ^n` of a
horizontal reference. All dimensions `m, k, d ∈ ℕ` are allowed, including the base `m = 0`
(one-point spatial factor, constant affine competitors).

**Definitions.** `parabolicFourierEnergy` is the homogeneous
parabolic Sobolev energy `∫ (|ξ|² + |τ|) |Ĥ|²` on the Fourier side; with mathlib's phase
`e^{-2πi⟨x,ζ⟩}` it equals `(4π²)⁻¹ ‖∇_u H‖₂² + ‖|D_t|^{1/2} H‖₂²` (the half-derivative symbol
is the existing `HalfTimeDerivative.symbol`, `|τ|^{1/2}`), the constant `4π²` being absorbed
in the constants of the inequalities. `spatialAffineErrorSq` is the purely spatial squared
affine error `r^{-k-2} inf_{a,B} ∫_{B(u,r)} |F(v) - a - B v|² dv` on `ℝ^k`; the existing
`affineErrorSq` lives on a parabolic base
`E × Time` and does not cover it. Real constants are compared through `ENNReal.ofReal`;
energies are extended nonnegative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal FourierTransform

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations

/- The direct continuity instance `FourierAffine.continuousSMul_fourierSpace`: the generic search
through the `WithLp` product exceeds the heartbeat budget when the L² Fourier transform on
`FourierSpace m` is elaborated. Local to this file. -/
attribute [local instance] FourierAffine.continuousSMul_fourierSpace

/-! ## Definitions -/

/-- The homogeneous parabolic Sobolev energy of a real `H ∈ L²(ℝ^m × ℝ)` on the Fourier side,
`∫ (|ξ|² + |τ|) |Ĥ(ξ,τ)|² dξ dτ ∈ [0,∞]`, where `Ĥ = 𝓕 (realLp hH)` is the L² Fourier
transform of the complexification and `ζ = (ξ,τ)` are the ordinary frequency coordinates of
`FourierSpace m`. With mathlib's phase `e^{-2πi⟨x,ζ⟩}` it equals
`(4π²)⁻¹ ‖∇_u H‖₂² + ‖|D_t|^{1/2} H‖₂²`; the value `⊤` means that one of these is infinite.
The time weight is the one of the existing `fourierAffine_bound`. -/
def parabolicFourierEnergy {m : ℕ} {H : FourierSpace m → ℝ} (hH : MemLp H 2 volume) :
    ℝ≥0∞ :=
  ∫⁻ z, (ENNReal.ofReal (‖(WithLp.ofLp z).1‖ ^ 2) + ENNReal.ofReal |(WithLp.ofLp z).2|) *
    ‖(𝓕 (HalfTimeDerivative.realLp hH) : Lp ℂ 2 (volume : Measure (FourierSpace m))) z‖ₑ ^ 2

/-- The squared spatial affine error of `F : ℝ^k → ℝ^d` at the centre `u` and radius `s`:
`s^{-k-2} inf_{a ∈ ℝ^d, B ∈ L(ℝ^k,ℝ^d)} ∫_{B(u,s)} |F(v) - a - B v|² dv` for `s > 0` (open
Euclidean ball, Lebesgue measure, extended nonnegative integral, no division by ball mass) and
`0` for `s ≤ 0`. This is the integrand of `SpatialAffineSquareStatement`; the affine competitors `v ↦ a + B v` are the same as `v ↦ a' + B(v - u)`. -/
def spatialAffineErrorSq {k d : ℕ} (F : Spatial k → Spatial d) (u : Spatial k) (s : ℝ) :
    ℝ≥0∞ :=
  if 0 < s then
    (ENNReal.ofReal s)⁻¹ ^ (k + 2) *
      ⨅ (a : Spatial d) (B : Spatial k →L[ℝ] Spatial d),
        ∫⁻ v in Metric.ball u s, ‖F v - (a + B v)‖ₑ ^ 2
  else 0

/-! ## The four statements -/

/-- **BMO growth**: local square integrability, the `L²` oscillation
bound and the logarithmic mean growth of a real parabolic-BMO function on `ℝ^m × ℝ`.

There is a constant `C = C_m > 0` such that every real `g` on `Space m` with real parabolic
BMO bound `B` (`HasStandardParabolicBMOBound m g B`: `B ≥ 0`, `g` locally integrable for
`parabolicVolume m`, mean oscillation at most `B` on every parabolic ball `P(p,r)`, `r > 0`,
unrestricted centres) satisfies:
1. `g ∈ L²(P(p,r))` for every ball (local square integrability);
2. `∫_{P(p,r)} |g - g_{P(p,r)}|² ≤ C B² |P(p,r)|` for every ball, `r > 0` (the oscillation
   estimate; parabolic balls are the rectangles `B(x,r) × (t - r², t + r²)`);
3. for concentric balls `0 < ρ ≤ R`,
   `∫_{P(p,R)} |g - g_{P(p,ρ)}|² ≤ C B² (1 + log(R/ρ))² |P(p,R)|` (the mean growth:
   `|g_{P_j} - g_{P_0}| ≤ C_m j B` on dyadic concentric balls, then the
   oscillation estimate on the large ball).

Item 3 is the normalization-free form of the growth bound on `U × [-T,T]`: a ball of radius
`C_U √T` contains `U × [-T,T]`, and the dependence of `C_U` on "one fixed local mean" is the
subtracted mean `g_{P(p,ρ)}`. The averages are the existing `standardBallAverage`. The scalar
statement is the one used (`HasCoordinateHalfTimeBMOBound` is coordinatewise); the vector
version is the sum over coordinates. `m = 0` is included. -/
def BMOGrowthStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (g : Space m → ℝ) (B : ℝ), HasStandardParabolicBMOBound m g B →
      (∀ (p : Space m) (r : ℝ), MemLp g 2 ((parabolicVolume m).restrict (Metric.ball p r))) ∧
      (∀ (p : Space m) (r : ℝ), 0 < r →
        ∫⁻ q in Metric.ball p r, ‖g q - standardBallAverage m g p r‖ₑ ^ 2 ∂parabolicVolume m ≤
          ENNReal.ofReal (C * B ^ 2) * parabolicVolume m (Metric.ball p r)) ∧
      (∀ (p : Space m) (ρ R : ℝ), 0 < ρ → ρ ≤ R →
        ∫⁻ q in Metric.ball p R, ‖g q - standardBallAverage m g p ρ‖ₑ ^ 2 ∂parabolicVolume m ≤
          ENNReal.ofReal (C * B ^ 2 * (1 + Real.log (R / ρ)) ^ 2) *
            parabolicVolume m (Metric.ball p R))

/-- **Critical Sobolev localization**, in quantitative unit-scale form.

There is a constant `C = C_m > 0` with the following property. Let `F` be a real function on
`Space m` which is `L`-Lipschitz for the parabolic metric, and let `f` be a representative of
its homogeneous half-time derivative (`RepresentsStandardHalfTimeDerivative m F f`, the
ordered windowed pairing on total-mean-zero compact tests, read in the ordinary coordinates
`fourierToParabolic m`) with real parabolic BMO bound `B`. Then for every centre `p₀` there
is a real `H ∈ L²(ℝ^m × ℝ)` (in ordinary coordinates) which equals `F - F(p₀)` on the testing
cylinder `P(p₀,2)`, and
`‖H‖₂² + ∫ (|ξ|² + |τ|) |Ĥ|² ≤ C (L² + B²)`,
i.e. `‖H‖₂² + ‖∇_u H‖₂² + ‖|D_t|^{1/2} H‖₂² ≤ C' (L² + B²)`.

"Normalized at unit scale": the testing cylinder has unit size, and `F(p₀)` is
subtracted, so that `|F(p) - F(p₀)| ≤ L d(p,p₀)`. Every parabolic ball `P(p,r)` with
`p ∈ P(p₀,1)`, `r ≤ 1` lies in `P(p₀,2)`, so on all those testing balls `H = F - F(p₀)` and
affine errors of `H` and `F` agree (constants are affine). The intended construction is
`H = χ(u) η(t) (F - F(p₀))` with smooth compact spatial and temporal cutoffs equal to `1` on
the cylinder, and the proof is the high-pass identity
`F = ψ *_t F + K *_t f` with the BMO tail estimates; only the existence of `H` with these
properties is asserted. The centre is arbitrary, so no translation covariance of the
half-time derivative is needed where it is applied. `m = 0` is included (no spatial derivative). -/
def CriticalSobolevLocalizationStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ),
      LipschitzWith L F → HasStandardParabolicBMOBound m f B →
      RepresentsStandardHalfTimeDerivative m F f →
      ∀ p₀ : Space m, ∃ (H : FourierSpace m → ℝ) (hH : MemLp H 2 volume),
        (∀ x : FourierSpace m, fourierToParabolic m x ∈ Metric.ball p₀ 2 →
          H x = F (fourierToParabolic m x) - F p₀) ∧
        (∫⁻ x, ‖H x‖ₑ ^ 2) + parabolicFourierEnergy hH ≤
          ENNReal.ofReal (C * ((L : ℝ) ^ 2 + B ^ 2))

/-- **The parabolic Fourier affine-square inequality.**

There is a constant `C = C_m > 0` such that every real `H ∈ L²(ℝ^m × ℝ)` satisfies
`∫_{ℝ^{m+1}} ∫_0^∞ γ_H(p,r)² dr/r dp ≤ C ∫ (|ξ|² + |τ|) |Ĥ(ξ,τ)|²`,
i.e. `≤ C' (‖∇_u H‖₂² + ‖|D_t|^{1/2} H‖₂²)`, where
`γ_H(p,r)² = r^{-k-2} inf_{a,B} ∫_{P_b(p,r)} |H - a - B·u|²`, `k = m + 2`, is the existing
`FourierAffine.affineEnergy` and the left side is the existing
`FourierAffine.affineCarlesonEnergy H` (all centres, all positive radii, `dr/r`). Both sides
are extended nonnegative; if the right side is infinite the inequality is trivial, so no
derivative hypothesis is needed beyond `H ∈ L²`.

This is the converse of `FourierAffine.fourierAffine_bound` (which bounds the time
part of the right side by the left side). `m = 0` is included: the affine competitor is then a
constant. Vector values are coordinatewise (sum of the scalar inequalities). -/
def FourierAffineSquareStatement : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (H : FourierSpace m → ℝ) (hH : MemLp H 2 volume),
      FourierAffine.affineCarlesonEnergy H ≤ ENNReal.ofReal C * parabolicFourierEnergy hH

/-- **The spatial affine square of a Lipschitz map**, in quantitative local form.

There is a constant `C = C_{k,d} > 0` such that for every `L`-Lipschitz `F : ℝ^k → ℝ^d`, every
centre `b` and every radius `R > 0`,
`∫_{B(b,R)} ∫_0^R r^{-k-2} inf_A ∫_{B(u,r)} |F(v) - A(v)|² dv dr/r du ≤ C L² R^k`,
the infimum over affine maps `A(v) = a + B v`. This is the quantitative form of the a.e.
finiteness of the spatial affine square function (which follows by exhausting `ℝ^k` by balls).
The values are vector valued because it is applied to the spatial map of a horizontal
reference; `k = 0` and `d = 0`
are allowed (trivial). -/
def SpatialAffineSquareStatement : Prop :=
  ∀ k d : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (F : Spatial k → Spatial d) (L : ℝ≥0), LipschitzWith L F →
      ∀ (b : Spatial k) (R : ℝ), 0 < R →
        ∫⁻ u in Metric.ball b R, ∫⁻ s in Ioo 0 R, spatialAffineErrorSq F u s ∂scaleMeasure ≤
          ENNReal.ofReal (C * (L : ℝ) ^ 2 * R ^ k)

end ParabolicRectifiability.Characterization
