import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Characterization.Proofs.Fourier.BMOGrowth
import ParabolicRectifiability.Characterization.Proofs.Fourier.Localization
import ParabolicRectifiability.Characterization.Proofs.Fourier.AffineSquare
import ParabolicRectifiability.Characterization.Proofs.Fourier.SpatialAffineSquare
import ParabolicRectifiability.Foundations.Proofs.HighPass.Assembly

/-! # Fourier and BMO estimates: the four results

Proofs of the four Fourier/BMO statements, each obtained from its proof module:

* `ba1_bmo_growth : BMOGrowthStatement` (used in the proof of
  `ba1_critical_sobolev_localization`);
* `ba1_critical_sobolev_localization : CriticalSobolevLocalizationStatement` and
  `ba1_fourier_affine_square : FourierAffineSquareStatement` (used for the vertical reference
  estimate `ba1_vertical_unit_carleson`);
* `ba1_spatial_affine_square : SpatialAffineSquareStatement` (used for the horizontal reference
  estimate `ba1_horizontal_energy`).
-/

set_option autoImplicit false

namespace ParabolicRectifiability.Characterization

/-- **BMO growth.**

`BMOGrowthStatement` — for a real parabolic-BMO function `g` on `Space m`
with bound `B`: `g ∈ L²` on every parabolic ball, the oscillation bound
`∫_P |g - g_P|² ≤ C_m B² |P|`, and the concentric mean growth
`∫_{P(p,R)} |g - g_{P(p,ρ)}|² ≤ C_m B² (1 + log(R/ρ))² |P(p,R)|`, `0 < ρ ≤ R`.

Proof sketch: parabolic rectangles of spatial side `ℓ` and time side `ℓ²`; each
lies in a comparable parabolic ball of comparable volume, so `⨍_R |g - g_R| ≤ C_m B =: B₀`.
Calderón–Zygmund stopping on the `2^{m+2}` equal children: stopped rectangles have total
volume `≤ |R|/2` and parent means within `2·2^{m+2} B₀`; outside them dyadic differentiation
gives `|g - g_R| ≤ 2B₀` a.e. Iterating gives the geometric tail
`|{z ∈ R : |g - g_R| > 2·2^{m+2}B₀ (j+1)}| ≤ 2^{-j}|R|`, and the layer-cake formula gives
`∫_R |g - g_R|² ≤ C_m B² |R|`. Balls: enclose in a comparable rectangle and compare means.
Item 3: `|g_{P_{j+1}} - g_{P_j}| ≤ C_m B` for radii `2^j ρ` (bounded volume ratio), telescope,
then the oscillation bound on the largest ball. `m = 0` is the time-only case.

Dyadic differentiation is `CoordinateDifferentiationStatement`, applied with `Y = Space m`
embedded isometrically with closed range in `Space (m + 1)` (zero last spatial coordinate), the
finite inner regular measure `(parabolicVolume m).restrict R` and the nested dyadic
subrectangles of `R` (exact Borel partitions, diameters `→ 0`). -/
theorem ba1_bmo_growth : BMOGrowthStatement := by
  exact ba1_bmo_growth_proof

/-- **Critical Sobolev localization** (quantitative unit-scale form).

`CriticalSobolevLocalizationStatement` — for an `L`-Lipschitz real `F` on
`Space m` whose homogeneous half-time derivative has a representative `f` with BMO bound `B`,
and every centre `p₀`, some `H ∈ L²(FourierSpace m)` equals `F - F(p₀)` on `P(p₀,2)` and has
`‖H‖₂² + ∫ (|ξ|² + |τ|) |Ĥ|² ≤ C_m (L² + B²)`.

Proof sketch: put `H = χ(u) η(t) (F - F(p₀))` with fixed smooth
compact cutoffs equal to `1` on `P(p₀,2)`. Normalize `f` to mean zero on a fixed large
cylinder (the kernel annihilates constants). By the high-pass identity
`F - F(p₀) = ψ *_t (F - F(p₀)) + K *_t f` a.e.:
* the low-pass part is `C¹` in time on the support with bounds `C L`;
* the near part `K *_t (1_J f)`: `‖1_J f‖_{L²} ≤ C B` by `BMOGrowthStatement`, and the
  multipliers `K̂`, `|τ|^{1/2} K̂` are bounded, so it lies in `L²_u H^{1/2}_t` with norm `C B`;
* the far part: on time annuli of size `2^j`, `‖1_{annulus} f‖_{L¹_t L²_u} ≤ C B (1+j)
  2^{j(1/2 + (m+2)/4)}` by item 3 of `BMOGrowthStatement`, and the rapid decay of `K`, `K'`
  makes the sum `C¹` in time with bound `C B` on the cylinder.
The Gagliardo identity `∫∫ |v(t) - v(s)|²/|t - s|² = c ∫ |τ| |v̂|²` and the
product estimates for the cutoffs give the temporal half-derivative bound;
spatial Lipschitz gives `|∇_u H| ≤ C L`; Plancherel converts both to
`parabolicFourierEnergy`. For `m = 0` there is no spatial part.

The proof uses `BMOGrowthStatement` and the high-pass kernel facts and identity
(`Foundations.fhp_highPassKernel_facts`, `Foundations.fhp_highPassIdentity`) for one fixed
admissible cutoff, with the a.e. identity transported to `parabolicVolume` for the given
representative. -/
theorem ba1_critical_sobolev_localization : CriticalSobolevLocalizationStatement := by
  exact ba1_critical_sobolev_localization_proof ba1_bmo_growth_proof Foundations.fhp_highPassKernel_facts Foundations.fhp_highPassIdentity

/-- **Parabolic Fourier affine-square inequality.**

`FourierAffineSquareStatement` — for every real `H ∈ L²(ℝ^m × ℝ)`,
`FourierAffine.affineCarlesonEnergy H ≤ C_m ∫ (|ξ|² + |τ|) |Ĥ|²`.

Proof sketch (a parabolic approximate identity): use a mass-one
smoothing, either the Gaussian approximate identity with multiplier `e^{-r²|ξ|² - r⁴τ²}` or
convolution with the existing mass-one `FourierAffine.kernel r` (`integral_kernel = 1`), and
establish the Plancherel identity for the selected mass-one smoothing. Competitor
`a = H_r(p)`, `B = ∇_u H_r(p)`; the scale bound, Plancherel and the two
explicit `dr/r` integrals give an integrated residual multiplier at most `C (|ξ|² + |τ|)`.
The smoothing `FourierAffine.smoothing r` does not work here: it convolves with the
cancellation kernel `scaleKernel r` (`∫ scaleKernel r = 0`), its Taylor competitor has residual
multiplier tending to `1` as `r → 0`, and the scale integral diverges. Prove the estimate first
for Schwartz `H`; then for `H ∈ L²` with finite right side by Fourier truncation and smooth
approximation in the norm with weight `1 + |ξ|² + |τ|`. The square root of the unnormalized
best affine squared error is the distance to the finite-dimensional affine-function subspace
and is `1`-Lipschitz in `L²`. Thus squared errors converge under local `L²` convergence, and
Fatou applies. `m = 0`: the competitor is a constant. -/
theorem ba1_fourier_affine_square : FourierAffineSquareStatement := by
  exact ba1_fourier_affine_square_proof

/-- **Spatial affine square of a Lipschitz map** (quantitative local form).

`SpatialAffineSquareStatement` — for `L`-Lipschitz `F : ℝ^k → ℝ^d`,
`∫_{B(b,R)} ∫_0^R spatialAffineErrorSq F u s ds/s du ≤ C_{k,d} L² R^k`.

Proof sketch: cut off `F - F(b)` by a smooth compact cutoff equal
to `1` on `B(b,2R)` and supported in `B(b,3R)`; the product `G` is in `W^{1,2}` with
`‖∇G‖₂² ≤ C L² R^k`. For `u ∈ B(b,R)` and `s < R` the testing ball `B(u,s)` lies in `B(b,2R)`,
where `G = F - F(b)`, so the affine errors agree. Choose a fixed even smooth mass-one Schwartz
kernel and test the first-order spatial Taylor polynomial of the smoothing `G_s`. The multiplier
of the residual against its spatial Taylor polynomial is bounded by `C min((s|ξ|)², 1)`,
uniformly for spatial increments of length less than `s` (the smoothing multiplier itself
equals one at zero and cannot satisfy that bound). Integrate centres and increments, and use
Plancherel with `∫_0^∞ min((s|ξ|)⁴, 1) s^{-3} ds = C|ξ|²`.
The statement is invariant under translation and dilation of `ℝ^k`, so it suffices to prove
it at `b = 0`, `R = 1` and rescale. Coordinates of `ℝ^d` separate. -/
theorem ba1_spatial_affine_square : SpatialAffineSquareStatement := by
  exact ba1_spatial_affine_square_proof

end ParabolicRectifiability.Characterization
