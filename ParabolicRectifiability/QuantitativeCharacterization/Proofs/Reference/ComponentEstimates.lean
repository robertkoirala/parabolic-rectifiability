import ParabolicRectifiability.QuantitativeCharacterization.Statements.Geometry
import ParabolicRectifiability.Characterization.Proofs.Fourier.Estimates
import ParabolicRectifiability.Foundations.Proofs.AmbientEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceBasic
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalADR
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceADRVertical
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.ReferenceDilation
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.VerticalCarleson
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.VerticalBetaEnergy
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalBeta
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalInterpolation
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalCoarse
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalFine
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalTemporalEnergy
import ParabolicRectifiability.Analysis.TraceExtension.AffineError
import ParabolicRectifiability.Characterization.Proofs.Fourier.EstimateStatements
import ParabolicRectifiability.Foundations.Statements.Ambient

/-! # Reference estimates: the component statements

This module proves the statements below `reference_estimates : ReferenceEstimatesStatement`:
uniform ADR bounds and own-type Carleson energy bounds for horizontal, vertical and ambient
references, together with the basic facts about references (measurability, closed carrier, locally
Radon measure). They are assembled into `ba1_reference_estimates` in the assembly module.

The first four statements are inputs, proved elsewhere (`Characterization` and `Foundations`):
critical Sobolev localization, the Fourier affine square estimate, the spatial affine square
estimate and the vanishing of the ambient energy at `k = n + 2`. The component estimates
cover the generic vertical estimate, the whole horizontal completion and the ambient endpoint;
the horizontal time restriction `|T(v) - T(u)| < r²` is kept.

**Wiring.** A statement that needs a sibling's result takes that result as an explicit hypothesis,
with the sibling's conclusion type; the assembly discharges every such hypothesis with
the sibling result. No statement assumes an ADR bound, an energy bound or any other conclusion of
`reference_estimates`.

**Reduction to unit scale (vertical).** Directly at every scale, for the base function: the
localization input is stated at unit scale for every centre, so no translation covariance is
needed; `ba1_standard_dilation` supplies the dilation covariance of the standard-base
half-time derivative, and `traceErrorSq_similarity_proof`
the exact scaling of affine errors. Dilations
about the origin keep the time windows `[-T,T]` symmetric, so no bracket
integrability is used. No invariance of `VerticalReference` itself is needed.

Conventions: `Space m = ℝ^m × Time` with `parabolicVolume m`; `affineErrorSq`,
`affineCarlesonIntegral`, `HasAffineCarlesonBound` are the definitions of the
trace-extension affine error (normalization `s^{-(m+4)} = s^{-k-2}`);
`Characterization.spatialAffineErrorSq` is the purely spatial error of the Fourier statements. The horizontal temporal cost written out in
the horizontal statements is

`τ_L(u,r) = r^{-k-2} ∫_{|v-u| < L r, |T(v) - T(u)| < r²} |T(v) - T(u)| dv`, with the actual
parabolic time restriction. The side of the Whitney cube `Q_i` is
`ℓ_i = λ 2^{j_i}` (`gridScale * 2 ^ cubeLevel i`). Real constants are compared through
`ENNReal.ofReal`; energies are extended nonnegative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ParabolicRectifiability.QuantitativeCharacterization

open ParabolicRectifiability.Foundations

/-! ## Input statements -/

/-- **Critical Sobolev localization** (quantitative form):
`Characterization.CriticalSobolevLocalizationStatement`, an input proved by
`Characterization.ba1_critical_sobolev_localization`. -/
theorem ba1_input_localization : Characterization.CriticalSobolevLocalizationStatement := by
  exact Characterization.ba1_critical_sobolev_localization

/-- **Fourier affine square estimate**:
`Characterization.FourierAffineSquareStatement`, an input proved by
`Characterization.ba1_fourier_affine_square`. -/
theorem ba1_input_fourierAffineSquare : Characterization.FourierAffineSquareStatement := by
  exact Characterization.ba1_fourier_affine_square

/-- **Spatial affine square estimate**:
`Characterization.SpatialAffineSquareStatement`, an input proved by
`Characterization.ba1_spatial_affine_square`. -/
theorem ba1_input_spatialAffineSquare : Characterization.SpatialAffineSquareStatement := by
  exact Characterization.ba1_spatial_affine_square

/-- **Vanishing ambient energy** (first clause):
`Foundations.AmbientEnergyZeroStatement`, an input proved as
`Foundations.ambient_energy_zero`. -/
theorem ba1_input_ambientEnergyZero : AmbientEnergyZeroStatement := by
  exact fun n hn μ _ _ T hT => Foundations.ambient_betaSq_squareEnergy_eq_zero_proof n hn μ T hT

/-! ## Basic reference facts (item 1, first part) -/

/-- **Basic facts of horizontal references.**

For `1 ≤ L` and every horizontal `L`-reference `H` (map `u ↦ (F(u),T(u))`,
`σ = (F,T)_# L^k`, `Γ = supp σ`): the map is Borel measurable, the carrier is closed, and `σ`
is locally Radon (finite on compacts and inner regular).

Proof sketch: `F` is Lipschitz; `T` is `τ` on the compact `D` (continuous there by the
quadratic trace bound) and constant on each of the countably many Borel faces, which
partition `Dᶜ`, so `T` is Borel and so is `(F,T)` (`point`). The carrier is a support, hence
closed (`Measure.isClosed_support`). For compact `K`, `(F,T)⁻¹ K ⊆ F⁻¹(π₁ K)` is bounded
because `|u - v| ≤ L |F(u) - F(v)|`, so `σ(K) < ∞`; a locally finite Borel measure on the
proper (Polish, σ-compact) space `X` is inner regular.


-/
theorem ba1_horizontal_basic :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular := by
  exact ba1_horizontal_basic_proof

/-- **Basic facts of vertical references** (completeness and the lower
Lipschitz bound make `Γ` closed).

For `1 ≤ L` and every vertical `L`-reference `V` (`Φ(p) = (F(p), t)`,
`σ = Φ_# L^{m+1}`, `Γ = Φ(ℝ^m × ℝ)`): `Φ` is a measurable embedding, `Γ` is closed and equals
`supp σ`, and `σ` is locally Radon.

Proof sketch: `Φ` is `L`-bi-Lipschitz for the parabolic metrics, hence a closed embedding of
the complete space `Space m` (Cauchy images have Cauchy preimages), so a measurable embedding
with closed range. `σ(A) = L^{m+1}(Φ⁻¹ A)` for every set; `Φ⁻¹(P(Φp, r)) ⊇ P(p, r/L)` has
positive volume, so every point of `Γ` is in the support, and the complement of the closed
`Γ` is `σ`-null. Compact sets have bounded preimages, so `σ` is finite on compacts and,
being locally finite on a proper space, inner regular. Only the fields `rank_eq` and
`bilipschitz` are used; the BMO field is not.


-/
theorem ba1_vertical_basic :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular := by
  exact ba1_vertical_basic_proof

/-- **Basic facts of the ambient reference** (at `k = n + 2` the reference is
`(X, L^{n+1})`).

`parabolicVolume n` is inner regular and its support is all of `X`
(finiteness on compacts is the existing instance `parabolicVolume_finiteOnCompacts`).

Proof sketch: `parabolicVolume n` is the image of Lebesgue measure under the coordinate
homeomorphism; Lebesgue measure is an inner regular Haar measure and
inner regularity transfers along homeomorphisms (mathlib `Measure.InnerRegular.map`-type
lemmas); every open ball has positive volume `2 ω_n r^{n+2}` (`parabolicVolume_ball`), so the
support is `univ`.


-/
theorem ba1_ambient_basic :
    ∀ n : ℕ, (parabolicVolume n).InnerRegular ∧ (parabolicVolume n).support = Set.univ := by
  exact ba1_ambient_basic_proof

/-! ## ADR bounds -/

/-- **Uniform ADR of horizontal references.**

For `1 ≤ L` there is `A ≥ 1`, depending only on `(n,k,L)`, such that the
natural measure `σ = (F,T)_# L^k` of every horizontal `L`-reference is globally `k`-ADR:
`A⁻¹ r^k ≤ σ(P(z,r)) ≤ A r^k` for `z ∈ supp σ`, `r > 0`.

Proof sketch: the support is the trace `{(F(a), τ(a)) : a ∈ D}` together with the
closed plateau faces `{(F(u), τ(a_Q)) : u ∈ Q}`, each **closed** cube `Q` taken at its own
plateau height `τ(a_Q)` (not the image `H.map '' Q`; a boundary point of `Q` whose face is
assigned to a neighbour still appears at height `τ(a_Q)`) (properness of `F`, Whitney local
finiteness; anchors of nearby cubes converge, so no other limiting height occurs). Upper bound: the
preimage of `P(z,r)` lies in a spatial ball of radius `L r`. Lower bound at a trace point
`(F(a), τ(a))`: nearby anchors satisfy `|a_Q - a| ≤ C|u - a|`, so
`|F(u) - F(a)| ≤ L|u - a|` and `|T(u) - τ(a)| ≤ C L² |u - a|²`, and a base ball of
radius `c r` maps into `P(z,r)`. Lower bound at a plateau point: for `r ≲ ℓ_Q` the inward cube
sector at the point (in `int Q ⊆ face Q`, height `τ(a_Q)`) has volume `≥ c r^k` and constant
time; for `r ≫ ℓ_Q` use the anchor
trace point at distance `C ℓ_Q`. Countably many faces are null for `L^k`.

Hypotheses: the conclusion of `ba1_horizontal_basic` (measurability of the map, for
`σ(A) = L^k((F,T)⁻¹ A)` on Borel sets), as stated.

-/
theorem ba1_horizontal_adr
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ H : HorizontalReference n k L, IsADR A k H.measure := by
  exact ba1_horizontal_adr_proof hbasic

/-- **Uniform ADR of vertical references** (the pushforward of `du dt`
under a bi-Lipschitz map is uniformly ADR).

For `1 ≤ L` there is `A ≥ 1`, depending only on `(k,L)`, such that
`σ = Φ_# L^{m+1}` is globally `k`-ADR for every vertical `L`-reference.

Proof sketch: `supp σ = Γ = Φ(ℝ^m × ℝ)`; for `z = Φ(p)`,
`P_b(p, r/L) ⊆ Φ⁻¹ P(z,r) ⊆ P_b(p, L r)` by the bi-Lipschitz bounds, and
`L^{m+1}(P_b(p,s)) = 2 ω_m s^{m+2}` (`parabolicVolume_ball`, `m + 2 = k`). Hence
`2 ω_m L^{-k} r^k ≤ σ(P(z,r)) ≤ 2 ω_m L^k r^k`. Only the bi-Lipschitz field is used: this is
the ADR of the pushforward under any time-preserving bi-Lipschitz map.

Hypotheses: the conclusion of `ba1_vertical_basic`, as stated.

-/
theorem ba1_vertical_adr
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ V : VerticalReference n k L, IsADR A k V.measure := by
  exact ba1_vertical_adr_proof hbasic

/-- **ADR of the ambient reference** (the only model is `X` with ambient
volume).

`parabolicVolume n` is globally `(n+2)`-ADR with some constant `A ≥ 1`.

Proof sketch: `parabolicVolume n (P(z,r)) = 2 ω_n r^{n+2}` exactly (`parabolicVolume_ball`);
take `A = max (2 ω_n) (2 ω_n)⁻¹` (and `≥ 1`), with `ω_n = (omega n).toReal ∈ (0,∞)`.


-/
theorem ba1_ambient_adr :
    ∀ n : ℕ, ∃ A : ℝ, 1 ≤ A ∧ IsADR A (n + 2) (parabolicVolume n) := by
  exact ba1_ambient_adr_proof

/-! ## Vertical references: the generic regular-vertical estimate -/

/-- **Dilation covariance on the standard base** (dilation part only).

For `ρ > 0`, `δ_ρ(u,t) = (ρu, ρ²t)` (`dilate ρ`) on `Space m`, and
`F_ρ = ρ⁻¹ F ∘ δ_ρ`, `f_ρ = f ∘ δ_ρ`: (1) `F` `L`-Lipschitz implies `F_ρ` `L`-Lipschitz;
(2) a real parabolic BMO bound `B` of `f` is one of `f_ρ`; (3) if `f` represents the
homogeneous half-time derivative of `F` (ordinary coordinates, windowed pairing), then `f_ρ`
represents that of `F_ρ`.

Proof sketch: (1) `d(δ_ρ p, δ_ρ q) = ρ d(p,q)` (`dist_dilate`). (2) `δ_ρ` maps `P(p,r)` onto
`P(δ_ρ p, ρr)` and multiplies `parabolicVolume m` by `ρ^{m+2}` (`map_dilate_parabolicVolume`),
so averages and mean oscillations are preserved; local integrability is preserved.
(3) For a test `φ` put `φ^ρ = φ ∘ δ_ρ⁻¹` (compact, smooth, total integral zero); the symbol
`|τ|^{1/2}` gives `|D_t|^{1/2}(φ ∘ δ_{1/ρ}) = ρ⁻¹ (|D_t|^{1/2} φ) ∘ δ_{1/ρ}` a.e. Substitute
`q = δ_ρ p` (spatial `x = ρ u`, time `t = ρ² s`); the Jacobian factor `ρ^{-(m+2)}` appears
explicitly in the identities
`∫ f_ρ φ = ρ^{-(m+2)} ∫ f (φ ∘ δ_{1/ρ})` and
`Window(F_ρ, φ, T) = ρ^{-(m+2)} Window(F, φ ∘ δ_{1/ρ}, ρ² T)`:
the window `[-T,T]` for `F_ρ` corresponds to the window `[-ρ²T, ρ²T]` for `F`, still
symmetric, and `ρ² T → ∞` as `T → ∞`. The integrability clauses transform likewise. No time
translation occurs, so no bracket integrability is needed.

This is the standard-base (`Space m`, scalar) analogue of the dilation stage of the
similarity statements, which are stated on vertical bases `W × ℝ`.


-/
theorem ba1_standard_dilation :
    ∀ (m : ℕ) (F f : Space m → ℝ) (L : ℝ≥0) (B ρ : ℝ), 0 < ρ →
      (LipschitzWith L F → LipschitzWith L (fun p => ρ⁻¹ * F (dilate ρ p))) ∧
      (HasStandardParabolicBMOBound m f B →
        HasStandardParabolicBMOBound m (fun p => f (dilate ρ p)) B) ∧
      (RepresentsStandardHalfTimeDerivative m F f →
        RepresentsStandardHalfTimeDerivative m (fun p => ρ⁻¹ * F (dilate ρ p))
          (fun p => f (dilate ρ p))) := by
  exact ba1_standard_dilation_proof

/-- **Unit-scale affine Carleson bound of a regular scalar function**.

There is `C = C_m > 0` such that every `L`-Lipschitz real `F` on `Space m`
whose half-time derivative has a representative `f` with BMO bound `B` satisfies, at every
centre `z`, `∫_{P(z,1)} ∫_0^1 κ_F(p,s)² ds/s dp ≤ C (L² + B²)` (`affineCarlesonIntegral` at
radius `1`, base volume `parabolicVolume m`).

Proof sketch: apply the localization input at `p₀ = z`: `H ∈ L²` with `H = F - F(z)` on
`P(z,2)` (read through `fourierToParabolic m`) and `‖H‖² + E(H) ≤ C (L² + B²)`. For
`p ∈ P(z,1)` and `0 < s < 1`, `P(p,s) ⊆ P(z,2)`, where `H = F - F(z)`; subtracting a constant
does not change the best affine error, and `fourierToParabolic m` is measure preserving and
maps `coordBall x s` onto `P(Ψ x, s)`, so `κ_F(p,s)² = FourierAffine.affineEnergy H (Ψ⁻¹ p) s`
(normalizations `s^{-(m+4)}`). Hence the left side is at most
`FourierAffine.affineCarlesonEnergy H ≤ C' E(H)` by the Fourier input.

Hypotheses: `Characterization.CriticalSobolevLocalizationStatement` and
`Characterization.FourierAffineSquareStatement`, as stated (inputs).

-/
theorem ba1_vertical_unit_carleson
    (hloc : Characterization.CriticalSobolevLocalizationStatement)
    (hfour : Characterization.FourierAffineSquareStatement) :
    ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasStandardParabolicBMOBound m f B →
        RepresentsStandardHalfTimeDerivative m F f →
        ∀ z : Space m, affineCarlesonIntegral (parabolicVolume m) F z 1 ≤
          ENNReal.ofReal (C * ((L : ℝ) ^ 2 + B ^ 2)) := by
  exact ba1_vertical_unit_carleson_proof hloc hfour

/-- **Affine Carleson bound of a regular vector function at every scale** (the integrated bound for the
generic class, obtained by scaling back).

There is `C = C_{m,d} > 0` such that every `L`-Lipschitz
`F : Space m → ℝ^d` whose coordinates have half-time derivative BMO bound `B`
(`HasCoordinateHalfTimeBMOBound m d F B`) has the affine Carleson bound
`∫_{P(z,R)} ∫_0^R κ_F(p,s)² ds/s dp ≤ C (L² + B²) R^{m+2}` at every centre and radius
(`HasAffineCarlesonBound (parabolicVolume m) F (C (L² + B²))`).

Proof sketch: scalar coordinates first. For a coordinate `G = F^α` (`L`-Lipschitz, with a
representative of BMO bound `B`) and `R > 0`, put `G_R = R⁻¹ G ∘ δ_R`; by the dilation statement it
has the same Lipschitz and BMO bounds, so the unit-scale statement bounds its unit Carleson
integral at `δ_{1/R} z`. `traceErrorSq_similarity_proof` (with `K = univ`, `v = 0`,
`x₀ = 0`) gives `κ_G(p,s)² = κ_{G_R}(δ_{1/R} p, s/R)²`, and `setLIntegral_comp_similarity`
together with `s ↦ s/R` on `dr/r` give
`∫_{P(z,R)} ∫_0^R κ_G² = R^{m+2} ∫_{P(δ_{1/R} z,1)} ∫_0^1 κ_{G_R}²`. Vector: the squared
norm and an independent coordinatewise choice of near-optimal `(a_α, B_α)` give
`κ_F² ≤ Σ_α κ_{F^α}²`. Take `C = max(1,d) C_m` (the case `d = 0` is trivial for any
constant; `d C_m` would violate `0 < C` there).

Hypotheses: the conclusions of `ba1_vertical_unit_carleson` and
`ba1_standard_dilation`, as stated.

-/
theorem ba1_vertical_carleson
    (hunit : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F f : Space m → ℝ) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasStandardParabolicBMOBound m f B →
        RepresentsStandardHalfTimeDerivative m F f →
        ∀ z : Space m, affineCarlesonIntegral (parabolicVolume m) F z 1 ≤
          ENNReal.ofReal (C * ((L : ℝ) ^ 2 + B ^ 2)))
    (hdil : ∀ (m : ℕ) (F f : Space m → ℝ) (L : ℝ≥0) (B ρ : ℝ), 0 < ρ →
      (LipschitzWith L F → LipschitzWith L (fun p => ρ⁻¹ * F (dilate ρ p))) ∧
      (HasStandardParabolicBMOBound m f B →
        HasStandardParabolicBMOBound m (fun p => f (dilate ρ p)) B) ∧
      (RepresentsStandardHalfTimeDerivative m F f →
        RepresentsStandardHalfTimeDerivative m (fun p => ρ⁻¹ * F (dilate ρ p))
          (fun p => f (dilate ρ p)))) :
    ∀ m d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F : Space m → Spatial d) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasCoordinateHalfTimeBMOBound m d F B →
        HasAffineCarlesonBound (parabolicVolume m) F (C * ((L : ℝ) ^ 2 + B ^ 2)) := by
  exact ba1_vertical_carleson_proof hunit hdil

/-- **The vertical beta bound.**

For `1 ≤ L`, every vertical `L`-reference `V`, base point `p` and `r > 0`,
`β_{σ,V}(Φ(p), r)² ≤ L^{k+2} κ_F(p, L r)²`, where `κ_F` is the vector spatial-affine error of
`F = V.spatialMap` on `Space m` (`affineErrorSq (parabolicVolume m)`, normalization
`(Lr)^{-k-2}`, `m + 2 = k`).

Proof sketch: `σ = Φ_# L^{m+1}` and `Φ` is a measurable embedding, so the fit over `P(Φp, r)` is
the base integral over `Φ⁻¹ P(Φp,r) ⊆ P_b(p, L r)` (lower Lipschitz bound). For an affine
competitor `A(u) = a + B u`, choose a spatial `m`-plane `W ⊇ range B` (possible since
`m < n`; deficient rank is harmless) and the vertical model `(a + W) × ℝ`; the point
`(A(u), s)` lies on it, so `d_P(Φ(u,s), model)² ≤ |F(u,s) - A(u)|²`. Take the infimum over
`(a,B)`, and `r^{-k-2} = L^{k+2} (Lr)^{-k-2}`.

Hypotheses: the conclusion of `ba1_vertical_basic`, as stated.

-/
theorem ba1_vertical_beta
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (V : VerticalReference n k L) (p : Space V.spatialRank) (r : ℝ), 0 < r →
        betaSq V.measure k .vertical (V.map p) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
            affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap p (L * r) := by
  exact ba1_vertical_beta_proof hbasic

/-- **Own-type Carleson energy of vertical references.**

For `1 ≤ L` there is `C > 0`, depending only on `(n,k,L)`, with
`referenceEnergy (vertical V) ≤ C` for every vertical `L`-reference `V`.

Proof sketch: centres `a ∈ Γ` are `a = Φ(p₀)`. Push forward: `∫_{P(a,R)} S^R dσ` is the base
integral of `S^R ∘ Φ` over `Φ⁻¹ P(a,R) ⊆ P_b(p₀, L R)`. The beta statement bounds
`β_{σ,V}(Φ p, r)² ≤ L^{k+2} κ_F(p, L r)²`; the substitution `s = L r` (invariance of `dr/r`)
turns `∫_0^R` into `∫_0^{LR}`. `F` is `L`-Lipschitz (`|F p - F q| ≤ d_P(Φp,Φq) ≤ L d(p,q)`)
and its coordinates have BMO bound `L` (field `coordinate_bmo`), so the Carleson statement at
radius `L R` gives `≤ L^{k+2} C_{m,n} (2L²) (LR)^k`. Divide by `R^k`. The constant is chosen
from `m = k - 2` before the reference.

Hypotheses: the conclusions of `ba1_vertical_basic`, `ba1_vertical_beta` and
`ba1_vertical_carleson`, as stated.

-/
theorem ba1_vertical_energy
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ V : VerticalReference n k L,
      MeasurableEmbedding V.map ∧ IsClosed V.carrier ∧ V.measure.support = V.carrier ∧
        IsFiniteMeasureOnCompacts V.measure ∧ V.measure.InnerRegular)
    (hbeta : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (V : VerticalReference n k L) (p : Space V.spatialRank) (r : ℝ), 0 < r →
        betaSq V.measure k .vertical (V.map p) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
            affineErrorSq (parabolicVolume V.spatialRank) V.spatialMap p (L * r))
    (hcarl : ∀ m d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (F : Space m → Spatial d) (L : ℝ≥0) (B : ℝ),
        LipschitzWith L F → HasCoordinateHalfTimeBMOBound m d F B →
        HasAffineCarlesonBound (parabolicVolume m) F (C * ((L : ℝ) ^ 2 + B ^ 2))) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ V : VerticalReference n k L, referenceEnergy (Reference.vertical V) ≤ ENNReal.ofReal C := by
  exact ba1_vertical_energy_proof hbasic hbeta hcarl

/-! ## Horizontal references: the whole plateau completion -/

/-- **The horizontal beta bound** (the temporal term).

For `1 ≤ L`, every horizontal `L`-reference `H`, `u ∈ ℝ^k` and `r > 0`,
`β_{σ,H}((F(u),T(u)), r)² ≤ L^{k+2} a_F(u, L r)² + τ_L(u,r)`, where `a_F` is the spatial
affine error `Characterization.spatialAffineErrorSq` of `F = H.spatialMap` and
`τ_L(u,r) = r^{-k-2} ∫_{|v-u| < Lr, |T(v)-T(u)| < r²} |T(v) - T(u)| dv` keeps the actual
parabolic time restriction.

Proof sketch: `σ = (F,T)_# L^k`, so the fit over `P((F(u),T(u)), r)` is the base integral over
`{v : |F(v) - F(u)| < r, |T(v) - T(u)| < r²} ⊆ {|v - u| < Lr, |T(v) - T(u)| < r²}`. For an
affine `A(v) = a + Bv` choose a spatial `k`-plane containing `range A` (deficient rank is
harmless, `k ≤ n`) and the horizontal model at the centre's time `T(u)`:
`d_P((F(v),T(v)), model)² ≤ |F(v) - A(v)|² + |T(v) - T(u)|` (testing at the centre's time). Drop the time restriction only in the spatial term, take the infimum over `(a,B)`,
and `r^{-k-2} = L^{k+2}(Lr)^{-k-2}`.

Hypotheses: the conclusion of `ba1_horizontal_basic`, as stated.

-/
theorem ba1_horizontal_beta
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (H : HorizontalReference n k L) (u : Spatial k) (r : ℝ), 0 < r →
        betaSq H.measure k .horizontal (H.map u) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
              Characterization.spatialAffineErrorSq H.spatialMap u (L * r) +
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) := by
  exact ba1_horizontal_beta_proof hbasic

/-- **The flat Whitney interpolation.**

There is `C = C_k > 0` such that for every `n`, `1 ≤ L` and horizontal
`L`-reference `H` (trace `τ = T|_D`, `|τ(u) - τ(v)| ≤ L²|u - v|²`) there is a `C¹` function
`h : ℝ^k → ℝ` with `h = T` on `D`, `|T - h| ≤ C L² d²` and `|∇h| ≤ C L² d` everywhere, where
`d = dist(·, D)`. In particular `∇h = 0` on `D`, so `∇h` may be integrated along segments that
meet `D`.

Proof sketch: a smooth Whitney partition of unity `(φ_Q)` subordinate to slightly enlarged
cubes of the given decomposition, `h = Σ_Q φ_Q τ(a_Q)` off `D` and `h = τ` on `D`.
Neighbouring cubes have comparable sides and anchors within `C ℓ_Q`, so their anchor values
differ by `O(L² ℓ_Q²)`; `Σ ∇φ_Q = 0` gives `|∇h| ≤ C L² ℓ_Q ≤ C L² d`; `T = τ(a_Q)` on the
face of `Q` gives `|T - h| ≤ C L² d²`. At `a ∈ D`, `|h(x) - h(a)| ≤ C L² |x - a|²`, so `h` is
differentiable with `∇h(a) = 0`, and `|∇h| ≤ C L² d → 0` gives continuity of `∇h`.

The same interpolation is the flat jet of the horizontal completion.

-/
theorem ba1_horizontal_interpolation :
    ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      ∃ h : Spatial k → ℝ, ContDiff ℝ 1 h ∧ (∀ u ∈ H.domain, h u = H.height u) ∧
        (∀ u, |H.height u - h u| ≤ C * L ^ 2 * Metric.infDist u H.domain ^ 2) ∧
        (∀ u, ‖fderiv ℝ h u‖ ≤ C * L ^ 2 * Metric.infDist u H.domain) := by
  exact ba1_horizontal_interpolation_proof

/-- **Coarse scales of the temporal energy.**

For `1 ≤ L` there is `C > 0`, depending only on `(n,k,L)`, such that for every
horizontal `L`-reference, centre `b` and `R > 0`, the coarse part of the temporal energy
`∫_{B(b,R) ∩ D} ∫_0^R τ_L(u,r) dr/r du + Σ_Q ∫_{B(b,R) ∩ face Q} ∫_{ℓ_Q}^R τ_L(u,r) dr/r du`
is at most `C R^k` (coarse: `r ≥ ℓ_Q` at centres in `Q`; every scale at centres in `D`).

Proof sketch: at coarse scales `d(u) ≤ C r`. Drop the time cutoff and split
`|T(v) - T(u)| ≤ |T(v) - h(v)| + |h(v) - h(u)| + |h(u) - T(u)|` with the interpolation `h`.
Plateau errors: Fubini over centres and their radius-`Lr` neighbours reduces both to
`C L² ∫_{B(b,CR)} d(w)² ∫_{d(w)/C}^R r^{-3} dr dw ≤ C R^k`; treat the points with `d = 0`
(they contribute zero) before the scale integration. Smooth difference:
`|h(u+w) - h(u)| ≤ C L² |w| ∫_0^1 d(u + s w) ds`; at fixed `r` and `s`, translate the centre
variable `q = u + s w` (Jacobian one), so the integral over centres is
`≤ C L² r^{-1} ∫_{d(q) ≤ Cr} d(q) dq`, and the scale integral is
`C L² ∫_{B(b,CR)} d(q) ∫_{d(q)/C}^R r^{-2} dr dq ≤ C R^k`. No logarithmic loss.

Hypotheses: the conclusion of `ba1_horizontal_interpolation`, as stated.

-/
theorem ba1_horizontal_coarse
    (hinterp : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (L : ℝ), 1 ≤ L →
      ∀ H : HorizontalReference n k L,
        ∃ h : Spatial k → ℝ, ContDiff ℝ 1 h ∧ (∀ u ∈ H.domain, h u = H.height u) ∧
          (∀ u, |H.height u - h u| ≤ C * L ^ 2 * Metric.infDist u H.domain ^ 2) ∧
          (∀ u, ‖fderiv ℝ h u‖ ≤ C * L ^ 2 * Metric.infDist u H.domain)) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) +
          (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R,
              (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
                (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                  ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k) := by
  exact ba1_horizontal_coarse_proof hinterp

/-- **Fine scales of the temporal energy, face strips.**

For `1 ≤ L` there is `C > 0`, depending only on `(n,k,L)`, such that for every
horizontal `L`-reference, centre `b` and `R > 0`, the fine part
`Σ_Q ∫_{B(b,R) ∩ face Q} ∫_0^{min(R, ℓ_Q)} τ_L(u,r) dr/r du` is at most `C R^k`.

Proof sketch: retain the actual time restriction `|T(v) - T(u)| < r²`
throughout. `τ_L ≤ ω_k L^k` always (the time restriction bounds the cost by `r²`);
`τ_L(u,r) = 0` when `L r < d_Q(u) = dist(u, ∂Q)`, since then the ball `B(u, Lr)` lies in
`int Q ⊆ face Q` where `T` is constant. Hence
`∫_0^{min(R,ℓ_Q)} τ_L dr/r ≤ C L^k log₊(L min(R,ℓ_Q)/d_Q(u))`. Cubes with `ℓ_Q ≤ R` meeting
`B(b,R)`: the logarithm integrates to `C_k L^k (1 + log L) |Q|` over `Q` (the constant depends
on `L` through `log L`; it is still `C(n,k,L)`), and their disjoint interiors lie in
`B(b,CR)`. Only boundedly many cubes with `ℓ_Q > R` meet `B(b,R)`: prove this count by inward
boxes (each such cube contains an inward box of volume `c_k R^k` near the ball). For each, the
clipped face strips satisfy `|B(b,R) ∩ Q ∩ {d_Q < s}| ≤ C s R^{k-1}` (`0 < s < R`), and the
layer-cake formula, including the portion `R ≤ s ≤ LR`, bounds the logarithm by `C R^k`.
The time restriction is essential here: jumps across a face can exceed `r²`, but such points
lie outside the parabolic ball.


-/
theorem ba1_horizontal_fine :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
          ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k) := by
  exact ba1_horizontal_fine_proof

/-- **The temporal energy at every radius.**

For `1 ≤ L` there is `C > 0`, depending only on `(n,k,L)`, with
`∫_{B(b,R)} ∫_0^R τ_L(u,r) dr/r du ≤ C R^k` for every horizontal `L`-reference, centre `b` and
`R > 0`.

Proof sketch: `B(b,R)` is the disjoint union of `B(b,R) ∩ D` and the Borel pieces
`B(b,R) ∩ face Q` (`faces_cover`, `face_disjoint`, `face_measurable`); for `u` in a face,
`(0,R) ⊆ [ℓ_Q, R) ∪ (0, min(R,ℓ_Q))`. Sum the coarse and fine statements (measurability of the
inner scale integrals in `u` from the Borel measurability of `T`).

Hypotheses: the conclusions of `ba1_horizontal_basic`, `ba1_horizontal_coarse` and
`ba1_horizontal_fine`, as stated.

-/
theorem ba1_horizontal_temporal
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular)
    (hcoarse : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∫⁻ u in Metric.ball b R ∩ H.domain, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) +
          (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
            ∫⁻ r in Ico (H.gridScale * (2 : ℝ) ^ H.cubeLevel i) R,
              (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
                (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                  ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k))
    (hfine : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        (∑' i : H.cubeIndex, ∫⁻ u in Metric.ball b R ∩ H.face i,
          ∫⁻ r in Ioo 0 (min R (H.gridScale * (2 : ℝ) ^ H.cubeLevel i)),
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure) ≤
          ENNReal.ofReal (C * R ^ k)) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure ≤
          ENNReal.ofReal (C * R ^ k) := by
  exact ba1_horizontal_temporal_proof hbasic hcoarse hfine

/-- **Own-type Carleson energy of horizontal references.**

For `1 ≤ L` there is `C > 0`, depending only on `(n,k,L)`, with
`referenceEnergy (horizontal H) ≤ C` for every horizontal `L`-reference `H`.

Proof sketch: for `a ∈ Γ` and `R > 0`, the preimage of `P(a,R)` under `(F,T)` is empty or lies
in a base ball `B(v₀, 2LR)` (`|v - v'| ≤ L|F(v) - F(v')| < 2LR`). Push forward and apply the
beta statement at every `(u,r)`. Spatial term: the substitution `s = L r` and (the input
`SpatialAffineSquareStatement`, with `F` `L`-Lipschitz, at radius `2LR`) give
`≤ L^{k+2} C L² (2LR)^k`. Temporal term: the temporal statement at radius `2LR` (the scale range
`(0,R) ⊆ (0,2LR)`). Divide by `R^k`. Constants independent of the number, measure or
diameter of the components of `D`.

Hypotheses: the conclusions of `ba1_horizontal_basic`, `ba1_horizontal_beta` and
`ba1_horizontal_temporal`, and `Characterization.SpatialAffineSquareStatement`, as stated.


-/
theorem ba1_horizontal_energy
    (hbasic : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∀ H : HorizontalReference n k L,
      Measurable H.map ∧ IsClosed H.carrier ∧ IsFiniteMeasureOnCompacts H.measure ∧
        H.measure.InnerRegular)
    (hbeta : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (H : HorizontalReference n k L) (u : Spatial k) (r : ℝ), 0 < r →
        betaSq H.measure k .horizontal (H.map u) r ≤
          ENNReal.ofReal (L ^ (k + 2)) *
              Characterization.spatialAffineErrorSq H.spatialMap u (L * r) +
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|))
    (hsp : Characterization.SpatialAffineSquareStatement)
    (htemp : ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ (H : HorizontalReference n k L) (b : Spatial k) (R : ℝ), 0 < R →
        ∫⁻ u in Metric.ball b R, ∫⁻ r in Ioo 0 R,
            (ENNReal.ofReal r)⁻¹ ^ (k + 2) *
              (∫⁻ v in {v : Spatial k | dist v u < L * r ∧ |H.height v - H.height u| < r ^ 2},
                ENNReal.ofReal |H.height v - H.height u|) ∂scaleMeasure ≤
          ENNReal.ofReal (C * R ^ k)) :
    ∀ (n k : ℕ) (L : ℝ), 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ H : HorizontalReference n k L,
        referenceEnergy (Reference.horizontal H) ≤ ENNReal.ofReal C := by
  exact ba1_horizontal_energy_proof hbasic hbeta hsp htemp

end ParabolicRectifiability.QuantitativeCharacterization
