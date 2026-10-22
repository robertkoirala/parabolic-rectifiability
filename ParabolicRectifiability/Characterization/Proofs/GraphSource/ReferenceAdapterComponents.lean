import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceAdapterStatements
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Plateau.Completion
import ParabolicRectifiability.Characterization.Proofs.GraphSource.HorizontalChart
import ParabolicRectifiability.Characterization.Proofs.GraphSource.HalfTimeAffine
import ParabolicRectifiability.Characterization.Proofs.GraphSource.VerticalChart
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ADRCarrierFacts
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ADRHausdorffComparison
import ParabolicRectifiability.Characterization.Proofs.GraphSource.ReferenceSupport
import ParabolicRectifiability.QuantitativeCharacterization.Proofs.Reference.HorizontalCarrier
import ParabolicRectifiability.QuantitativeCharacterization.Statements.WhitneyPlateau
import ParabolicRectifiability.QuantitativeCharacterization.Coverings

/-! # Component estimates for the reference adapters and reference facts

The declarations delegate to the component proof theorems imported above from
`Characterization/Proofs/` and, for the plateau completion,
`QuantitativeCharacterization/Proofs/`. Each retains its original mathematical inputs.
Estimates that are taken as hypotheses appear as explicit hypotheses (in implication form).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ParabolicRectifiability.Characterization

open ParabolicRectifiability.Foundations ParabolicRectifiability.QuantitativeCharacterization

/-! ## Horizontal adapter -/

/-- The Whitney plateau completion (`WhitneyPlateauCompletionStatement`).

From a nonempty compact `D ⊆ ℝ^k`, a global `L`-bi-Lipschitz `F` and a trace
with `|τ(u) - τ(v)| ≤ L²|u - v|²` on `D`, produce the remaining data of a horizontal
`L`-reference with spatial map `F`, domain `D` and plateau function equal to `τ` on `D`.

Proof route. Grid origin `0`, scale `1`. Take the maximal closed dyadic cubes `Q` with
`4 diam Q ≤ dist(Q,D)` (they exist: small cubes containing a point of `Dᶜ` qualify; large
ancestors do not, since `D ≠ ∅`). For the parent `Q'`, `dist(Q,D) ≤ diam Q' + dist(Q',D)
< 2 diam Q + 8 diam Q`, so `dist(Q,D) ≤ 10 diam Q`. Maximal cubes are nested or have disjoint
interiors, and their union is `Dᶜ`; enumerate them by a subset of `ℕ`. Anchors: minimize
`(x,a) ↦ |x - a|` on the compact `Q × D`. Faces: `Φ_i = Q_i \ ⋃_{j<i} Q_j` in the enumeration
order (the interior of `Q_i` meets no other closed cube). Plateau: `T = τ` on `D` and
`T = τ(a_i)` on `Φ_i`. `setDist` is the genuine infimum here (nonempty `Q`, nonempty `D`). -/
theorem b2_whitney_plateau_completion : WhitneyPlateauCompletionStatement := by
  exact ParabolicRectifiability.QuantitativeCharacterization.b2_whitney_plateau_completion_proof

/-- Spatial chart of a horizontal subset graph.

For every real `ε` there is `L ≥ 1`, depending on `(n, k, ε)` as the type
states (`∀ n k ε, ∃ L`), such that every
horizontal subset graph `G` of slope at most `ε` is contained in `{(F(u), τ(u)) : u ∈ D}` for a
global `L`-bi-Lipschitz `F : ℝ^k → ℝ^n`, a set `D ⊆ ℝ^k` and a function `τ` with
`|τ(u) - τ(v)| ≤ L²|u - v|²` on `D`, where `D` is nonempty (compact) when the graph domain is.

Proof route. `e`: orthonormal coordinates `G.direction ≃ ℝ^k` (reindex
`stdOrthonormalBasis` by `finCongr G.rank_eq`). `D = e(domain)`. Extend the normal map
`g : domain → U^⊥` to a global Lipschitz map (componentwise McShane `LipschitzOnWith.extend_real`
in an orthonormal basis of `U^⊥`, constant `√(n-k) ε`, or Kirszbraun). Set
`F(v) = a + e⁻¹ v + g̃(e⁻¹ v)`; orthogonality gives `|v - w| ≤ |F v - F w| ≤ (1 + √n |ε|)|v - w|`.
`τ = h ∘ e⁻¹` on `D` (any value off `D`); the slope bound gives `|τ u - τ v| ≤ ε²|u - v|²`.
Take `L = 1 + √n |ε|`; this choice is additionally independent of `k`, but the type only promises `L = L(n, k, ε)`. If `ε < 0` the domain has at most one
point (constant extension). -/
theorem b2_horizontal_chart :
    ∀ (n k : ℕ) (ε : ℝ), ∃ L : ℝ, 1 ≤ L ∧ ∀ G : HorizontalGraph n k ε,
      ∃ (F : Spatial k → Spatial n) (D : Set (Spatial k)) (τ : Spatial k → ℝ),
        (∀ u v : Spatial k, dist u v ≤ L * dist (F u) (F v) ∧ dist (F u) (F v) ≤ L * dist u v) ∧
        (∀ u ∈ D, ∀ v ∈ D, |τ u - τ v| ≤ L ^ 2 * dist u v ^ 2) ∧
        (G.domain.Nonempty → D.Nonempty) ∧ (IsCompact G.domain → IsCompact D) ∧
        G.image ⊆ (fun u => point (F u) (τ u)) '' D := by
  exact ParabolicRectifiability.Characterization.b2_horizontal_chart_proof

/-- Trace points lie in the closed support: the closed support consists of the trace and all
closed plateau faces.

For every horizontal `L`-reference and every `u ∈ D`, the trace point
`(F(u), τ(u))` belongs to `Γ = supp σ`, `σ = (F,T)_# L^k`.

Proof route. `(F,T)` is measurable (`F` is Lipschitz; `T` is continuous on the closed `D` by the
trace bound and constant on each Borel face), so `σ(U) = L^k((F,T)⁻¹ U)`. For `v` near `u`:
if `v ∈ Φ_i`, choose `x ∈ Q_i` with `|x - a_i| = dist(Q_i,D) ≤ |v - u|`; then
`|a_i - u| ≤ |a_i - x| + diam Q_i + |v - u| ≤ 3 |v - u|`, so
`|T v - τ u| = |τ a_i - τ u| ≤ 9 L² |v - u|²`; on `D` directly. With `|F v - F u| ≤ L |v - u|`,
a base ball `B(u, δ r)` maps into `P((F u, τ u), r)`, so every neighbourhood has positive
`σ`-measure (`Measure.mem_support_iff_forall`). (`L ≥ 1` is forced by bi-Lipschitzness on
`ℝ^k`, `k ≥ 1`.) -/
theorem b2_horizontalReference_map_mem_carrier :
    ∀ (n k : ℕ) (L : ℝ) (H : HorizontalReference n k L) (u : Spatial k),
      u ∈ H.domain → H.map u ∈ H.carrier := by
  exact ParabolicRectifiability.Characterization.b2_horizontalReference_map_mem_carrier_proof

/-! ## Vertical adapter -/

/-- Half-time derivative of an affine-plus-combination function
(`HalfTimeAffineCombinationStatement`).

Representation is linear, and a time-independent affine function of the
spatial variable is represented by `0`, both in the exact sense of
`RepresentsHomogeneousHalfTimeDerivative` (local integrability, a.e.-time inner
integrability, window integrability of the bracket, convergence of the ordered pairing).

Proof route. Linearity: prove finite-sum linearity using the stated
ordered-integrability clauses (inner integrands, brackets a.e. in `t`, and windows are linear;
limits add; `∫ (Σ M_i g_i) φ = Σ M_i ∫ g_i φ` since each `g_i φ` is integrable). Affine part
`A(u) = c + ℓ(u)`: apply compact-test kernel integrability
(`integrable_testKernel_of_hasCompactSupport`)
and total cancellation (`fcond_integral_testKernel_eq_zero`; it gives the **total** integral, not a per-fibre one)
to the smooth compact test `Aφ`. Time translation leaves `A` unchanged, so
`testKernel (Aφ) = A · testKernel φ`. Transfer through the almost-everywhere equality with
`halfTimeDeriv` (`testKernel_ae_halfTimeDeriv`), then apply ordered Fubini. The pointwise
support and fibre identities belong to `testKernel`; the chosen `halfTimeDeriv` representative
inherits them only almost everywhere. (`fcond_integrable_testKernelIntegrand_prod` is the
integrability of the `(x,h)` kernel integrand, not of `testKernel ψ` itself.
`fcond_representsHomogeneous_const_add` assumes `MemLp H 2` and `RepHalf`
so it is not the general constant case.) -/
theorem b2_halfTime_affine_combination : HalfTimeAffineCombinationStatement := by
  exact ParabolicRectifiability.Characterization.b2_halfTime_affine_combination_proof

/-- The vertical chart is bi-Lipschitz (with time recovered).

For a linear subspace `W`, an offset `a` and a `K`-Lipschitz
`G : W × ℝ → W^⊥`, the map `Φ(p) = (a + ι(p)₁ + G(ι p), p₂)` on `Space (dim W)`,
`ι = (subspaceParabolicIsometry W).symm`, satisfies `d(p,q) ≤ d(Φ p, Φ q) ≤ (1 + K) d(p,q)`.

Proof route. `ι` is an isometry. The spatial difference is `(ι p)₁ - (ι q)₁ + (G(ι p) - G(ι q))`
with the first summand in `W` and the second in `W^⊥`, so its norm squared is the sum of the
two squares (`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`); it is at least
`|p₁ - q₁|` and at most `|p₁ - q₁| + K d(p,q)`. The time components agree with those of `p, q`
(`Prod.dist_eq`). -/
theorem b2_vertical_chart_bilipschitz :
    ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (a : Spatial n)
      (Gf : SubspaceSpace W → W.orthogonal) (K : ℝ≥0), LipschitzWith K Gf →
      ∀ p q : Space (Module.finrank ℝ W),
        dist p q ≤ dist ((a + (((subspaceParabolicIsometry W).symm p).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm p) : Spatial n), p.2) : Space n)
            (a + (((subspaceParabolicIsometry W).symm q).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm q) : Spatial n), q.2) ∧
        dist ((a + (((subspaceParabolicIsometry W).symm p).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm p) : Spatial n), p.2) : Space n)
            (a + (((subspaceParabolicIsometry W).symm q).1 : Spatial n) +
              (Gf ((subspaceParabolicIsometry W).symm q) : Spatial n), q.2) ≤
          (1 + (K : ℝ)) * dist p q := by
  exact ParabolicRectifiability.Characterization.b2_vertical_chart_bilipschitz_proof

/-- Coordinate BMO of a vector BMO function.

If `g : W × ℝ → W^⊥` has vector parabolic BMO bound `B` for the intrinsic
volume, then for every ambient coordinate `α`, the real function
`p ↦ (g(ι p) : ℝ^n)_α` on `Space (dim W)` has real parabolic BMO bound `B` for
`parabolicVolume (dim W)` (`ι = (subspaceParabolicIsometry W).symm`).

Proof route. `ι` is an isometry and carries `parabolicVolume` to `intrinsicParabolicVolume W`
(`subspaceParabolic_symm_measurePreserving`), so it maps balls to balls with the same volume
and preserves local integrability. Averages commute with the continuous linear functional
`v ↦ (v : ℝ^n)_α` of norm at most one (integrable on balls by local integrability), and
`|v_α| ≤ |v|` (`PiLp.norm_apply_le`), so the mean oscillation of the coordinate is at most the
vector mean oscillation, ball by ball. -/
theorem b2_vertical_coordinate_bmo :
    ∀ (n : ℕ) (W : Submodule ℝ (Spatial n)) (g : SubspaceSpace W → W.orthogonal) (B : ℝ),
      HasParabolicBMOBound W g B → ∀ α : Fin n,
        HasStandardParabolicBMOBound (Module.finrank ℝ W)
          (fun p => ((g ((subspaceParabolicIsometry W).symm p) : W.orthogonal) : Spatial n) α)
          B := by
  exact ParabolicRectifiability.Characterization.b2_vertical_coordinate_bmo_proof

/-! ## Reference facts -/

/-- Basic carrier facts of the typed references: completeness and the lower Lipschitz bound
make `Γ` closed.

For every typed `L`-reference, `supp σ = Γ` and `Γ ≠ ∅`.

Proof route. Horizontal: `Γ = supp σ` by definition; `(F,T)` is measurable (see
`b2_horizontalReference_map_mem_carrier`) so `σ(X) = L^k(ℝ^k) = ∞`, `σ ≠ 0`
(`Measure.nonempty_support`). Vertical: bi-Lipschitzness forces `L ≥ 1`; `Φ` is continuous with
closed range (complete domain, lower Lipschitz bound); a point of the range has every
neighbourhood of positive measure (the preimage is a nonempty open set and
`parabolicVolume` charges open sets), a point off the range has a null open neighbourhood.
Ambient: `parabolicVolume n` charges every ball (`parabolicVolume_ball`), so its support is
`X`. -/
theorem b2_reference_support_carrier :
    ∀ (n k : ℕ) (L : ℝ) (ρ : Reference n k L),
      ρ.measure.support = ρ.carrier ∧ ρ.carrier.Nonempty := by
  exact ParabolicRectifiability.Characterization.b2_reference_support_carrier_proof

/-- `IsADR` gives the closed ADR carrier (`ADRCarrierOfADRStatement`).

Converts the single-constant ADR property into the reference hypotheses of
the source-transfer appendix, with `Γ = supp σ`, `c = A⁻¹`, `C = A`.

Proof route. `isClosed_support`; finiteness on compacts: a ball `P(z,r)` either misses
`supp σ` (then it is null, `measure_compl_support`) or lies in `P(w, 2r)` for a support point
`w`, of measure at most `A (2r)^k`; cover a compact set by finitely many balls. Inner
regularity: a locally finite Borel measure on the proper second-countable space `X` is
regular, hence inner regular (`Measure.InnerRegular` from `Regular` and sigma-finiteness). The ADR bounds are the hypothesis. -/
theorem b2_isADRCarrier_of_isADR : ADRCarrierOfADRStatement := by
  exact ParabolicRectifiability.Characterization.b2_isADRCarrier_of_isADR_proof

/-- Comparison of an ADR measure with Hausdorff measure (`ADRHausdorffComparisonStatement`):
`σ(S) ≤ a H_P^k(S ∩ Γ)` and `H_P^k(S ∩ Γ) ≤ b σ(S)` for every set `S`, with
`a, b` depending only on `(k, c, C)`.

Proof route. Upper: `σ(Γᶜ) = 0`; a `δ`-cover of `S ∩ Γ` by sets `E_i` of diameter `d_i` gives,
recentred at points of `Γ`, `σ(E_i) ≤ σ(P(x_i, 2 d_i)) ≤ C 2^k d_i^k` (a singleton is
`σ`-null by upper ADR at every radius), so `σ(S) ≤ 2^k C H_P^k(S ∩ Γ)`. Lower: for a Borel
`E ⊆ Γ` inside an open `O`, centre balls of radius `< δ` inside `O`, select disjoint ones with
fivefold dilates covering `E` (`FivefoldSelectionStatement`), and use lower ADR:
`H^k_{10δ}(E) ≤ 10^k Σ r_i^k ≤ 10^k c⁻¹ σ(O)`; then outer regularity of `σ` and
`σ(S) = σ(toMeasurable σ S)` pass to arbitrary `S`.

Constants: for arbitrary real `c, C`, choose `a = 2^k max(C,1)` and
`b = 10^k max(c⁻¹,1)`. Both are positive before the carrier hypothesis is imposed; for
admissible parameters the sharper bounds `2^k C` and `10^k / c` are valid. The recipe
`b = 10^k / c` alone fails the unconditional positivity when `c ≤ 0` (and `a = 2^k C` when
`C ≤ 0`); the statement itself is true as typed.

The hypothesis `FivefoldSelectionStatement` is taken explicitly. -/
theorem b2_adr_hausdorff_comparison : ADRHausdorffComparisonStatement := by
  exact ParabolicRectifiability.Characterization.b2_adr_hausdorff_comparison_proof

/-- A finite Carleson energy gives an a.e. finite square.

If `sup_{a ∈ S, R > 0} R^{-k} ∫_{P(a,R)} S^R_{σ,T} dσ < ∞` for a nonempty `S`
and a measure `σ` finite on compacts, then `S^1_{σ,T} < ∞` `σ`-almost everywhere.

Proof route. Fix `a ∈ S`. For each natural `N ≥ 1`, `∫_{P(a,N)} S^N_{σ,T} dσ ≤ N^k M < ∞`, so
`S^N < ∞` `σ`-a.e. on `P(a,N)` (`ae_lt_top'` with `measurable_squareEnergy`), and
`S^1 ≤ S^N` (`squareEnergy_mono_endpoint`). The balls `P(a,N)` exhaust `X`. -/
theorem b2_ae_squareEnergy_lt_top_of_carleson :
    ∀ (n k : ℕ) (T : FamilyKind) (S : Set (Space n)) (σ : Measure (Space n)),
      IsFiniteMeasureOnCompacts σ → S.Nonempty →
      rootCarlesonSup S σ k (fun R z => squareEnergy σ k T R z) < ⊤ →
        ∀ᵐ z ∂σ, squareEnergy σ k T 1 z < ⊤ := by
  exact ParabolicRectifiability.Characterization.b2_ae_squareEnergy_lt_top_of_carleson_proof

end ParabolicRectifiability.Characterization
