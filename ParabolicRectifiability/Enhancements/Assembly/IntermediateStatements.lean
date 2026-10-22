import ParabolicRectifiability.Enhancements.Decomposition
import ParabolicRectifiability.Measure.BetaLaws
import ParabolicRectifiability.Enhancements.Proofs.Scaling.RescaledEnhancedDecomposition
import ParabolicRectifiability.Enhancements.Proofs.ElementaryBounds
import ParabolicRectifiability.Enhancements.Proofs.GraphDomains.FixedCarrierCover
import ParabolicRectifiability.Characterization.Proofs.Fivefold
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.HorizontalClosedExtension
import ParabolicRectifiability.Foundations.Proofs.GraphEnvelope.GraphImageBorel

/-! # Intermediate statements for the rectifiable Reifenberg theorem and its enhancements

Five intermediate lemmas, each with one mathematical content, used in the proofs of the
rectifiable Reifenberg theorem, the graph-domain enhancement, the scaled theorem, the energy rates
and the density corollaries:

| Lemma | Used in |
|---|---|
| `exists_hausdorffP_le_of_local_bound` | `rectifiable_reifenberg_theorem_of_providers` |
| `exists_fixedCarrier_graphDomainCover` | `fixed_carrier_graph_domain_skeleton` |
| `isLocalEnhancedDecomposition_of_rescaledSource` | `scaled_rectifiable_reifenberg_of_providers` |
| `measure_lt_squareEnergy_le_gaugeEnergy_div` | the power and gauge rates |
| `upperDensity_eq_of_not_mem_closed_carrier` | the density corollaries |

None of them assumes a packing, content, density or regularity hypothesis beyond those of
the theorems they serve.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ParabolicRectifiability.Enhancements

open ParabolicRectifiability.Foundations

/-- **Global Hausdorff bound from local bounds on the unit closure** (the global
Hausdorff estimate is a finite-cover consequence of the local one on the compact unit
closure).

There is a number `N = N(n) > 0` (a covering number of `P̄(0,1)` by open
radius-one cylinders, independent of `k`) such that every set `K ⊆ P̄(0,1)` whose local
Hausdorff measure obeys `H_P^k(K ∩ P(q,R)) ≤ C R^k` for every centre `q` and `0 < R ≤ 1`
satisfies `H_P^k(K) ≤ N C`. The argument is countable subadditivity of the outer measure
over the finite cover; compactness or measurability of `K` is not needed, and the
statement is also true for `C < 0` (then `K` is `H_P^k`-null).

Used in `rectifiable_reifenberg_theorem_of_providers`, which applies it to the union of the
actual supports of the rectifiability decomposition (whose local Hausdorff field is
`HasRectifiabilityContentBounds.hausdorff`). -/
theorem exists_hausdorffP_le_of_local_bound (n : ℕ) :
    ∃ N : ℝ, 0 < N ∧ ∀ (k : ℕ) (C : ℝ) (K : Set (Space n)),
      K ⊆ Metric.closedBall (point 0 0) 1 →
      (∀ (q : Space n) (R : ℝ), 0 < R → R ≤ 1 →
        hausdorffP n k (K ∩ Metric.ball q R) ≤ ENNReal.ofReal (C * R ^ k)) →
      hausdorffP n k K ≤ ENNReal.ofReal (N * C) := by
  exact exists_hausdorffP_le_of_local_bound_proof n

/-- **Relative graph-domain covers on a fixed carrier.**

For each `n ≥ 1` there is `C > 0` such that for every `1 ≤ k ≤ n+2`, one
available fixed type `T`, and every compact `K` with `H_P^k(K) < ∞` that has a countable
type-`T` cover modulo `H_P^k` at every tolerance `η > 0`, the singleton family `(K)` (the
carrier pair with `K` in the slot of `T` and `∅` in the other slot) has, for every
`ε, δ > 0`, a graph-domain cover with bound `C`, tolerance `ε` and mesh `δ`
(`Foundations.GraphDomainCover`: disjoint Borel traces, Borel trace preimages, patches of
radius at most `δ`, the trace estimate for every Borel `U`, and the relative global and
local patch bounds `C H_P^k(K)` and `C H_P^k(K ∩ P(q,2R))` at every `R > 0`).

The construction proceeds through bi-Lipschitz graph charts, closures and Borel traces,
base-volume comparison, assignment of points to graphs, compact traces, a fivefold ball
selection, density estimates, selection of patches, and the global and local charge
bounds. The final numerical growth substitution
(`C H_P^k(K ∩ P(q,2R)) ≤ C 2^k A R^k` under the growth hypothesis when `2R ≤ R_*`) is
elementary and is done in `fixed_carrier_graph_domain_skeleton`. No growth, density or
source hypothesis is assumed. -/
theorem exists_fixedCarrier_graphDomainCover (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ n + 2 →
      ∀ T : FamilyKind, T ≠ .mixed → Nonempty (Models n k T) →
      ∀ K : Set (Space n), IsCompact K → hausdorffP n k K < ⊤ →
      (∀ η : ℝ, 0 < η → HasTypedGraphCover T k K η) →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        Nonempty (GraphDomainCover n k C ε δ
          (if T = .horizontal then K else ∅) (if T = .vertical then K else ∅)) := by
  exact GraphDomainTree.exists_fixedCarrier_graphDomainCover_of_providers
    Characterization.fivefold_ball_selection_proof Foundations.fgenv_horizontal_closed_extension_proof
    Foundations.fgenv_horizontal_image_measurableSet_of_isClosed_proof
    Foundations.fgenv_vertical_image_measurableSet_proof n hn

/-- **Similarity transport of an enhanced unit decomposition.**

Setting: `F(y) = a + δ_R y`, `ν = R^{-k} (F^{-1})_# μ = rescaledSource μ k a R hR`, and
`F^{-1} = similarity a R hR`. Let `D` be unit retained sets for `ν` whose actual supports
satisfy the unit support bundle with constant `C`, the unavailable-type and fixed-family
vanishing clauses, and, for every `ε, δ > 0`, graph-domain covers with bound `C` and the
absolute charge bounds at scale `1`.

Then the pulled-back sets `E_T = F(D_T) = (similarity a R hR)⁻¹' D_T` form the
enhanced restriction decomposition of `μ` on `P(a,R)` with the **same** constant `C`, and
the loss transforms exactly: `μ⁺(P(a,R)) = R^k ν⁺(P(0,1))`. This is pure covariance under
the parabolic similarity: restrictions and actual supports are carried by the
homeomorphism; `H_P^k` and base volumes scale by `R^k`, ambient volume by `R^{n+2}`,
separated nets and packings by the radius factor `R`; horizontal slopes and the general
regular seminorm are invariant under `G_R(u,t) = R G(u/R, t/R²)`; graph-domain covers with
mesh `δ/R` become covers with mesh `δ`, charges scale by `R^k`, and the local index sets
`I(q,s)` correspond to `I(F⁻¹q, s/R)`.

No threshold, energy or regularity hypothesis on `μ` beyond the stated data is used; the
remainder bound of `D` is not an input (the loss identity is an equality).

Used in `scaled_rectifiable_reifenberg_of_providers` (through
`scaled_and_ambient_of_graphEnhanced`), which supplies `D` from the unit graph enhancement
applied to `ν` with threshold allowance `R^{-k} Γ`. -/
theorem isLocalEnhancedDecomposition_of_rescaledSource {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n + 2)
    (μ : Measure (Space n)) (hμ : IsFiniteMeasureOnCompacts μ) (hreg : μ.InnerRegular)
    (a : Space n) (R : ℝ) (hR : 0 < R) (T : FamilyKind) (C : ℝ) (D : RetainedSets n)
    (hunH : ¬ (1 ≤ k ∧ k ≤ n) →
      D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.horizontalSupport (rescaledSource μ k a R hR) = ∅)
    (hunV : ¬ (2 ≤ k ∧ k ≤ n + 2) →
      D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.verticalSupport (rescaledSource μ k a R hR) = ∅)
    (honlyH : T = .horizontal →
      D.verticalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.verticalSupport (rescaledSource μ k a R hR) = ∅)
    (honlyV : T = .vertical →
      D.horizontalMeasure (rescaledSource μ k a R hR) = 0 ∧
        D.horizontalSupport (rescaledSource μ k a R hR) = ∅)
    (hS : HasRegularSupportBounds k C (point 0 0) 1
      (D.horizontalSupport (rescaledSource μ k a R hR))
      (D.verticalSupport (rescaledSource μ k a R hR)))
    (hG : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      HasScaledGraphDomainCover k (D.horizontalSupport (rescaledSource μ k a R hR))
        (D.verticalSupport (rescaledSource μ k a R hR)) C ε δ 1) :
    IsLocalEnhancedDecomposition k T C a R μ
        (similarity a R hR ⁻¹' D.horizontal) (similarity a R hR ⁻¹' D.vertical) ∧
      μ.restrict (similarity a R hR ⁻¹' D.horizontal ∪ similarity a R hR ⁻¹' D.vertical)ᶜ
          (Metric.ball a R) =
        ENNReal.ofReal R ^ k *
          D.remainderMeasure (rescaledSource μ k a R hR) (Metric.ball (point 0 0) 1) := by
  exact ScalingTree.isLocalEnhancedDecomposition_of_rescaledSource_of_leaves hn hk hkn μ hμ hreg a R hR
    T C D hunH hunV honlyH honlyV hS hG

/-- **Markov tail bound for integrated gauge energies.**

For a source finite on compacts, any family `T`, a cylinder `P(a,R)`, a
nondecreasing Borel gauge `Φ : [0,∞] → [0,∞]` and a real `M` with `0 < Φ(M) < ∞`,
`μ(P(a,R) ∩ {S^{2R}_{μ,T} > M}) ≤ Λ_Φ / Φ(M)`, where
`Λ_Φ = ∫_{P(a,R)} Φ(S^{2R}_{μ,T}) dμ` (`gaugeEnergy`). On the exceptional set
`Φ(S) ≥ Φ(M)` by monotonicity; integrate and divide by the finite positive `Φ(M)`. The
power energy is the special case `Φ(x) = x^q`, `q > 0` (`powerEnergy` is definitionally
`gaugeEnergy (· ^ q)`); no convexity and no restriction `q ≥ 1` is used.

Used in `powerRateProperty_of_scaled` (with `Φ = (·)^q`, including the zero-energy
case by a countable union of thresholds) and `gaugeRateProperty_of_scaled`, where the
threshold `M` is chosen and the real arithmetic is done. -/
theorem measure_lt_squareEnergy_le_gaugeEnergy_div {n : ℕ} (k : ℕ) (μ : Measure (Space n))
    (hμ : IsFiniteMeasureOnCompacts μ) (T : FamilyKind) (a : Space n) (R : ℝ)
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Monotone Φ) (hΦm : Measurable Φ) (M : ℝ)
    (hpos : 0 < Φ (ENNReal.ofReal M)) (hfin : Φ (ENNReal.ofReal M) ≠ ⊤) :
    μ (Metric.ball a R ∩ {z | ENNReal.ofReal M < squareEnergy μ k T (2 * R) z}) ≤
      gaugeEnergy Φ μ k T a R / Φ (ENNReal.ofReal M) := by
  exact measure_lt_squareEnergy_le_gaugeEnergy_div_proof k μ hμ T a R Φ hΦ hΦm M hpos hfin

/-- **Upper density off a closed retained carrier.**

If `μ = μ⁺ + μ_g` and `μ_g` is carried by a closed set `K`
(`μ_g(Kᶜ) = 0`), then at every `z ∉ K` the upper densities agree:
`Θ^{k,*}(μ⁺,z) = Θ^{k,*}(μ,z)`. Sufficiently small balls around `z` miss `K`, so
`μ(P(z,r)) = μ⁺(P(z,r))` for small `r > 0`, and the `limsup` along `r ↓ 0` is unchanged.
Closedness of `K`, not merely a measurable carrier, is essential. No regularity of the
measures is needed.

The companion bound `H_P^k(F \ K) ≤ C_k a^{-1} μ⁺(U)` is
`density_hausdorff_levelSet_le`, which uses this lemma and applies
`UpperDensityDominationStatement` to the source `μ⁺`. -/
theorem upperDensity_eq_of_not_mem_closed_carrier {n : ℕ} (k : ℕ)
    (μ μp μg : Measure (Space n)) (K : Set (Space n)) (hK : IsClosed K)
    (hsum : μ = μp + μg) (hcarried : μg Kᶜ = 0) {z : Space n} (hz : z ∉ K) :
    upperDensity μp k z = upperDensity μ k z := by
  exact upperDensity_eq_of_not_mem_closed_carrier_proof k μ μp μg K hK hsum hcarried hz

end ParabolicRectifiability.Enhancements
